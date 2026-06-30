# EVM DIV/MOD Operand Workload — Empirical Distribution (Phase 2)

> **Purpose.** Replace the *reasoned-not-measured* divisor distribution from
> Phase 1 with **real mainnet data**, so the Phase 3 algorithm redesign optimizes
> a *frequency-weighted* objective instead of guessing which divisor classes
> matter. Machine-readable output: [`bench/div-weights.json`](../bench/div-weights.json).

## TL;DR — the four findings that reshape Phase 3

Across **145,888 division ops** from **32 distinct mainnet blocks**
(frequency-*weighted over this sample* — see Methodology and the stability caveat §1):

1. **DIV dominates.** Of all division-family ops, **91.7 % are DIV**, 3.3 % MOD,
   4.0 % SDIV, 1.0 % SMOD. Optimize DIV first; MOD shares its core.
2. **Most divisors are small.** For the unsigned DIV+MOD core, divisor
   word-count **n=1 (<2⁶⁴) is 49 %**, n=2 is 21 %. **Small divisors — the
   *most expensive* case in today's `evm_div` (inverted cost curve, Phase 1) —
   are also the *most common*.** Optimizing them is doubly justified.
3. **Over half of all divides are not really divides.** **54 % are "cheap"**
   (block-bootstrap 95 % CI **[48 %, 61 %]**): `a < b` → early-out (q=0, r=a)
   (**23 %**), or **divisor is a power of two** (**46 %**) → a shift, or `b == 0`
   (0.2 %). A correct early-out / shift dispatch removes the division for the
   majority of calls. **Caveat (important):** ~85 % of that pow2 class is
   `divisor = 2^(8k)` **byte/word-extraction** (dominated by `2^224` and `2^160`),
   *not* Q96/Q128 fixed-point — see §2.3. These are real executed `DIV` opcodes so
   a shift path genuinely helps, but the share is contract-vintage-sensitive
   (modern Solidity emits `SHR`).
4. **The benchmark's worst case is real but rare.** Yoichi's repricing benchmark
   targets *genuine* (non-pow2) divisors just over 2⁶⁴ and 2¹²⁸ — i.e. n=2 and
   n=3 schoolbook work. But **89 % of real n=3 divisors and 97 % of real n=4
   divisors are powers of two**, and 67 % of n=3 are also `a<b`. **Genuine
   non-cheap divides needing n≥3 are only 1.8 % (n=3 alone: 1.6 %); 96 % of all
   genuine divides are n≤2 (and 91 % of genuine *multi-word*, n≥2, divides are
   n=2).** The boundary worst-case the benchmark presumes "has no fast path" is a
   thin tail in practice.

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
transaction-by-transaction**, so within a block the operand stream is
**frequency-weighted**: a contract that executes many divisions contributes
proportionally many samples. DeFi math dominates naturally — no hand-picking.
This is *not* a uniform random sample of mainnet (see the stability caveat below);
read every number as "frequency-weighted over these 32 blocks."

- **Collector:** [`scripts/collect-div-operands.py`](../scripts/collect-div-operands.py)
- **Sample:** 32 distinct blocks, `25238313 .. 25431308` (~27 days, June 2026);
  **145,888 division ops**. The sample is the **union of two collection runs** plus
  a small probe: block spacing is mostly stride 7919, with an irregular tail and
  three block-pairs only 6 apart, so it is **not reproducible from a single
  `collect` command** — the exact 32-block list is recorded in
  `bench/div-weights.json` → `_meta.block_list`, and the committed raw data is the
  ground truth. (To reproduce *the analysis*, re-bucket the raw `.gz`; see §5.)
- **Raw data (committed, gzip):** [`bench/div-operands-mainnet.jsonl.gz`](../bench/div-operands-mainnet.jsonl.gz)
  — one JSON record per op `{blk, tx, op, a (dividend hex), b (divisor hex)}`.
  Exact-duplicate records occur (a loop dividing by the same constant); these are
  **legitimate under frequency-weighting** and are kept, not deduped.

### Tier 2 — execution-specs Python EVM instrumentation (offline, reproducible)
A monkeypatch hook that wraps the **real** spec opcode implementations
(`ethereum.forks.<fork>.vm.instructions.arithmetic.{div,sdiv,mod,smod}`) and
drives them with actual EVM bytecode through a minimal interpreter loop.

- **Script:** [`scripts/instrument-spec-div.py`](../scripts/instrument-spec-div.py)
- Operand semantics were confirmed **by reading the spec directly**: `div` pops
  the dividend first (stack top) then the divisor
  (`execution-specs/.../arithmetic.py:120-121`), so the tracer's `peek(0)` is the
  dividend `a` and `peek(1)` the divisor `b`. *Note:* the Tier-2 hook asserts this
  convention by construction (it pushes the dividend last); it does **not** by
  itself cross-check the tracer against a known quotient, so the spec reading is
  the actual evidence. The script's value is (a) a node-free reproducible path and
  (b) replaying the benchmark's adversarial operands (Tier 3).

### Tier 3 — repricing benchmark (adversarial; NOT a distribution)
The operands in
`execution-specs/tests/benchmark/compute/instruction/test_arithmetic.py`
are deliberately worst-case (divisors just over 2⁶⁴ / 2¹²⁸). Captured to
[`bench/div-operands-benchmark.jsonl`](../bench/div-operands-benchmark.jsonl) as
the point-set the benchmark assumes. **These are 6 hand-chosen pairs, not a
frequency distribution** — they bound the worst case, nothing more.

### Representativeness caveats (read before trusting any number)
- **Sample size / stability.** 32 blocks is thin. Per-block cheap% ranges
  **30 %–93 % (stdev 19 pp)**; the op-weighted 54 % differs from the
  block-unweighted mean (61 %), i.e. the headline is driven by *which* heavy DeFi
  contracts landed in the sample. A block-level bootstrap gives a **95 % CI of
  [48 %, 61 %]** on the 54 % cheap figure. Concentration: the single biggest block
  is 12.4 % of all ops, the top 10 of 32 blocks are ~51 %. The conclusion is
  robust to dropping the dominant block (54.1 → 54.6 %), but treat the 3-sig-fig
  numbers as point estimates with ~±6 pp error, not population constants.
- **Heavy-tx drop-out (bias direction UNPROVEN).** The free-tier node returns a
  server-side trace timeout (HTTP 408) on the heaviest ~3–8 % of transactions
  (148 logged failures across the runs) — typically the largest aggregator/MEV
  swaps. Those are **not sampled**, and their op-density and divisor mix are
  **unmeasured**. It is *plausible* they are pow2/`a<b`-heavy (more byte-slicing
  and zero-amount probes) rather than genuine Knuth-D work, so the missing tail
  could cut **either** way — do not assume this bias is conservative. Quantifying
  the dropped population (e.g. on a paid endpoint) is open work.
- **Temporal window.** ~27 days of mid-2026 mainnet. DeFi composition shifts over
  time; re-run the collector to refresh. The structural drivers (decimals, bps,
  fixed-point, byte-extraction) are durable but their *relative* mix is not.
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
**96 % of all genuine divides are n≤2** (equivalently, 91 % of genuine
*multi-word*, n≥2, divides are n=2; genuine n≥3 is 1.8 % of all divides).

### 2.3 Cheap-vs-genuine summary (DIV+MOD core)
This is a **non-overlapping partition of all divides** (precedence `a<b` > `pow2`
> genuine-by-n; it sums to 100 %). It is the canonical weighting for Phase 3 —
see `bench/div-weights.json` → `partition`. Note `a<b` and `pow2` *overlap* ~15 pp
(byte-extraction `x/2^(8k)` where the high bytes are zero is both); the partition
charges those to the `a<b` early-out, so the pow2 row here (31 %) is pow2-**and**-not-`a<b`.

| class | share | path |
|---|--:|---|
| `b == 0` | 0.2 % | return 0 |
| `a < b` early-out (q=0 / r=a) | 22.8 % | no divide |
| divisor power-of-two, `a≥b` → shift | 31.1 % | shift/mask |
| **CHEAP subtotal** | **54.1 %** | (CI [48 %, 61 %]) |
| genuine n=1 (single-word `DIVU`) | 26.0 % | divide |
| genuine n=2 (double-word) | 18.2 % | divide |
| genuine n=3 (Knuth-D tail) | 1.6 % | divide |
| genuine n=4 (Knuth-D tail) | 0.2 % | divide |

(For reference, the *overlapping* totals — count every `a<b` and every `pow2`
independently — are `a<b` 22.8 % and pow2 46.0 %; **do not add these**, they
double-count the ~15 pp intersection.)

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
drivers: **decimals (10⁶/10¹⁸/ray), basis points, and fixed-point (Q96/Q128).**

### 2.4b What the power-of-two class actually is (don't mistake it for fixed-point)
The 46 % pow2 class is **not** mostly Q96/Q128 fixed-point. Breaking it down:

| pow2 sub-class | share of pow2 | share of all divides |
|---|--:|--:|
| `2^(8k)` byte/word-extraction (e.g. `2^224`, `2^160`) | **84.8 %** | **39.0 %** |
| &nbsp;&nbsp;↳ `2^224` (extract top 4 bytes) | 22.7 % | 10.4 % |
| &nbsp;&nbsp;↳ `2^160` (extract an address) | 21.5 % | 9.9 % |
| `2^128` (Q128) + `2^96` (Q96) fixed-point | ~3.4 % | ~1.6 % |
| `1`, `2`, other small/odd exponents | remainder | — |

So the dominant pow2 use is **slicing words into bytes/addresses**, an idiom
modern Solidity compiles to `SHR` — these reach `evm_div` as real `DIV` opcodes
(often in older or hand-written bytecode), so a shift path *does* help them, but
their prevalence is **contract-vintage-sensitive** and could shrink over time.
Treat "46 % pow2 → free shift" as an upper bound on a workload-dependent win, not
a structural constant. (`pow2_byte_aligned_frac` in the weights JSON tracks this.)

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
| pow2 divisor | (not exercised) | **46 %** biggest class (but 85 % is `2^(8k)` byte-extraction — §2.4b) |
| `a<b` early-out | (not exercised) | **23 %** |

The benchmark is a fair *worst-case lower bound* for a 1-and-2-word-optimized
algorithm, but it is **not** where the real cost lives. Building the n=2 path it
demands is justified (18 % genuine); chasing the n=3 boundary beyond
correctness is optimizing a 1.6 % tail. The unexercised pow2 (46 %, mostly
byte-extraction shifts) and `a<b` (23 %) classes are where the
dynamic-instruction budget actually goes — modulo the heavy-tx drop-out caveat (§1).

---

## 4. Recommended frequency weights for Phase 3

Use [`bench/div-weights.json`](../bench/div-weights.json) (`divmod` block) as the
canonical weights for the `bench/DivBench.lean` cost objective. The single number
to minimize is **frequency-weighted dynamic instruction count**:

```
cost = Σ_class  weight[class] · steps(candidate_algorithm, class)
```

Dispatch classes and weights — the **non-overlapping partition** (DIV+MOD core;
rounded, exact values in the JSON `divmod.partition`). **These sum to 1.000** —
weight against *this* table, not the overlapping `a_lt_b_frac`/`pow2_frac`:

| class | weight | Phase-3 path |
|---|--:|---|
| `b == 0` | 0.002 | return 0 |
| `a < b` (precedence first) | 0.228 | return q=0, r=a (early-out) |
| `pow2(b)`, `a≥b` (and not `a<b`) | 0.311 | shift: `q = a >> log2(b)`, `r = a & (b−1)` |
| genuine n=1 | 0.260 | register-resident single-word (≤ a few `DIVU`) |
| genuine n=2 | 0.182 | double-word specialized path |
| genuine n=3 | 0.016 | existing Knuth-D tail (correctness, not speed) |
| genuine n=4 | 0.002 | existing Knuth-D tail |
| **sum** | **1.000** | |

> ⚠️ **Do not** build a weight row from `a_lt_b_frac` (0.228) **plus** `pow2_frac`
> (0.460): they overlap by ~0.15 (≈15 pp of divides are both `a<b` and pow2 —
> byte-extraction with zero high bytes) and would sum past 1. The partition above
> charges the intersection to the `a<b` early-out. Use `divmod.partition` +
> `divmod.cheap_frac` from the JSON; never sum the overlapping fractions.

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

**To reproduce the committed analysis/weights exactly**, re-bucket the committed
raw data (this regenerates `bench/div-weights.json` byte-for-byte except its
hand-written `_meta` block):
```bash
zcat bench/div-operands-mainnet.jsonl.gz | \
    python3 scripts/analyze-div-operands.py /dev/stdin \
    --label mainnet-32blocks-2026-06 --weights bench/div-weights.json
```

**To collect a fresh sample** (the original 32-block set is a union of runs and
not reproducible from one command — see §1; the exact block list is in
`bench/div-weights.json` → `_meta.block_list`):
```bash
# needs a debug_traceTransaction-capable endpoint (drpc.org free tier works):
python3 scripts/collect-div-operands.py --count 25 --stride 7919 --workers 3 \
    -o fresh.jsonl
python3 scripts/analyze-div-operands.py fresh.jsonl --label fresh --weights fresh-weights.json

# Tier 2/3 — offline spec-EVM instrumentation (adversarial operands):
execution-specs/.venv/bin/python scripts/instrument-spec-div.py --fork prague \
    -o bench/div-operands-benchmark.jsonl
```

Endpoint note: opcode-level full-block tracing exceeds free-tier limits; the
collector traces one tx per request and parallelizes with `--workers 3` (higher
concurrency triggers rate-limiting). It fail-fasts and circuit-breaks per block
so a throttled/heavy block is skipped rather than stalling the run.
