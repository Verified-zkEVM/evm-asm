# DIV Algorithm Redesign Under Real Mainnet Weights (Phase 3)

This document records the **measured** performance of the DIV/MOD opcode
candidates under the empirical mainnet operand distribution from Phase 2, and the
resulting algorithm-redesign roadmap. It feeds the gas-repricing discussion
(@pirapira): DIV is flat `LOW` = 5 gas, but its real zkVM proving cost (≈ dynamic
instruction count, Gassmann et al. arXiv:2508.17518v2) varies with divisor size,
and the current implementation has an **inverted** cost curve — the common
small-divisor case is the *most* expensive.

## Method

`bench/DivBench.lean` runs the **verified** `step` semantics
(`EvmAsm/Rv64/Execution.lean`) on concrete operands, counting dynamic
instructions (the primary cost driver). Phase 3 added two things:

1. **PRIMARY metric — operand-sampled mean.** The true mean step count over a
   **frequency-weighted sample of real mainnet `(a,b)` pairs**
   (`bench/div-operands-sample.txt`, drawn from the Phase-2 trace by
   `scripts/sample-div-operands.py`: 800 DIV + 400 MOD ops, stride-sampled so the
   distribution is preserved). This has **no representative-bias** — it captures
   the variation *within* a divisor word-count (normalization shift, dividend
   size, a<b/pow2 sub-cases) that a single representative cannot.
2. **CROSS-CHECK metric — representative point estimate.** Σₙ (divisor-word-count
   fraction `nₖ`) · steps(repₙ), plus a partition-weighted variant, using one
   operand per class. This is **not exact** (step count varies within a fixed `n`
   — e.g. `evm_div_v5` n=2 spans ~528–634, `evm_div_v6` n=1 ~347–369 — and the
   chosen reps skew to the expensive end), so it is kept only to sanity-check the
   sampled mean and to give the per-class breakdown the (not-yet-built)
   cheap-dispatch candidate will be ranked against.

Reproduce:

```
lake build EvmAsm.Evm64.DivMod.FastN1Program EvmAsm.Evm64.DivMod.Program \
           EvmAsm.Rv64.Execution EvmAsm.Evm64.Basic
python3 scripts/sample-div-operands.py     # regenerate the sample (once)
lake env lean bench/DivBench.lean          # ~3 min (runs ~3200 real-operand executions)
```

## Candidates measured

| candidate | what it is |
|---|---|
| `evm_div` / `evm_mod` (v4) | deployed, Knuth-D, `div128_v4` |
| `evm_div_v5` | Knuth-D, `div128_v5` (v6's n≥2 fallback) |
| `evm_div_v6` / `evm_mod_v6` | v5 core + an n=1 single-limb fast path (issue #9303) |

## Headline: operand-sampled mean steps (real mainnet operands)

| | deployed (v4) | v5 | **v6 (fast path)** | v6 vs deployed |
|---|--:|--:|--:|--:|
| **DIV** (800 real ops) | 551.53 | 557.60 | **399.08** | **−27.6%** |
| **MOD** (400 real ops) | 609.48 | — | **406.52** | **−33.3%** |

> **`evm_div_v6` cuts the real-workload DIV instruction count 27.6%, and
> `evm_mod_v6` cuts MOD 33.3%** (MOD gains more because n=1 is 68% of MOD
> operands vs 49% of DIV). Both are correct on **every** sampled operand
> (800/800 DIV, 400/400 MOD) *and* on the 112-operand synthetic corner sweep.
> Note `evm_div_v5` is a **−1.08% regression vs v4** (557.6 vs 551.5) — it exists
> only as v6's fallback core, not as a standalone improvement.

The win comes entirely from collapsing the dominant n=1 bucket; per-class step
counts (the representative cross-check) show why:

| class | `evm_div`(v4) | `evm_div_v5` | `evm_div_v6` |
|---|--:|--:|--:|
| n=0 (b=0)        | 13  | 13  | 21  |
| **n=1**          | **685** | **693** | **365** |
| n=2              | 628 | 634 | 640 |
| n=3              | 449 | 453 | 459 |
| n=4              | 204 | 206 | 212 |

The **inverted curve** is confirmed: under v5, n=1 (693) is 3.4× the n=4 cost
(206). v6 inverts the inversion for the dominant bucket (n=1 → 365) while adding
only ~6 steps to the n≥2 fallback (the dispatch prologue) and ~8 to the b=0 path
(both negligibly weighted). **Caveat on the per-class numbers:** these are single
representatives; the true cost varies within each `n` (v5 n=2 spans ~528–634
depending on normalization shift and dividend), which is exactly why the
*sampled mean* above — not this table — is the headline. The representative
n-weighted point estimate (566.6 → 414.2, −26.9%) sits ~15 steps above the true
sampled mean and slightly understates the win.

## Workload weights (from `bench/div-weights.json`, `divmod` block)

All percentages below are the DIV+MOD (`divmod`) distribution that the sampling
draws from. (The DIV-only `div` block differs by <1pp and changes the headline
by <0.4pp, so the choice is immaterial.)

- divisor word-count: n0 0.2%, **n1 49.3%**, n2 21.4%, n3 14.5%, n4 14.7%.
- non-overlapping `partition` (sums to 1.0): b0 0.2%, a<b 22.8%,
  **pow2¬a<b 31.0%**, genuine_n1 26.0%, **genuine_n2 18.2%**, genuine_n3 1.6%,
  genuine_n4 0.2%. **Weight against `partition`; do NOT add a_lt_b+pow2 (they
  overlap ~15pp).** Cheap classes (b0+a<b+pow2) = **54.1%** (file's `cheap_frac`;
  block-bootstrap 95% CI [48%, 61%]).
- conditionals: a<b is ~67% n=3 (`altb_by_n[3]=0.666`); pow2 is ~97% of n=4
  (`pow2_by_n[4]=0.967`) and ~89% of n=3 (`0.888`). MOD: n=1 is **68%**.

## What this means for the redesign

1. **Verify `evm_div_v6` / `evm_mod_v6` first.** They already exist, are
   executable, are correct across the full sample (1200 real ops) and the corner
   sweep, and capture the biggest measured win (−27.6% DIV, −33.3% MOD). The
   verification work (dispatch `cpsBranchWithin` + fast-path body triple + arm
   merge) is scoped in `PLAN.md` (n=1 fast path entry).

2. **The cheap-dispatch front-end is the next prize — but read the inverted
   curve carefully.** The cheap classes are **54.1%** of divides, but they are
   *dominated by high-`n` divisors* (a<b ~67% n=3; pow2 ~97% of n=4 / ~89% of
   n=3, the 2^(8k) byte-extraction idiom). Because of the inverted curve, those
   high-`n` cheap calls are **already among the cheapest** today (n=3 ≈ 459,
   n=4 ≈ 212). So the cheap-dispatch win is real but smaller than the raw "54% of
   calls" suggests. A front-end that takes the cheap classes to ~tens of steps
   (b=0→0 / a<b→(0,a) / pow2→shift+mask) is estimated to reach **roughly −50% off
   the measured v6 mean** (the representative partition-weighted estimate is
   ~236 steps, ~−58% off deployed) — but this is an *estimate*; it will be
   **measured** with `bench/DivBench.lean` once the candidate exists (the harness
   already computes the sampled mean for any new `Program`).

   ⚠️ Caveats carried from Phase 2: the pow2 win is contract-vintage-sensitive
   (85% is byte-extraction; modern Solidity emits `SHR`, not `DIV` by 2^k), and
   the 54%-cheap figure has a 95% CI of [48%, 61%] with an unproven bias from
   dropped heavy-tx traces. The **genuine n=1 / n=2** buckets (26.0% / 18.2%,
   vintage-independent) are the most defensible targets; v6 already owns n=1,
   leaving the **n=2 double-word path** as the most robust un-captured win.

3. **n=2 double-word specialized path (18.2% genuine, the most defensible
   un-captured win).** ~640 steps under v6. A 2-limb divide-heavy / reciprocal
   method (no Knuth normalization) is the third priority.

4. **Keep Knuth-D as the n≥3 tail** (1.8% of all divides). Correctness only.

## Recommended ordering

1. Verify `evm_div_v6` / `evm_mod_v6` (n=1 fast path) — captures the measured
   −27.6% DIV / −33.3% MOD.
2. Build + verify the cheap-dispatch front-end (a<b / pow2 / b0) — estimated
   ~−50% off v6; **measure** it with the sampled-mean harness; mind the vintage
   caveat.
3. Build + verify the n=2 double-word path — the most defensible remaining
   genuine win (18.2%).
4. Leave n≥3 on Knuth-D.
