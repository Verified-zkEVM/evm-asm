# DIV Algorithm Redesign Under Real Mainnet Weights (Phase 3)

This document records the **measured** performance of the DIV opcode candidates
under the empirical mainnet operand distribution from Phase 2, and the resulting
algorithm-redesign roadmap. It feeds the gas-repricing discussion (@pirapira):
DIV is flat `LOW` = 5 gas, but its real zkVM proving cost (≈ dynamic instruction
count, Gassmann et al. arXiv:2508.17518v2) varies with divisor size, and the
current implementation has an **inverted** cost curve — the common small-divisor
case is the *most* expensive.

## Method

`bench/DivBench.lean` runs the **verified** `step` semantics
(`EvmAsm/Rv64/Execution.lean`) on concrete operands, counting dynamic
instructions (the primary cost driver) plus the memory axis. Phase 3 extended it
to consume `bench/div-weights.json` (138,601 unsigned DIV+MOD ops over 32 mainnet
blocks, ~27 days June 2026) and emit a single frequency-weighted cost per
candidate. Reproduce:

```
lake build EvmAsm.Evm64.DivMod.FastN1Program EvmAsm.Evm64.DivMod.Program \
           EvmAsm.Rv64.Execution EvmAsm.Evm64.Basic
lake env lean bench/DivBench.lean
```

Two weighted metrics are reported:

- **n-weighted** = Σₙ (divisor-word-count fraction `nₖ`) · steps(repₙ). This is
  **exact** for any candidate whose cost depends only on divisor word-count `n`
  — both `evm_div_v5` and the `evm_div_v6` n=1 fast path dispatch on `n` alone —
  so it is the faithful before/after headline.
- **partition-weighted** = Σ_class (partition fraction) · steps(rep_class) over
  the non-overlapping `divmod.partition` {b0, a<b, pow2¬a<b, genuine n1..n4}.
  This is the metric a **cheap-dispatch front-end** (not yet built) is designed
  to minimize. For v5/v6 it is *not* faithful (they have no a<b/pow2 fast path,
  so the high-`n` representatives picked for those classes make it read low);
  treat it only as the scaffold for the cheap-dispatch candidate.

## Candidates measured

| candidate | what it is | n=1 path |
|---|---|---|
| `evm_div`    | deployed, Knuth-D, `div128_v4` | full loop |
| `evm_div_v5` | Knuth-D, `div128_v5` (v6's n≥2 fallback) | full loop |
| `evm_div_v6` | `evm_div_v5` + an n=1 single-limb fast path (issue #9303) | fast path |

## Per-class dynamic instruction count (steps)

| class | `evm_div`(v4) | `evm_div_v5` | `evm_div_v6` |
|---|--:|--:|--:|
| n=0 (b=0)        | 13  | 13  | 21  |
| **n=1**          | **685** | **693** | **365** |
| n=2              | 628 | 634 | 640 |
| n=3              | 449 | 453 | 459 |
| n=4              | 204 | 206 | 212 |
| a<b (rep n=3)    | 411 | 415 | 421 |
| pow2 (rep 2²²⁴)  | 269 | 271 | 277 |

All three candidates are correct on **112/112** swept operands (every dispatch
corner: b=0, b∈{1,2,256} single-limb pow2, b=7, a<b single-word, the n=2/3/4
boundary divisors). The **inverted curve** is confirmed: under v5, n=1 (693
steps) is 3.4× the n=4 cost (206). v6 inverts the inversion for the dominant
bucket — n=1 drops to 365 — while adding only ~6 steps to the n≥2 fallback (the
dispatch prologue) and ~8 to the b=0 path (both negligibly weighted).

## Headline: frequency-weighted cost (mainnet divmod)

| metric | `evm_div`(v4) | `evm_div_v5` | `evm_div_v6` |
|---|--:|--:|--:|
| **n-weighted avg steps** | **566.64** | 572.73 | **414.18** |
| partition-weighted avg steps | 476.96 | 481.73 | 400.91 |

> **`evm_div_v6` cuts the real-workload-weighted DIV instruction count by
> 26.9%** (566.6 → 414.2), entirely by collapsing the n=1 bucket — which is
> **49.3% of all divides** — from ~685 to 365 steps. This is the largest single
> lever already implemented and validated.

## What this means for the redesign

1. **Verify `evm_div_v6` first.** It already exists, is executable, and is
   correct across the full sweep, and it captures the biggest measured win
   (−27%). The verification work (dispatch `cpsBranchWithin` + fast-path body
   triple + arm merge) is scoped in `PLAN.md` (n=1 fast path entry). MOD shares
   the core (`evm_mod_v6`); n=1 is **68%** of MOD operands, so the same path
   helps MOD even more.

2. **The cheap-dispatch front-end is the next prize — but read the inverted
   curve carefully.** The cheap classes are **53.7%** of divides (a<b 22.8% +
   pow2¬a<b 30.7% + b0 0.2%), but they are *dominated by high-`n` divisors*
   (a<b is ~67% n=3; pow2 is ~99% of n=4 and ~89% of n=3, the 2^(8k)
   byte-extraction idiom). Because of the inverted curve, those high-`n` cheap
   calls are **already among the cheapest** today (n=3 ≈ 459, n=4 ≈ 212, the
   2²²⁴ pow2 rep ≈ 277). So the cheap-dispatch win is real but smaller than the
   raw "54% of calls" suggests. Estimated ceiling, layered on v6 (every cheap
   class → ~30 steps via b=0→0 / a<b→(0,a) / pow2→shift+mask):

   | class | weight | v6 steps | cheap steps | weighted saving |
   |---|--:|--:|--:|--:|
   | a<b           | 0.228 | ~421 | ~30 | 89.1 |
   | pow2¬a<b      | 0.307 | ~277 | ~30 | 75.8 |
   | b0            | 0.002 | 21   | ~10 | 0.0 |

   → partition-weighted ≈ 400.9 − 165 ≈ **236 steps**, i.e. another ~41% off v6
   and **~58% off the deployed `evm_div`**. Worth building, *after* v6 lands.

   ⚠️ Caveats carried from Phase 2: the pow2 win is contract-vintage-sensitive
   (85% is byte-extraction; modern Solidity emits `SHR`, not `DIV` by 2^k), and
   the 54%-cheap figure has a block-bootstrap 95% CI of [48%, 61%] with an
   unproven bias from dropped heavy-tx traces. The **genuine n=1 / n=2**
   buckets (0.262 / 0.181, vintage-independent) are the most defensible targets;
   v6 already owns n=1, leaving the **n=2 double-word path** as the most robust
   un-captured win.

3. **n=2 double-word specialized path (18.1% genuine, the most defensible
   un-captured win).** Currently 640 steps under v6. A 2-limb divide-heavy or
   reciprocal method (no Knuth normalization) is the third priority.

4. **Keep Knuth-D as the n≥3 tail** (1.8% of all divides). Correctness only.

## Recommended ordering

1. Verify `evm_div_v6` (n=1 fast path) — captures the measured −27%.
2. Build + verify the cheap-dispatch front-end (a<b / pow2 / b0) — ceiling
   ~−58% vs deployed; mind the vintage caveat.
3. Build + verify the n=2 double-word path — the most defensible remaining
   genuine win (18%).
4. Leave n≥3 on Knuth-D.
