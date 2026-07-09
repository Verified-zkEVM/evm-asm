# DIV-Perf Phase 4 Bootstrap — Verify the Winner, Build the Next Candidates

> **What this file is.** A self-contained kickoff for Phase 4 of the DIV opcode
> performance effort. Open a *fresh* session, read **only** this file, and you
> have everything needed to continue without re-deriving context.
>
> **Per-phase workflow.** Each phase gets (1) its own branch off the relevant
> base, (2) its own clean session, (3) a bootstrap file like this.
> **This phase continues on `perf/div-algorithm-redesign`** (the Phase 3 branch),
> which already carries the Phase 2 weights/data, the Phase 1 harness, and the
> Phase 3 measurement. Start with
> `git fetch origin && git checkout perf/div-algorithm-redesign`.
> **Bootstrap files are LOCAL / UNCOMMITTED.** Deliverables (proofs, new
> `Program`s, updated docs) commit as normal; push is gated by a Lean guardrail
> — hand the push command to the user to run manually.
>
> **Your last task this session is to generate the Phase 5 bootstrap** if work
> spills past one session: `docs/agents/div-perf-phase5-*.md`, local.

---

## 0. The big picture (settled — DO NOT re-litigate)

We optimize the verified 256-bit EVM **DIV** opcode (`evm_div` in
`EvmAsm/Evm64/DivMod/Program.lean`), a RISC-V macro-assembly subroutine verified
against `EvmWord.div`. Motivation: a gas-repricing question from @pirapira —
DIV is flat `LOW`=5 gas, but real zkVM proving cost ≈ **dynamic instruction
count** (Gassmann et al. arXiv:2508.17518v2; near-linear, Pearson > 0.9;
per-instruction cost ~uniform, "division is not expensive"; branches cheap but
speculation wasteful → compute exactly ONE path per input).

**Phases 1–3 are DONE.** Phase 1: the two-axis harness `bench/DivBench.lean`.
Phase 2: real mainnet operand distribution (`bench/div-weights.json`,
`docs/divmod-evm-workload.md`; 138,601 unsigned division ops, 32 blocks).
Phase 3: extended the harness to a **frequency-weighted** cost and **ranked the
existing candidates** — full writeup in `docs/divmod-evm-redesign.md`.

### The Phase 3 result that drives Phase 4 (measured, on this branch)

Operand-sampled mean step count over a frequency-weighted sample of REAL mainnet
operands (no representative-bias):

| | deployed (v4) | v5 | **v6 (fast path)** | v6 vs deployed |
|---|--:|--:|--:|--:|
| **DIV** (800 real ops) | 551.53 | 557.60 | **399.08** | **−27.6%** |
| **MOD** (400 real ops) | 609.48 | — | **406.52** | **−33.3%** |

`evm_div_v6` / `evm_mod_v6` (the n=1 single-limb fast path,
`EvmAsm/Evm64/DivMod/FastN1Program.lean`, issue #9303) are the **ranked winners**,
correct on all 1200 sampled ops + the 112-operand corner sweep. (`evm_div_v5` is
a −1.08% regression vs v4 — fallback core only.) Full writeup +
methodology in `docs/divmod-evm-redesign.md`. Reproduce:

```
lake build EvmAsm.Evm64.DivMod.FastN1Program EvmAsm.Evm64.DivMod.Program \
           EvmAsm.Rv64.Execution EvmAsm.Evm64.Basic
python3 scripts/sample-div-operands.py     # regenerate bench/div-operands-sample.txt
lake env lean bench/DivBench.lean          # ~3 min
```

### Workload weights you will need (`bench/div-weights.json` → `divmod`)

- n-distribution: n0 0.2%, **n1 49.3%**, n2 21.4%, n3 14.5%, n4 14.7%.
- non-overlapping `partition` (sums to 1.0, `divmod` block): b0 0.2%, a<b 22.8%,
  pow2¬a<b 31.0%, genuine_n1 26.0%, **genuine_n2 18.2%**, genuine_n3 1.6%,
  genuine_n4 0.2%. **Weight against `partition`; do NOT add a_lt_b+pow2 (they
  overlap ~15pp).** MOD: n=1 is 68% (the n=1 fast path helps MOD even more — measured −33.3%).

---

## 1. Phase 4 goal — in priority order

### Task A (PRIMARY): verify `evm_div_v6` / `evm_mod_v6`
The winner already exists and is executable + harness-correct; it just needs a
stack-level proof so the −27.6% DIV / −33.3% MOD win becomes verified. This is the single
highest-value action.

- **The blocker to clear first** (from PLAN.md, n=1 fast path entry): the proven
  `evm_div_stack_spec` is over `divCode` (v1 `divK_div128` block), while the
  executables use v4/v5 `div128` and `divCode_v5` is unused by any spec — a
  v1→v4→v5 migration artifact. **Pin one consistent (spec, executable,
  code-bundle) triple before composing.**
- **Then** (the structure): dispatch `cpsBranchWithin` (the `divK_dispatchN1`
  prologue: n≥2 / b=0 / n=1 routing) + fast-path body `cpsTripleWithin`
  (micro-decomposed under the WHNF atom ceiling) + reuse the n1 exactness math
  (`fullDivN1R*` in `EvmAsm/Evm64/DivMod/Spec/`) + merge arms on
  `divStackDispatchPost`.
- **Verification leverage:** `bv_udiv_umod_unique` (`EvmWordArith/Div.lean`)
  reduces any path to "exhibit `(q,r)` with `a = b·q + r ∧ r < b`". Each path =
  one sub-domain theorem + one dispatch-exhaustiveness proof; the existing
  Knuth-D paths stay as the n≥3 tail unchanged.
- **NO `native_decide`/`bv_decide`** (CI-forbidden; `scripts/check-forbidden-tactics.sh`
  + `scripts/check-axioms.sh` enforce the 3-classical-axiom trust base). Use
  `decide` (kernel `Nat` is GMP-backed), `omega`/`bv_omega`, `simp`/`ext`.
- Consider the `lean4:*` agents/skills (`lean4:autoprove`, `lean4:prove`,
  proof-repair) for the heavy proof lifting.

### Task B: build + verify the cheap-dispatch front-end (b=0 / a<b / pow2)
The next prize. *Estimated* ceiling (rep-based, NOT yet measured): ~−50% off the
measured v6 mean / ~−58% off deployed — **measure it with the operand-sampled
harness once the candidate exists** (`docs/divmod-evm-redesign.md` §2). Dispatch
(compute exactly one path):
- `b==0 → (q=0,r=0)`; `a<b → (q=0,r=a)` (256-bit high-to-low limb compare);
- `pow2(b) → q = a >> ctz(b), r = a & (b−1)` — detect via `b & (b−1) == 0 ∧ b≠0`;
  `ctz` via RISC-V `CTZ`/`CLZ` if modeled, else an unrolled bit scan; the shift
  is the existing SHR logic (reuse, don't re-derive).
- **Proof:** for pow2, `a >> k` and `a & (2^k−1)` give `(q,r)` with
  `a = 2^k·q + r ∧ r < 2^k` directly → `bv_udiv_umod_unique`, bitvector
  identities via `BitVec.eq_of_getLsbD_eq`/`getLsbD_ushiftRight`.
- ⚠️ **Caveats (mind before over-investing):** 85% of pow2 is `2^(8k)`
  byte-extraction (vintage-sensitive; modern Solidity emits `SHR`), and the
  cheap classes are dominated by **high-`n`** divisors that the inverted curve
  already makes cheap (n=3≈459, n=4≈212), so the marginal win is smaller than
  "54% of calls" suggests. The vintage-independent buckets (genuine n1/n2) are
  the most defensible.
- **Implementation note:** the hard part is hand-computing branch offsets for a
  new dispatch prologue (cf. the magic offsets `796 788 …` in
  `divK_dispatchN1`). Prototype as an *unverified* `Program`, validate
  correctness + measure cost with `bench/DivBench.lean` (the harness's
  correctness sweep catches mis-wired offsets), *then* verify.

### Task C: build + verify the n=2 double-word path (genuine_n2, 18.2%)
The **most defensible un-captured win** (vintage-independent, unlike pow2). ~640
steps under v6 today. A specialized 2-limb divide-heavy / reciprocal method (no
Knuth normalization). Evaluate divide-heavy vs schoolbook with the harness.

### Task D: leave Knuth-D as the n≥3 tail (1.8% of all divides). Correctness only.

---

## 2. How to extend the harness for a new candidate
`bench/DivBench.lean` (this branch) already: parametrizes `benchDiv`/`benchMod`
by `exitPC`, computes the **operand-sampled mean** (the headline; over
`bench/div-operands-sample.txt`) plus a representative cross-check, and runs a
112-operand correctness sweep. To add a candidate:
1. Add `{ name, prog, exitPC }` to `candidates` (DIV) or `modCandidates` (MOD).
   **`exitPC` = byte offset of the program's terminal NOP** (1068 for v4/v5-shaped
   DIV/MOD; 1884 for `evm_div_v6`; 1912 for `evm_mod_v6`; compute for a new shape
   from its instruction layout — a wrong `exitPC` shows as WRONG/non-`✓` in the
   sweep or a timeout).
2. Re-run `lake env lean bench/DivBench.lean`. **The operand-sampled mean is the
   faithful headline for ANY candidate** (it captures within-class variation);
   the representative point estimate is only a cross-check. For a cheap-dispatch
   candidate, the sampled mean already routes real a<b/pow2 operands through the
   new path, so no special weighting is needed.

## 3. Deliverables (Phase 4)
1. Verified `evm_div_v6`/`evm_mod_v6` (Task A) — the −27.6% DIV / −33.3% MOD becomes verified.
2. (stretch) Cheap-dispatch and/or n=2 `Program`(s) + proofs (Tasks B/C).
3. Updated `docs/divmod-evm-redesign.md` with verified-status + any new
   candidate numbers; before/after deltas vs the Phase-3 table above.
4. Phase 5 bootstrap (local) if work continues.

## 4. What NOT to do
- Don't re-derive the cost model or the workload data; both are settled (§0).
- Don't re-rank v4/v5/v6; v6 is the measured winner (§0).
- Don't over-invest in the n≥3 tail (1.8%) or the vintage-sensitive pow2 class
  before the defensible genuine n1 (v6) / n2 wins are verified.
- Don't use branchless select across candidate quotients (speculation is
  wasteful in the cost model) — dispatch to exactly one path.
- Don't add `native_decide`/`bv_decide` anywhere (CI-forbidden).
- Don't optimize MOD/SDIV/SMOD separately — make DIV's core reusable and wrap it.
