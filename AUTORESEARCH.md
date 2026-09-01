# A roadmap for auto-research cycles that optimise evm-asm

**Status:** draft for circulation. Numbers below are measured against this
checkout unless attributed to the benchmark gist. Open questions are marked
**Q**.

---

## 0. TL;DR

Three findings reshape the first draft of this roadmap:

1. **Opcodes are 4.0% of proving cost.** Precompiles are 57.3%, and evm-asm's
   precompile cost (~538 B units) is roughly **430× reth's** (~1.25 B) — that
   single term alone is ~36× reth's *entire* cost. Optimising ALU opcodes is
   the right way to *build* the loop; it is not where the win is.
2. **The rebuild problem is module granularity, not proofs.** An MCOPY assembly
   edit moves 14 of 1440 constants in one generated file and invalidates **992
   modules**; the set that actually consumes those 14 symbols closes at **94**.
   That is **~31× amplification**, and two of the three fixes are mechanical
   edits to *generated* files.
3. **The inner search loop does not need the rebuild fix.** Scoring one
   candidate routine with `ziskemu -X` on a standalone ELF takes **0.74 s
   measured**, with no guest relink. Rebuild cost gates *landing* a change, not
   *searching* for one. Preliminaries and benchmarking can run in parallel.

Almost every measurement component already exists in the tree and is
disconnected from every other one. The work in Phase 0 is integration, not
invention.

---

## 1. Preliminaries: why an opcode edit is expensive

### 1.1 The mechanism (this is the "jump destination shift" question, answered)

The guest image is one flat, ordered string concatenation
(`EvmAsm/Codegen/Programs/Registry.lean:1342`, `statelessGuestUnit`). Section
bases are pinned by linker flags in `EvmAsm/Codegen/Driver.lean:71-98`, so a
`.text` size change does **not** shift `.data`/`.bss`. Only `.text` symbols
*after* the edit move.

Those addresses land in one generated file:

- `EvmAsm/Codegen/GuestAddrs.lean` — 1468 lines, **1440 `def <sym> : Nat`**,
  under `@[expose] public section`. Its own header calls it "the SINGLE file
  that churns on guest layout drift."
- **297 modules import it directly; its transitive reverse cone is 992 modules
  / ~997 MB of oleans**, of which **917 are not module-system-migrated** (so
  they fully re-elaborate rather than re-export).
- It is the **#1 file by commit-touch count** over the last 90 days (944
  touches; `scripts/churn-report.sh`).

So the cost is not that proofs break — it is that one module carries 1440
independent facts, and Lean's incremental unit is the module.

**Measured blast radius**, from the live `scripts/asm-fixtures/symbol-addresses.tsv`:

| Handler | `.text` symbols after it | …with a `GuestAddrs` pin |
|---|---|---|
| `h_ADD` | 132 (88 are other `h_*`) | **15** |
| `h_MCOPY` | 67 | **14** |
| `h_STOP` | 45 | **14** |

### 1.2 What PR #11492 did, and how far it got

#11492 (`dc159a84c`, merged in `828297981`) is one step of GH **#10753**:
parameterise a program over an abstract `GuestLayout` record so the leaf imports
the layout's *type*, and only one module binds the concrete `GuestAddrs` values.
Three-module shape: abstract leaf `<Name>Prog.lean` → `GuestLayout` →
`GuestLayoutInstance` → bridge `<Name>.lean`.

It is the right seam. It has **stalled at ~3%**:

| | now |
|---|---|
| abstract `Programs/*Prog.lean` leaves | **10** of 1013 |
| `GuestLayout` fields | **26** of 1440 |
| modules importing `GuestAddrs` directly | **297** |
| modules importing `GuestLayoutInstance` | **9** |

Two things to know before anyone restarts it. The design is **already written**
(`docs/agents/guestaddrs-layout-design.md`, issue #12068, closed) and specifies
*grouped* records — a single mega-flat `GuestLayout` **fails elaboration** past
~1125 fields, which the 24-field pilot already demonstrated. And the
indirection helps *leaves*, not hubs: `GuestLayoutInstance`'s own reverse cone
is already 778 modules because the bridges are consumed by hubs. **Q:** is
finishing #10753 worth its (large, one-time) migration cost relative to §1.3?

### 1.3 Three cheaper levers, ranked

**(a) Reorder `.text` so opcode handlers are last.** The 88 `h_*` handlers sit
contiguously at `0x80040a74`–`0x800527a0`, emitted at
`Registry.lean:1370` — and are followed by ~14 tail routines (`derive_*_requests`,
`stage_system_call*`, `parse_deposit_requests`, `extract_deposit_data`,
`materialize_log_records`, `assemble_execution_requests`, `requests_hash_verify`)
before the halt label. Moving the dispatcher block to immediately precede
`.Lstateless_guest_halt_after_runtime_dispatcher` takes `h_MCOPY`'s
pinned-symbol shift from **14 → 0**.

Residual: the 88 handlers still shift *each other*. Per-handler slot padding
(`.balign` or pad-to-budget) makes them mutually independent, at the cost of
image size. **Q:** do we have `.text` headroom (`RegionMap.textSizeBytes`) to
spend on that, and is opcode-vs-opcode independence worth it?

**(b) Split `GuestAddrs.lean` per cluster.** 1440 independent facts in one
module. The split lives in one function of `scripts/asm_to_program.py
guest-addrs` (e.g. `GuestAddrs/Text/<Cluster>.lean`, `GuestAddrs/Data.lean`,
`GuestAddrs/Bss.lean`), with `GuestAddrs.lean` retained as a re-exporting
umbrella so no consumer changes. Expected: 992-module cone → ~94.

**(c) Migrate the `EvmAsm.Rv64.SAsm.*` cluster to the module system.** 13 files
(`Ast`, `Flatten`, `Vc`, `Fn`, `StmtSound`, `StmtSoundCall`, `Handle`,
`RegionSound`, `BlockSound`, `GlobalData`, `CtrlSpecs`, `Tactic`, `RaSpill`),
each gating ~1000 modules. A `module` file cannot import a non-`module` one, so
these are the downward-closed blocker for 917 of the 992 modules in the
GuestAddrs cone.

**Also:** `guestImageEntries_extentsOk`
(`EvmAsm/Codegen/Proofs/GuestImage.lean:94`) is a single kernel `decide` over a
476-entry list at `maxRecDepth 8000`, re-run on every address move. It is the
documented merge deadlock in `docs/regenerating-generated-files.md`.

### 1.4 Measuring it

`scripts/import-graph-metrics.py` already computes exactly "I edited one thing;
how much re-elaborates", is sub-second, needs no build, and is ratcheted in CI
against `scripts/import-metrics-baseline.json`. Current baseline: 3027 modules,
14838 edges, depth 57, `sum_cone` 342656, `sum_private_cone` 66074.

**`EvmAsm.Codegen.GuestAddrs` is not currently an anchor.** Adding it (plus
`GuestLayout`, `Layout`, `Dispatch`, `Programs.Registry`, `Emit`) to
`scripts/import-metric-anchors.txt` is a one-line change that turns the cost
this section is about into a ratcheted CI number **before** we attack it.
(`scripts/olean-weights.json` should be refreshed with `--update-weights` first
— its provenance is a dev-branch commit.)

Acceptance for any of (a)–(c) is the paired-commit protocol already specified in
`docs/agents/guestaddrs-layout-design.md`: one generated-layout change, no
source change, three repeats, compare medians of wall clock **and** the
rebuilt-module list. Importer count is never the acceptance metric.

### 1.5 The part that is not a problem

**The inner loop does not relink the guest.** Scoring a candidate routine is
Tier A below, measured at 0.74 s. §1.1–§1.4 are about the cost of *landing* a
change, which matters for throughput of accepted candidates, not for search.

---

## 2. The benchmark and the cost function

### 2.1 What the reth comparison actually says

From the benchmark run (glamsterdam-devnet-7 block 115260, gas used 65,318,413,
witness 568,669 B, ziskemu v1.1.0-alpha):

| | EvmAsm | reth v0.1.0-rc.1 | ratio |
|---|---:|---:|---:|
| steps | 4.35 B | 124.6 M | **34.9×** |
| cost units | 938.6 B | 14.87 B | **63×** |
| wall | 142.3 s | 5.04 s | |

Category split:

| Category | EvmAsm | reth | EvmAsm abs | reth abs |
|---|---:|---:|---:|---:|
| Precompiles | 57.3% | 8.4% | **538 B** | 1.25 B |
| Main | 31.5% | 57.0% | 296 B | 8.47 B |
| Memory | 7.2% | 5.4% | 68 B | 0.80 B |
| Opcodes | 4.0% | 27.4% | 38 B | 4.07 B |
| Base | 0.0% | 1.9% | — | 0.28 B |

Two things fall out. `MAIN = 68 × steps` **exactly**, for both guests (and
confirmed locally on `gen-out/arith_mix.elf`) — so Main is a pure restatement of
step count. And **evm-asm's precompile term alone is ~36× reth's entire cost.**

### 2.2 The cost function

**Objective:** ZisK `TOTAL` cost units from `ziskemu -X` on a pinned workload,
always reported with its category split.

```
cost = BASE + MAIN + OPCODES + MEMORY + PRECOMPILES
     ≈ 293,601,280 + 68·steps + Σ_op w_op·n_op + w_mem·memops + Σ_p w_p·n_p
```

A steps-only objective — the first draft's "reducing max number of steps per
instruction" — is blind to the 57.3% that dominates. **Optimise cost units;
report steps alongside.**

**Report three numbers, not one:**

1. `cost_total` — the objective.
2. `steps` — the currency `stepsPerGas` is denominated in. One accelerator
   CSRRS is exactly one Lean `step` and one retired instruction, so Lean-step,
   spike `minstret`, and ziskemu step counts agree 1:1
   (`EvmAsm/Codegen/MemoryBudgetGuard.lean`, §Units).
3. `cost/gas` and `steps/gas` — the comparison unit against reth, and the same
   quantity `stepsPerGas := 128` claims to bound. `block_gas_limit` is already
   emitted per row by `scripts/eest-stateless-to-input.py:102`; it is simply
   never joined into the cycle record.

**Workload weighting.** `bench/div-weights.json` +
`bench/div-operands-mainnet.jsonl.gz` (138,601 real mainnet division ops across
32 blocks, with block-bootstrap CIs) is the template and the standard to hold
to: a *frequency-weighted* objective over real traffic, not a guessed
distribution. Generalise `scripts/collect-div-operands.py` from DIV/MOD to a
general opcode+operand histogram.

### 2.3 The three-tier evaluator

The loop's throughput is set by how fast one candidate can be scored, and the
tiers differ by ~5 orders of magnitude:

| Tier | Mechanism | Cost/eval | Gives |
|---|---|---|---|
| **A** | `ziskemu -X` on a standalone per-routine ELF | **0.74 s** (measured) | Exact ZisK cost + category + per-opcode breakdown, **no guest relink** |
| **A′** | `bench/DivBench.lean` — verified `step` semantics on a `Program` | ms | steps, loads/stores, distinct dwords, distinct 1 KiB pages; workload-weighted |
| **B** | `scripts/spike/spike_run` on the linked guest, real block | ~1 s/block | `minstret` steps, whole-guest |
| **C** | `ziskemu -X` on the linked guest, pinned block set | ~60 s/block | Authoritative cost + split |

Thousands of Tier A per hour, dozens of Tier B, a handful of Tier C.

### 2.4 What exists today, and what is missing

**Exists:**

- `bench/DivBench.lean` — runs the *verified* `step` semantics and reports steps
  + loads/stores + distinct dwords + distinct 1 KiB pages (the paging proxy;
  a page-in/out is ≈1130 cycles). Cost-model rationale cited from Gassmann et
  al., arXiv:2508.17518v2. **This is the right shape — it has just never been
  lifted above DIV/MOD.**
- `scripts/spike/spike_run` — the only real end-to-end step counter
  (`minstret`), ~50× faster than ziskemu (which re-transpiles a ~447 MB ROM
  each run), byte-parity gated.
- `scripts/cycles-append.sh` + `cycles-history` orphan branch — schema and
  persistence path.
- `EvmAsm/Progress.lean` `cycleBound` — per-opcode worst-case step bounds,
  kernel-bound to the witness theorem's own bound by
  `EvmAsm/Progress/CycleBounds.lean` (`pin_cycle_bound`), so the registry
  cannot drift from the proof.
- `EvmAsm/Codegen/MemoryBudgetGuard.lean` §7/§7b — a kernel-checked ledger of
  measured steps/gas ratios per mechanism.
- `scripts/codegen-eest-stateless-check.sh` — the block runner (EEST fixtures).

**Missing:**

1. **No aggregator.** Nothing sums, weights, or normalises `cycles-history.jsonl`.
2. **No gas normalisation** in the record, so `steps/gas` — the natural
   comparison unit — cannot be computed from the history.
3. **Essentially no data.** `cycles-history` holds **one** record.
4. **Not on any schedule.** `benchmark.yml` measures *Lean build time*, not
   guest cost.
5. **`cycles` is always null.** `--append-cycles` requires the spike backend;
   ziskemu emits no parsed step/cost marker, so the authoritative ZisK cost is
   never recorded.
6. **No pinned workload.** Selection is `--limit N` / `--random --seed N`, so
   two runs are not comparable; and only cleanly-halted rows are recorded, so a
   guest that fails more cases silently benchmarks on a smaller population.
7. **No attribution.** A step count is one opaque number. No keccak counter, no
   per-accelerator counter, no per-subsystem split.
8. **No reth baseline in-repo.** The 34.9×/63× figure lives only in a gist.

---

## 3. Hashes and precompiles: where the cost actually is

This was "TBD" in the first draft. What the code says:

- Precompiles are **ZisK accelerator syscalls** (`EvmAsm/Rv64/ZiskAccel.lean`:
  `0x800` Keccak-f[1600], `0x805` SHA-256, `0x802/0x80B` arith256/384-mod,
  secp256k1/BN254/BLS12-381 point add+double, `0x819` BLAKE2b round). The
  accelerators cover **leaf primitives only** — there is no inversion, no
  scalar-mul, no pairing, no P-256 entry. KECCAK256 is a guest *sponge wrapper*
  around the permutation, so its cost is (number of permutations) × unit cost.
- **There is no keccak result cache anywhere.** 244 `zkvm_keccak256` call sites
  across `EvmAsm/Codegen/Programs/`. The only cache in the tree,
  `mpt_resolve_cache` (4096-entry direct-mapped), caches *witness-node lookup*,
  not hashes, and is explicitly reset at **28** call sites.
- Upstream `execution-specs` **does** memoise; the port records that it does not
  (`EvmAsm/Stateless/SpecRef/WitnessReads.lean:25-33`,
  `IncrementalMpt.lean:52`).

So the "500× keccak calls because of no caching" observation is consistent with
the code — **but nobody has counted the calls.** Counting is ~20 lines of C++
(§4, Phase 0.1) and is the single highest-information change in this document.

**On the 512 MB RAM observation.** reth used ~2.6 GB emulated RAM; evm-asm used
none. reth *buys* its speed with memory. evm-asm's `.data` already spans
~427 MiB of the 512 MiB window with ~36 MiB free
(`docs/call-frame-memory-layout.md`), and the call-frame arena is already a
union region aliased over 244 MiB of execution-dead BAL scratch. So a hash cache
has to be paid for out of an aliased region — a real design constraint, not a
free win. **Q:** which region pays?

**On adversarial inputs.** Once a cache exists, "can an adversary defeat it?"
becomes a soundness question, and it has a home:
`MemoryBudgetGuard.lean` already records adversarial-*optimum* ratios (warmth
scan 114 steps/gas, MPT walk 16) distinct from structural ceilings.

**Already-measured hot paths** (from the same ledger, §7/§7b) — these are
optimisation targets that someone has already quantified:

| Mechanism | steps/gas | Note |
|---|---:|---|
| EIP-2929 warmth-table linear scan | **114** | the binding path; a hash table or sorted index is the obvious fix |
| MCOPY byte-at-a-time copy | **64** | |
| RIPEMD-160 software core | 24 | no accelerator; RV64 base has no rotate |
| MPT walk per cold access | 16 | |
| ECRECOVER | **≥512** | on *every* transaction, non-adversarial |
| Witness index | ≥2048 | |
| MODEXP (`modexp_binmod`, bit-serial) | ≥4096 | |
| Per-block prologue | **5,081,997 steps, gas-independent** | |

**Note the alignment with correctness work.** `stepsPerGas` has no value that is
simultaneously sound and provable today: 128 is false on ECRECOVER, and covering
the exceedances needs `k ≳ 2¹⁸`, which puts the top theorem's fuel past the
~1e9 prover working figure. **Fixing these hot paths is what makes a provable
`k` exist.** Performance work and obligation 12 of the top theorem are the same
work.

---

## 4. The plan

### Phase 0 — make the objective measurable and attributed (~1–2 weeks)

Nothing here changes guest behaviour. Every item is small and unblocks the rest.

| # | Item |
|---|---|
| 0.1 | **Per-accelerator invocation counters** in `scripts/spike/zisk_accel.cc`, printed next to `spike_run: halted cleanly steps=N` (`spike_run.cc:635`). Splits the 57.3% by primitive and settles the "500× keccak" question. |
| 0.2 | **Gas-normalise the cycle record.** `--gas`/`--gas-used` on `scripts/cycles-append.sh`; `append_cycles_for_case()` (`codegen-eest-stateless-check.sh:1548`) reads `block_gas_limit` from `manifest.tsv`. Add `cost_total` + the five category fields. |
| 0.3 | **Pin a reference workload** — `scripts/bench-workload.txt`, an explicit committed fixture list at the pinned `scripts/eest-fixture-tag.txt`, plus the gist's block 115260. Not `--random --seed N`. |
| 0.4 | **`scripts/cycles-report.sh`** — reduce the history to `{n_rows, total_steps, total_gas, steps_per_gas, cost_total, category_split}`. |
| 0.5 | **`cycles.yml` weekly job** mirroring `benchmark.yml`: spike leg with `--append-cycles --persist-cycles`, plus one ziskemu leg for authoritative cost. Needs a Linux runner with `riscv-isa-sim` (`scripts/spike/build.sh` already supports Linux x86_64). |
| 0.6 | **The reth leg** — script the `eth-act/ere-guests` `stateless-validator-reth` run on the same block and the same ziskemu version; commit the ratio as a tracked number. |

**Deliverable:** one command produces `{cost, steps, cost/gas, category split,
per-accelerator call counts, ratio vs reth}` on a pinned workload, and a weekly
job records it.

### Phase 1 — make iteration cheap (parallel with Phase 0)

1.1 Reorder `.text` (§1.3a) · 1.2 Split `GuestAddrs.lean` (§1.3b) ·
1.3 Add the hot modules to `import-metric-anchors.txt` (§1.4) ·
1.4 Migrate the `Rv64.SAsm.*` cluster (§1.3c) ·
1.5 Finish #10753 with grouped records, scoped (§1.2) ·
1.6 Retire the 476-entry whole-list `decide` (§1.3).

Byte-identity must be unchanged throughout — and note that several gates
`exit 0` when the RISC-V toolchain is incomplete, so confirm each one *ran*
rather than skipped.

### Phase 2 — the evaluation substrate + a thin reference driver

| # | Item |
|---|---|
| 2.1 | **`bench/CostHarness.lean`** — generalise `bench/DivBench.lean` by parameterising the three things it hardcodes (initial memory image, program, exit PC). Keep both cost axes. |
| 2.2 | **`scripts/eval-candidate.sh`** — the Tier-A scorer: candidate → standalone ELF → `ziskemu -X` → JSON `{steps, cost_total, categories, frops}`. |
| 2.3 | **Workload generalisation** — extend `scripts/collect-div-operands.py` to a general opcode+operand histogram, same methodology, same `bench/*-weights.json` shape. |
| 2.4 | **A thin reference driver** (`scripts/autoresearch/`): candidate → Tier A score → ranked shortlist → Tier B/C confirmation. Deliberately minimal; the search strategy is swappable. |
| 2.5 | **Correctness gate inside the loop** — a candidate is only a candidate if it agrees with the reference on the workload (`MainArithDiffCheck.lean` / `scripts/fuzz_arith_oracle.py` for ALU; `scripts/eest-ab-compare.py` for guest-level). Cost without agreement is meaningless. |

### Phase 3 — pilot on ALU opcodes (a mechanism proof, not the payoff)

**Acceptance policy:** the loop searches over **unproven** candidates scored by
cost and emits a ranked shortlist; a separate step re-derives the proof for the
winner. Nothing lands unproven.

That policy has a price, and the one precedent prices it: DIV v4→v6 was **198
lines of new assembly → 6,077 lines of Lean across 53 commits** for −27.6% DIV /
−33.3% MOD. **~30 lines of proof per line of assembly.** So bias the search
toward the two shapes where that ratio collapses:

- **DCode/SAsm** (`EvmAsm/Rv64/SAsm/Deriv.lean`). `Stmt.flatten` **synthesises
  every branch and jump offset from `Stmt.size`** — so a length change is free
  at the layout level. `Stmt.steps` is derived, not written, so there is no
  bound literal to sync. `fn_spec`'s layout side conditions close by `rfl`.
  **This is the direct structural answer to "jump destination shifts."**
- **Prepend-a-fast-path.** `divCodeV6 = CodeReq.unionAll [..., CodeReq.ofProg
  (base + v6V5Off) evm_div_v5]`
  (`EvmAsm/Evm64/DivMod/Compose/OffsetsV6.lean:70`) reframes the *entire
  existing proof* at a shifted base. This is what made DIV v6's −28% affordable
  without touching the proven core.

For anything hand-written, use **named offsets with drift checks**, not
literals — the `OffsetsV6.lean:110-135` pattern (`example : v6SetupOff =
v6ClzOff + 4 * divK_clz.length := by decide`) turns a shift into a compile error
in the right place. Already mandated by `EvmAsm/Evm64/OPCODE_TEMPLATE.md`.

Two invariants always bite, and both are mechanical: `pin_cycle_bound` kernel-
binds the registry bound to the theorem's own (you cannot edit either alone),
and byte-identity (602 `_eq_prog` guards, `scripts/check-asm-to-program.sh`
against a real assembler).

**Success criterion for the pilot is not the speedup.** It is: a candidate went
generated → scored → differentially validated → re-proven → landed, with the
cost delta visible in `cycles-history`.

### Phase 4 — pivot to where the cost is

Re-derive the ordering from Phase 0.1's counters rather than assuming it:

1. **Keccak call count** (57.3%) — node→hash memoisation across the incremental
   MPT update, paid for out of an aliased region (§3).
2. **Step count** (31.5%, linear in steps) — the §3 ledger's hot paths, warmth
   scan first.
3. **Memory** (7.2%) — the paging axis `bench/DivBench.lean` already models.
4. **Opcodes** (4.0%) — the pilot surface.

---

## 5. Open questions for reviewers

- **Q1** Is the objective ZisK cost units, or should it be prover wall-clock /
  proving time? Cost units are what `ziskemu -X` reports and what the gist
  compared; they are a model of proving cost, not proving cost itself.
- **Q2** ziskemu in this checkout is **0.18.0**; the gist used **v1.1.0-alpha**.
  Are the category names and cost weights identical? Nothing cross-compares
  until this is settled, and the version should be pinned alongside
  `scripts/eest-fixture-tag.txt`.
- **Q3** Which memory region pays for a keccak/node-hash cache (§3)?
- **Q4** Is finishing #10753 worth its one-time migration cost relative to the
  cheaper levers in §1.3?
- **Q5** Do we want per-handler slot padding in `.text` (opcode-vs-opcode
  rebuild independence) at the cost of image size?
- **Q6** Should the loop be allowed to propose *algorithmic* changes to unproven
  guest code (where `docs/spec-aligned-rewrite-workflow.md` already says
  unproven code is disposable), or restricted to routines that carry a proof?

---

## Appendix — key paths

| Purpose | Path |
|---|---|
| Churning address table | `EvmAsm/Codegen/GuestAddrs.lean`; generator `scripts/asm_to_program.py guest-addrs` |
| `.text` emission order | `EvmAsm/Codegen/Programs/Registry.lean:1342-1394` |
| Rebuild-cost metric | `scripts/import-graph-metrics.py`, `scripts/import-metric-anchors.txt`, `scripts/import-metrics-baseline.json` |
| Layout parameterisation | `EvmAsm/Codegen/GuestLayout.lean`, `GuestLayoutInstance.lean`; design in `docs/agents/guestaddrs-layout-design.md` |
| Cost harness (template) | `bench/DivBench.lean`, `bench/div-weights.json`, `scripts/{collect,sample,analyze}-div-operands.py`, `docs/divmod-evm-workload.md` |
| Guest runner | `scripts/codegen-eest-stateless-check.sh`, `scripts/spike/{spike_run.cc,zisk_accel.cc,build.sh}` |
| Cost history | `scripts/cycles-append.sh`, `scripts/cycles-history-persist.sh`, `cycles-history` orphan branch |
| Step/cost ledgers in Lean | `EvmAsm/Codegen/MemoryBudgetGuard.lean` §7/§7b, `EvmAsm/Progress/CycleBounds.lean`, `EvmAsm/Progress.lean` (`cycleBound`) |
| Cheap re-proof shapes | `EvmAsm/Rv64/SAsm/{Deriv,Flatten,Fn}.lean`, `EvmAsm/Evm64/DivMod/Compose/OffsetsV6.lean`, `docs/dcode-porting-playbook.md`, `docs/sasm-deriv.md` |
| Regen contract | `docs/regenerating-generated-files.md`, `EvmAsm/Codegen/Proofs/GuestImage.lean:94` |
| Differential oracles | `MainArithDiffCheck.lean`, `scripts/fuzz_arith_oracle.py`, `scripts/eest-ab-compare.py` |
| Accelerator ABI | `EvmAsm/Rv64/ZiskAccel.lean`, `docs/zkvm-accelerators-interface.md` |
| Benchmark run this doc cites | https://gist.github.com/pirapira/a5cc0088ade5ac31fcbed3b562e3e9b1 |
