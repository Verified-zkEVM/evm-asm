# Implementation plan: Sail-anchored zkVM RISC-V semantics

**Status:** Plan — sequencing **locked foundation-first** (2026-06-24). Capstone of the three design
docs: [`sail-zkvm-integration-design.md`](sail-zkvm-integration-design.md) (RFC),
[`sail-zkvm-model-review.md`](sail-zkvm-model-review.md) (findings),
[`riscv-zkvm-compliance.md`](riscv-zkvm-compliance.md) (correspondence).
**Audience:** maintainers deciding how and in what order to build this.

---

## 1. The chosen strategy — foundation-first

**Decisions locked (2026-06-24):** (1) **pipeline/migration first** — establish
the correct substrate before proof work; (2) **full RV64IM coverage** — add the
12 word-ops + lemmas; (3) **vendor** the regenerated scoped model in-tree now.

The rationale: do not build the consolidated theorem, gates, and decode tie on a
model + toolchain we are about to replace, only to migrate them. Stand up the
*right* foundation once — a pinned, scoped, vendored, regenerable model on the
correct toolchain — then do every proof on it exactly once.

### 1.1 The one hard coupling: bump + swap are inseparable

The Sail backend's hardcoded target is **Lean `v4.29.0` / mathlib `v4.29.0` /
lean-sail `v4`** (review §1.1); the project is on **`lean4:v4.30.0-rc1`** /
lean-sail `v3` via the dhsorens model — i.e. *ahead* of the backend default. So
this is a **version reconciliation**, not a simple forward bump: P1 must find a
Sail commit + lean-sail rev whose Lean output works on v4.30.0-rc1 (or decide to
move the project toolchain). Either way you **cannot** adopt the regenerated
model without reconciling the toolchain, nor reconcile while keeping the old
model. So the toolchain reconciliation, the dependency swap, and the
repair/re-pointing of the existing 51 `*_sail_equiv` lemmas + the ~300 KB proof
base are **one large coupled migration** — and, per the chosen ordering, it lands
early. This is the highest-risk phase; §1.2 is how we de-risk it.

### 1.2 De-risking the front-loaded migration

1. **Spike before committing (P1).** Prove scoped generation works and inspect
   the artifact on a *throwaway* branch before touching the project.
2. **Explicit fallback.** If scoped generation is messy (e.g. the `sys` residue
   pulls unacceptable vector/CSR state, review §3), fall back to *full model at
   the new toolchain*, vendored + pinned, and rely on the **scope gate** to
   enforce scoping in our layer. Scoping-by-generation can then be revisited.
3. **Long-lived migration branch.** The bump+swap+repair proceeds on its own
   branch, incrementally, never blocking documentation or planning work.
4. **The proof base is the schedule risk, not the model.** Most of the migration
   effort is making the existing proofs compile on 4.29.0/mathlib-v4, independent
   of Sail. Treat it as a standard toolchain bump with the Sail swap layered in.

### 1.3 Phase order

```
P1 spike (throwaway) ─► P2 FOUNDATION MIGRATION (bump + vendor scoped model + repair proofs)
   ─► P3 differential testing ─► P4 consolidated sim theorem ─► P5 full RV64IM coverage
   ─► P6 scope/coverage gates + CI-regenerated ledger ─► P7 decode tie ─► (P8 optional)
```

---

## 2. Per-phase plan (foundation-first)

Each phase = one feature branch, one (or few) PRs, one bead, fitness-functions
**seeded green**. Follows the project's one-phase-per-session workflow (memory:
`steering-rollout-workflow`), with a `docs/agents/sail-phaseN-bootstrap.md` at
each hand-off.

### P1 — Regeneration spike & go/no-go *(throwaway branch; ~1 session)*
- **Deliverable:** a *report* (`docs/agents/sail-regen-spike.md`), no project
  changes. On a scratch clone of `riscv/sail-riscv` + `rems-project/sail`, run
  the Lean target with the scoped closure
  `-DSAIL_MODULES="--module prelude --module core … --module M_insts --module postlude"`
  (review §3) and the `riscv64im_zicclsm` config (review §4).
- **Measure:** Does it generate & type-check? What is the actual generated
  `Register` enum — i.e. how much vector/CSR state does `sys` drag in (review
  §3)? Is the generated decode `bv_decide`-free (review §5.6)? Which exact Sail
  version pins the v4.29.0 output?
- **Decision:** scoped-generation **go**, or **fallback** to full-model-at-new-toolchain
  + scope gate (§1.2.2).
- **Exit:** a recommended `SAIL_MODULES` + config + version triple, ready for P2.

### P2 — Foundation migration *(long-lived branch; the heavy lift, multi-session)*
The one coupled migration (§1.1). Recommended internal order:
1. **Toolchain bump alone first:** Lean `4.28→4.29.0`, mathlib, `lean-sail v3→v4`
   — while *still on the dhsorens model if it builds at v4*, or a minimal stub —
   to isolate "does the proof base survive the toolchain?" from the Sail swap.
   (If dhsorens won't build at v4, this step merges with the swap.)
2. **Vendor the scoped model:** generate per P1, commit under `vendor/sail-riscv-zkvm-lean/`
   (the durable, self-owned package), add `lakefile` path-dep.
3. **Provenance + regen:** `sail-import/PROVENANCE.toml` (sail-riscv commit, sail
   commit, lean-sail rev, module list, config hash, toolchain), `scripts/regen-sail-model.sh`,
   `scripts/check-sail-pin.sh` (blocking — guards all of the above).
4. **Re-point the tie:** repair the 51 `*_sail_equiv` lemmas + `StateRel` /
   `toSailInstr?` against the new scoped model (signatures/state types may shift
   v3→v4). **This is the gate that the new foundation actually carries our tie.**
5. **Drop the dhsorens fork** from `lakefile.toml`.
- **Verify:** full `lake build` green on 4.29.0; `#print axioms` clean; all
  existing gates pass; the 51 lemmas hold against the vendored model.

### P3 — Differential testing of the vendored model *(~1–2 sessions)*
- **Deliverable:** generate the *executable* Lean variant (`--lean-executable`)
  and run it against the Sail C reference simulator and/or `riscv-tests` on the
  RV64IM subset; wire as a CI job.
- **Why:** the active mitigation for the experimental backend — the headline
  trust item (review §1). Turns "trust the translator" into "the generated model
  passes the reference conformance suite."

### P4 — Consolidated simulation theorem *(~1 session)*
- **Deliverable:** `EvmAsm/Rv64/SailEquiv/StepSim.lean` —
  `step_execute_sail_sim : toSailInstr? i = some si → StateRel … → ∃ sSail', runSail (execute si) … = some (RETIRE_SUCCESS, sSail') ∧ StateRel (execInstrBr …) sSail'`,
  by `cases i` over the (now re-pointed) per-instruction lemmas; uniform
  PC-agreement (review §5.5).
- **Verify:** builds; `#print axioms` = 3 classical axioms only.
- **Output:** the single auditable "our step *is* RISC-V" object, on the right model.

### P5 — Full RV64IM coverage *(~1–2 sessions)*
- **Deliverable:** add the 12 word-ops to `EvmAsm.Rv64.Instr` (SLLIW SRLIW SRAIW
  ADDW SUBW SLLW SRLW SRAW MULW DIVW DIVUW REMW REMUW), their `execInstr`
  semantics, `toSailInstr?` mappings (Sail `RTYPEW`/`SHIFTIWOP`/`MULW`/`DIVW`/`REMW`
  clauses), and `*_sail_equiv` lemmas; extend `step_execute_sail_sim`'s `cases`.
- **Verify:** model now covers **all of RV64IM**; coverage list (P6) matches with
  no gap.

### P6 — Scope/coverage gates + CI-regenerated ledger *(~1 session)*
- **Gates:** `check-isa-scope.sh` (only in-target constructors referenced),
  `check-isa-coverage.sh` (our set == checked-in `sail-import/rv64im-instructions.txt`),
  `check-sail-config.sh` (config matches the §1 keys).
- **Ledger:** make [`riscv-zkvm-compliance.md`](riscv-zkvm-compliance.md)
  regenerate from a registry (extend `EvmAsm/Progress.lean` or a sibling), guarded
  by `check-compliance-doc.sh` (identical-regen, like `check-progress.sh`).

### P7 — Decode tie *(several sessions; the real semantic gap)*
- **Deliverable:** `EvmAsm/Rv64/SailEquiv/DecodeSim.lean` —
  `bytesAt sRv pc = w → ext_decode w = some si → toSailInstr? i = some si`, folded
  into a fetch→decode→execute end-to-end `step` simulation. (P1/P2 already
  confirmed the subset decode is `bv_decide`-free.)
- **Verify:** end-to-end `step` theorem; axiom + forbidden-tactic gates green.
- **Note:** the half that matters most for a zkVM (the prover commits to bytes).

### P8 (optional) — Definitional derivation
- `execInstrFromSail := project ∘ runSail (execute ∘ toSailInstr?) ∘ embed`,
  proven `= execInstrBr` via P4. Mostly rhetorical once P4+P7 exist; defer.

---

## 3. Dependency graph & what parallelizes

```
P1 spike ─► P2 foundation migration ─┬─► P3 differential testing
                                      ├─► P4 sim theorem ─► P5 full coverage ─► P7 decode tie ─► (P8)
                                      └─► P6 gates + ledger
```

- **Hard ordering:** P1 before P2 (de-risk before the migration). P2 before
  *everything* else (it establishes the foundation all proofs run on). P4 before
  P5 (coverage extends the consolidated `cases`) and before P7 (decode reuses the
  execute sim).
- **Parallelizable after P2:** P3 (differential testing, infra) ‖ P4 (proofs)
  ‖ P6 (gates/ledger) — different surfaces.
- **Critical path:** P1 → P2 → P4 → P5 → P7. P2 dominates the schedule.

---

## 4. Conventions (align with existing project machinery)

- **Branching:** one feature branch per phase off latest `main`; conventional-commit
  PR titles (`feat(sail): consolidated step simulation theorem`).
- **Beads:** one parent bead `sail-zkvm-integration` with a child per phase;
  honor the `bd close` rules (deliverable must be grep-visible on `origin/main`).
- **Fitness functions:** every new `check-*.sh` seeded **green** on the current
  tree (steering review rule), registered in `AGENTS.md`'s gate table + wired in
  `.github/workflows/build.yml`. Blocking vs advisory per design §6.2.
- **Heartbeats/axioms:** no `maxHeartbeats` bumps; `#print axioms` clean; no
  `native_decide`/`bv_decide`. The decode tie (B4) must actively confirm this.
- **Per-phase hand-off:** a `docs/agents/sail-phaseN-bootstrap.md` at each
  session boundary (matches the steering rollout workflow).

---

## 5. Risks & mitigations

| Risk | Phase | Mitigation |
|---|---|---|
| **Front-loaded migration breaks the proof base** (the schedule risk) | P2 | P1 spike de-risks first; bump toolchain *alone* before the Sail swap to isolate causes; long-lived branch, incremental; standard toolchain-bump playbook. |
| `sys` drags vector/CSR state, scoped trim isn't clean | P1 | Spike *measures* the `Register` enum before commitment; fallback = full-model-at-new-toolchain + scope gate (§1.2.2). |
| New scoped model shifts `execute_*`/state signatures, breaks the 51 lemmas | P2.4 | Re-pointing the tie is an explicit, gated P2 step — the proof the new foundation carries our semantics. |
| Experimental backend mistranslates | P3 | Differential testing vs Sail C sim / `riscv-tests`; backend fails-loud in known cases; small subset minimizes surface. |
| `match_bv`→`bv_decide` in generated decode | P1/P7 | Spike confirms decode `bv_decide`-free; `check-forbidden-tactics.sh` gate. |
| Word-op coverage incomplete | P5 | Add all 12 + lemmas; `check-isa-coverage.sh` makes any residual gap loud. |
| ECALL divergence misread as a bug | P6 | Named ledger line; governed by host-ABI specs, not a Sail equiv. |

---

## 6. Decisions — locked (2026-06-24)

1. **Sequencing:** ✅ **pipeline/migration first** (foundation-first, §1).
2. **Word-op coverage:** ✅ **add the 12 `.W` instructions + lemmas** (P5) — the
   model will cover all of RV64IM.
3. **Model source:** ✅ **vendor the regenerated scoped model in-tree** now
   (`vendor/sail-riscv-zkvm-lean/`, P2) — self-owned and reproducible from day
   one.

First concrete action: **P1 — the regeneration spike** on a throwaway branch
(no project changes), producing the go/no-go report + the recommended
`SAIL_MODULES`/config/version triple that P2 consumes. This is the cheapest way
to retire the biggest unknown (does scoped generation work, and how clean is the
result) before committing to the migration.

### Note on the front-loaded-risk tradeoff
This ordering deliberately puts the hardest phase (P2) early. The upside chosen:
never migrate proofs twice — every theorem is written once, on the final model
and toolchain. The cost accepted: audit/legibility deliverables (P4/P6) land
*after* the migration rather than before. P1 + the §1.2 fallback keep P2 from
becoming a dead end.
</content>
