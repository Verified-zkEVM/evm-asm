# Sail-zkVM integration — Phase 3 bootstrap (differential testing + P2 residuals)

**For:** the next session. **Context:** P2's core migration is **DONE and green** (see
`sail-phase2-bootstrap.md`). The project builds against the vendored, release-pinned,
scoped RV64IM model (`require out from "vendor/sail-riscv-zkvm-lean"`); `dhsorens` is
gone from the build; all 51 `*_sail_equiv` lemmas pass; full `lake build EvmAsm` =
2984/2984, exit 0.

> ⚠️ **Read `sail-adversarial-review.md` FIRST.** An independent review (2026-06-25)
> verified the build/lemmas/scoping but found three overstated trust claims and two stale
> doc surfaces. The corrections change the recommended order below — in particular the
> "axioms = 3 classical only" claim is **false for memory ops** (they carry Sail platform
> axioms), so P4's exit criterion as originally written is unachievable. Details + the
> corrected priority list (trust-hygiene + gates BEFORE P4) are in that doc.

**Two tracks are now unblocked and parallelizable**:
- **P3 — differential testing** (this doc's headline; the trust mitigation for the
  experimental Lean backend).
- **P4 — consolidated sim theorem** (pure-Lean; arguably the higher-value *proof* next
  step now that the 51 lemmas are re-pointed). Doable without the regen toolchain.

> Read first: `sail-import/PROVENANCE.toml` (`[current]` now == `[target]`; the
> migration note records what's proven). Deliverable specs for this phase live in
> this bootstrap doc (and the parallel P4 notes below); there is no separate
> successor to the removed implementation-plan doc.

## Recommended order (CORRECTED by the adversarial review)

The original "start with P4" is superseded. Cheapest-and-highest-leverage first
(full rationale in `sail-adversarial-review.md §Assessment`):

0. **Trust hygiene** — DONE this session (2026-06-25): F4 stale docs fixed
   (`PROGRESS.md`, `scripts/progress-template.md`, `README.md`, `AGENTS.md`); F2
   `model_sha256` recipe pinned reproducibly (hash was correct, recipe underspecified);
   F1 PROVENANCE note + P4 exit criterion corrected. Remaining residual: F5/F6 (softfloat
   coverage note, config validate) — fold into P6.
1. **P4 — consolidated sim theorem, corrected spec** (pure Lean, ~1 session). The single
   auditable "our step *is* RISC-V" object. Exit = builds + axioms ⊆ {classical} ∪
   {platform allowlist}; see corrected Verify below.
2. **P6 gates, promoted ahead of P3** (pure-repo). `check-forbidden-tactics.sh` +
   `check-axioms.sh` (enforce the F1 allowlist) + `check-sail-pin.sh` (after F2). Closes
   F3 — there is currently NO CI gate for axioms or forbidden tactics, so the bv_decide
   purge / axiom hygiene can silently regress.
3. **P3 — differential testing.** The *essential* mitigation (GO so far = "builds +
   type-checks", NOT "proven correct against the reference"), but infra-heavy and the only
   track that can't start cold — needs the Sail toolchain (opam `sail5`, Sail 0.20.2,
   z3 4.15.3). Do when that environment is available.

### P4 — Consolidated simulation theorem (~1 session, pure Lean)
- **Deliverable:** `EvmAsm/Rv64/SailEquiv/StepSim.lean` —
  `step_execute_sail_sim : toSailInstr? i = some si → StateRel … → ∃ sSail', runSail (execute si) … = some (RETIRE_SUCCESS, sSail') ∧ StateRel (execInstrBr …) sSail'`,
  by `cases i` over the per-instruction `*_sail_equiv` lemmas; uniform PC-agreement
  (model review §5.5).
- **Verify:** builds; `#print axioms step_execute_sail_sim` ⊆ {3 classical} ∪ {Sail
  platform allowlist: `plat_term_write, load_reservation, match_reservation,
  sys_enable_experimental_extensions`}. **NOT "3 classical only"** — memory ops legitimately
  carry the platform axioms (verified `#print axioms ld_sail_equiv`); the consolidated
  theorem inherits them. Enumerate + justify the allowlist as the model's trust boundary.
  (Pattern: `lake env lean` on a scratch file that `#print axioms`.)

### P3 — Differential testing of the vendored model (~1–2 sessions, infra)
- **Deliverable:** generate the *executable* Lean variant (`--lean-executable` in
  `scripts/regen-sail-model.sh`) and run it against the Sail C reference simulator
  and/or `riscv-tests` on the RV64IM subset; wire as a CI job.
- **Why:** turns "trust the translator" into "the generated model passes the reference
  conformance suite." Headline trust item (model review §1).
- **Note:** needs the regen toolchain (opam switch `sail5`, Sail 0.20.2, z3 4.15.3) —
  same as the residual config work below.

## P2 residuals carried forward (do alongside, none block P3/P4)

5. **Config revalidate.** `sail-import/riscv64im_zicclsm.json` was produced against
   sail-riscv `1760ee2`; **regenerate/revalidate against the release tag
   `2026-06-22-b5a2182`'s config schema** and tighten: single flat RAM region; justify
   the kept extensions (Zicntr/Zihpm/Zifencei) vs the zkVM standard; **actually run
   `validate_config`** (P1 only confirmed it *generates*). Needs the regen toolchain.
6. **Scoping decision — RECORD AS DECIDED (scoped).** The vendored model is scoped
   (`main I_insts M_insts`, 113 files) and everything builds + all 51 lemmas pass + full
   project green. Scoped gave 163 vs 178 registers and did NOT reduce generation memory,
   but it's a smaller trust/attack surface and is sufficient for RV64IM. **Decision:
   ship scoped**; the only follow-on is a coverage gate (P6 `check-isa-scope.sh` /
   `check-isa-coverage.sh`) once P5 adds the 12 word-ops. Write this into the design doc's
   open-questions section so it stops being "open".
7. **Gates + ledger hygiene.**
   - **DONE this session:** axiom hygiene (3 classical axioms on `*_sail_equiv`);
     forbidden-tactic scan of vendored `Out/` + proof files = clean.
   - **TODO:** write `scripts/check-sail-pin.sh` — assert the resolved dep matches
     `PROVENANCE.toml [target]` (`model_sha256` over vendored `*.lean`, `lean_sail_rev`
     `79b4d08`, `out` path require present, `dhsorens` absent). The model_sha256 recipe
     is in PROVENANCE: `find -name '*.lean' | sort | xargs sha256sum | sha256sum`.
   - **TODO:** de-`nix` the z3 store path in `scripts/regen-sail-model.sh` before CI
     (machine-specific). Note the ~9-min/~7-GB regen cost in the ledger.

## Exit criteria (P3)

Executable Lean model passes the RISC-V conformance subset (Sail C sim / `riscv-tests`)
on RV64IM, wired as a CI job; `check-sail-pin.sh` green; config revalidated against the
tag. (P4, if done first/in parallel: `step_execute_sail_sim` builds, 3-axiom clean.)

## Housekeeping

- **Synced.** `feat/sail-zkvm-integration` is pushed; local and `origin` both at
  `ba45cc4d`. No manual push pending.
- Untracked `docs/agents/phaseN-bootstrap.md` + `rollout-complete.md` are unrelated
  steering-rollout leftovers — leave them.

## Bead tree (`bd` still not installed)

```
sail-zkvm-integration (parent)
├─ p1-regen-spike            ✅ DONE — GO, proven end-to-end (docs/agents/sail-regen-spike.md)
├─ p2-foundation-migration   ✅ CORE DONE — vendored + repointed + 51 lemmas green + full build 2984/2984 (residuals 5–7 here)
├─ p3-differential-testing   ← THIS PHASE (essential — backend is experimental)
├─ p4-consolidated-sim-theorem  ← ALSO UNBLOCKED (pure Lean; parallel with P3)
├─ p5-full-rv64im-coverage   (word-ops already in model; lemmas-only)
├─ p6-gates-and-ledger       (scope/coverage gates; check-sail-pin.sh; portable regen)
└─ p7-decode-tie
```
