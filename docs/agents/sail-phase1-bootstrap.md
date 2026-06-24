# Sail-zkVM integration — Phase 1 bootstrap (regeneration spike)

**For:** the next session. **Goal of P1:** prove out scoped Lean generation for
the zkVM RISC-V target on a *throwaway branch*, produce a go/no-go report, and
hand P2 a validated `SAIL_MODULES` + config + version triple. **No changes to the
main project in P1.**

> Read first, in order: `docs/sail-zkvm-integration-design.md` (RFC),
> `docs/sail-zkvm-model-review.md` (findings — esp. §1 backend, §3 closure, §4
> Zicclsm config, §5.6 decode), `docs/riscv-zkvm-compliance.md` (correspondence),
> `docs/sail-zkvm-implementation-plan.md` (the phase plan; P1 is §2).

## Context in one paragraph

The project anchors its RV64 semantics on the official Sail RISC-V model via 51
`*_sail_equiv` lemmas, but against the *full* RV64D model (153 Lean files) pinned
to a moving `rev=main` of the `dhsorens/sail-riscv-lean` fork. The locked plan
(foundation-first) is to vendor a *pinned, scoped* model (~14 modules, RV64IM
only) generated from upstream, then do all proof work on it. P1 de-risks the one
big unknown — does scoped generation work cleanly — before the P2 migration.

## Already staged (this session, toolchain-independent)

- `sail-import/rv64im-instructions.txt` — the 65-instruction RV64IM target list
  for the future coverage gate.
- `sail-import/PROVENANCE.toml` — `[current]` filled (dhsorens @
  `6009afb1…`, lean-sail v3, toolchain `v4.30.0-rc1`); `[target]` has the module
  closure + TODOs P1 fills.
- `scripts/regen-sail-model.sh` — recipe skeleton; `--plan` prints the pipeline.

## P1 tasks

1. **Build Sail from source with the Lean backend.** Released Sail has no Lean
   backend (see `.lake/packages/Lean_RV64D/README.md`): clone
   `rems-project/sail`, `opam pin add sail`, `dune build --release && dune
   install`. Needs `opam`, `z3`, `gmp`, `pkg-config`, `cmake`. **This may be the
   hard part / may not be feasible in-env — if so, that itself is the P1 finding;
   report and stop.** Fresh clones needed (the scratchpad clones from the design
   session are gone — scratchpad is per-session).
2. **Clone `riscv/sail-riscv`** at a candidate commit; record it.
3. **Produce the zkVM config** `sail-import/riscv64im_zicclsm.json` from
   `--print-default-config`, set per review §4: `base.xlen=64`,
   `extensions.{M=true, A=F=D=V=false, S=false, U=false, Zicclsm=true,
   Zicsr=true}`, `memory.misaligned.exceptions.load_store={"None":null}`, single
   flat RAM region. (`validate_config.sail` requires S and U toggled together.)
4. **Generate the scoped Lean model**:
   `cmake -DSAIL_MODULES="--module prelude --module core --module exceptions
   --module pmp --module sys --module I_types --module I_insts --module M_types
   --module M_insts --module postlude" …` then
   `cmake --build <build> --target generated_lean_rv64d`.
5. **Measure & decide (the deliverable):** write `docs/agents/sail-regen-spike.md`:
   - Did it generate and type-check? Which exact Sail commit / target toolchain?
   - The generated `Register` enum — how much vector/CSR state does `sys` drag in
     (review §3 caveat)? Is the state vector acceptably small?
   - Is the generated decode `bv_decide`-free (review §5.6)?
   - Do the in-scope `execute_*` (RTYPE/ITYPE/LOAD/STORE/MUL/DIV/REM) match the
     shapes the existing `*_sail_equiv` lemmas expect (v3→v4 signature drift)?
   - **GO** (scoped generation clean) **or FALLBACK** (full-model-at-new-toolchain
     + scope gate, plan §1.2.2).
   - Fill `sail-import/PROVENANCE.toml [target]` and the pins in
     `scripts/regen-sail-model.sh`.

## Version reconciliation (do not skip — review §1.1, corrected)

Backend hardcodes lean4 **v4.29.0** / mathlib v4.29.0 / lean-sail **v4**; the
project is on lean4 **v4.30.0-rc1** / lean-sail **v3** — i.e. the project is
*ahead* of the backend's default target. P1 must determine the compatible triple
(which Sail commit + lean-sail rev generates Lean usable on v4.30.0-rc1, or
whether to align the project toolchain). This decision gates all of P2.

## Workflow / conventions

- Throwaway branch off latest `main`; P1 lands only the spike report + the filled
  `sail-import/*` skeletons + (if config produced) `riscv64im_zicclsm.json`. No
  proof/model changes.
- No `bd` in this environment — track via the proposed bead structure below
  (create when `bd` is available).
- End P1 by writing `docs/agents/sail-phase2-bootstrap.md` for the migration.

## Proposed bead structure (parent + children)

```
sail-zkvm-integration            (parent)
├─ p1-regen-spike                (this phase; go/no-go + version triple)
├─ p2-foundation-migration       (toolchain reconcile + vendor scoped model + re-point 51 lemmas + drop fork)
├─ p3-differential-testing       (executable Lean vs Sail C sim / riscv-tests)
├─ p4-consolidated-sim-theorem   (step_execute_sail_sim)
├─ p5-full-rv64im-coverage       (add 12 word-ops + lemmas)
├─ p6-gates-and-ledger           (check-isa-scope/coverage/config + CI-regen compliance doc)
└─ p7-decode-tie                 (fetch→decode→execute end-to-end)
```

## Exit criteria for P1

A committed `docs/agents/sail-regen-spike.md` with a clear GO/FALLBACK verdict,
the measured `Register` enum, the decode `bv_decide` finding, the resolved
version triple, and `PROVENANCE.toml [target]` + `regen-sail-model.sh` pins
filled — enough that P2 can start without re-discovering any of it.
</content>
