# Sail-zkVM integration — Phase 2 bootstrap (foundation migration)

**For:** the next session. **Goal of P2:** vendor a pinned, scoped RV64IM Lean
model in-tree, get it to **build in-project**, and re-establish the 51
`*_sail_equiv` lemmas against it — dropping the moving `dhsorens` fork. This is the
locked **foundation-first** step. P1 (the regen spike) is done: verdict
**🟡 CONDITIONAL GO** — generation works, but a real version reconciliation remains
and is now P2's central task.

> Read first, and trust it over the design doc: `docs/agents/sail-regen-spike.md`
> (esp. "What does NOT work yet" + "The version finding" + "What P2 must decide").
> Then `sail-import/PROVENANCE.toml [target]` and `scripts/regen-sail-model.sh`.

## What P1 settled (don't re-discover)

- **Sail + Lean backend is installed** (opam switch `sail`, 0.19.1). z3 4.15.3 at
  the nix path in `regen-sail-model.sh`. No build-from-source for *this* Sail.
- **Working generation recipe**: `scripts/regen-sail-model.sh --run <dir>` →
  sail-riscv `1760ee2`, positional modules `main I_insts M_insts`, config
  `sail-import/riscv64im_zicclsm.json`. ~84 files. Decode is `bv_decide`-free.
  `execute_*` *signatures* match the lemmas. Word-ops already present (P5 is
  lemmas-only).
- **Config is validated** (`riscv64im_zicclsm.json`, sha256 `7dd1fa11…`).

## The crux P1 uncovered (was hidden by a wrong first draft)

**The 0.19.1-emitted model does NOT build drop-in against the project's pinned
lean-sail v3 on v4.30.0-rc1.** Measured by actually building it:

- 0.19.1's model assumes lean-sail **v4** (`79b4d08`, lean4 v4.29.0): wants
  `open ConcurrencyInterfaceV1`, `Arch`-as-a-class, `sail_barrier`.
- Against project **v3** (`49ccc5a`, which *does* build on v4.30.0-rc1) the model
  fails: `Access_variety` universe metavar → then `Arch` not-a-class,
  `sail_barrier` unresolved, duplicate `ExceptT.map_error`.
- The generator's **inline runtime** copy is pre-v4.30 (`BitVec.getMsb'`,
  `String.Slice`, an `IntRange` omega that v4.30 rejects). v3 is precisely the
  v4.30-patched runtime — but a *different* model-match.

So the original review §1.1 skew is real: **Sail 0.19.1 ↔ lean-sail v4 ↔ lean4
v4.29.0** vs **project v3 ↔ v4.30.0-rc1**. No single existing lean-sail rev both
matches a 0.19.1 model *and* builds on v4.30.0-rc1.

## P2's reconciliation decision (pick one — none is free)

- **Path A — align project to backend:** lean4 `v4.29.0` + lean-sail `v4`, vendor
  the 0.19.1 model drop-in. *Downgrades the project's Lean; re-points 51 lemmas.*
- **Path B (recommended) — keep v4.30, patch v4 forward:** vendor the 0.19.1 model
  + lean-sail `v4`, backport v3's v4.30 fixes onto v4 (`getMsb`, `String.Slice`
  `.toString`, `IntRange` omega — all visible in the v3↔v4 diff). *Keeps the
  project on v4.30.0-rc1; cost is a maintained runtime patch.*
- **Path C — match v3 at source:** build the older Sail commit whose emitted model
  matches lean-sail `v3`, and regenerate. *Reintroduces "build a specific Sail from
  source"; yields a true drop-in on the project's working v3.*

## P2 task order

1. **Confirm the match.** Build the scoped 0.19.1 model against lean-sail **v4**
   (`79b4d08`) — verify v4 resolves the `Arch`/`sail_barrier`/`Access_variety`
   drift that the v3 attempt hit. The scratchpad work stopped exactly here.
2. **Resolve the runtime** per the chosen path (B: clone lean-sail `v4`, backport
   the three v4.30 fix-classes from v3, confirm it builds on v4.30.0-rc1).
3. **Regenerate + vendor** under `vendor/sail-riscv-zkvm-lean/`
   (`regen-sail-model.sh --run`), replacing only the generator's `lean-toolchain`/
   `lakefile.toml` scaffolding; keep the model's `Out/Sail` → external-runtime
   wiring (`import Sail.*`, add `open ConcurrencyInterfaceV1` to model files — the
   generator omits it for v3 but the v4 model needs it; verify whether v4-target
   generation emits it).
4. **Re-point** `lakefile.toml`/`lake-manifest.json` off `dhsorens` to the vendored
   package; drop `rev=main`.
5. **`lake build`**; fix the lemma re-pointings — start with `bool_to_bit →
   bool_to_bits` in `ALUProofs` SLT/SLTU/SLTI; `diff` regenerated-vs-vendored first
   to enumerate the rest. Get the 51 `*_sail_equiv` lemmas green.
6. **Axiom hygiene** unchanged (`[[bv-decide-purge]]`: 0 custom axioms); no
   forbidden tactic in vendored code (the runtime's lone `try bv_decide` BEq macro
   is pre-existing). Update `PROVENANCE.toml` (set `lean_sail_rev`), PLAN.md, and
   write `docs/agents/sail-phase3-bootstrap.md`.

## Exit criteria

Project builds against the **vendored, pinned, scoped** model with `dhsorens`
removed; the runtime reconciliation resolved + recorded; all 51 `*_sail_equiv`
lemmas green; axiom hygiene preserved.

## Bead tree (`bd` still not installed)

```
sail-zkvm-integration (parent)
├─ p1-regen-spike            ✅ DONE — CONDITIONAL GO (docs/agents/sail-regen-spike.md)
├─ p2-foundation-migration   ← THIS PHASE (version reconciliation is the crux)
├─ p3-differential-testing
├─ p4-consolidated-sim-theorem
├─ p5-full-rv64im-coverage   (word-ops already in model; lemmas-only)
├─ p6-gates-and-ledger
└─ p7-decode-tie
```
