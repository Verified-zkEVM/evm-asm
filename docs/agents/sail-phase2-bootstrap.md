# Sail-zkVM integration — Phase 2 bootstrap (foundation migration)

**For:** the next session. **Goal of P2:** vendor the (now-proven) current-upstream
scoped RV64IM Lean model into evm-asm, build it in-project, drop the moving
`dhsorens` fork, and re-establish the 51 `*_sail_equiv` lemmas against it.

**Status (2026-06-25):** steps 1–4 DONE — **the core P2 migration is complete and
green.** `dhsorens` is gone from `lakefile.toml`/`lake-manifest.json`; the project
builds against the vendored model (`require out from "vendor/sail-riscv-zkvm-lean"`).
Full `lake build EvmAsm` = **2984/2984, exit 0**. All **51 `*_sail_equiv` lemmas green**;
axioms = `{propext, Classical.choice, Quot.sound}` only (no custom axioms, no `sorryAx`);
no forbidden tactic in vendored or proof code. The `LeanRV64D → Out` rename was **100%
mechanical** — the feared `bool_to_bit → bool_to_bits` rename was a PHANTOM (both old and
new model use `bool_to_bit`; the doc below had it backwards). Residual P2 items 5–7
(config revalidate, scoping write-up, pin gate) are tracked below and in
`docs/agents/sail-phase3-bootstrap.md`; none block downstream proof work.

**What proved out (the two real risks, both retired):**
- lean-sail **v4 + mathlib-`master` coexist** in the real evm-asm build (StateRel +
  2984-job full build). This was the one unverified step-1 risk.
- The 51 lemmas re-point with **zero genuine logic renames** — pure `LeanRV64D → Out`.

> Read first: `sail-import/PROVENANCE.toml [target]` (the proven pins + `vendor_path`
> + `model_sha256`). Then `scripts/regen-sail-model.sh` (the validated regen recipe)
> and `docs/agents/sail-regen-spike.md` (the GO report) only if you need to regenerate.

## Proven foundation (DONE — don't re-litigate)

- **Toolchain stack:** Sail **0.20.2** (opam switch `sail5`, OCaml **5.4.1** — 4.14.2
  stack-overflows, sail#1674) + sail-riscv release tag **`2026-06-22-b5a2182`** +
  external **lean-sail v4** (`79b4d08`) on lean4 **v4.30.0-rc1** (NO bump). z3 4.15.3
  at the nix path in `regen-sail-model.sh` (machine-specific — de-nix before CI).
- **Generation works** (step ✔): `scripts/regen-sail-model.sh --run <dir>` → 113
  files, scoped `main I_insts M_insts`, decode `bv_decide`-free.
- **Matched pair builds** (step ✔): that model + lean-sail v4 → `lake build` 84/84,
  exit 0.
- **VENDORED + re-proven from git (step 2, commit `a2dedf448`):**
  `vendor/sail-riscv-zkvm-lean/` (113 `.lean`, package `out`, lib `Out`). Its
  `lakefile.toml` **git-pins lean-sail @ `79b4d08`** (tag v4); `lean-toolchain` =
  v4.30.0-rc1. A clean `lake build` from the committed dir — fetching lean-sail fresh
  from the pinned rev — gives **84/84, exit 0**. `model_sha256` recorded in PROVENANCE.
  Package/lib names kept verbatim from the proven artifact (renaming the lib would
  rewrite every internal `import Out.*`).

## The step 3/4 seam (mapped — start here)

**Current wiring (to remove):** `lakefile.toml:11-14` requires `Lean_RV64D` from
`git = dhsorens/sail-riscv-lean, rev = "main"` (moving!). Resolved rev in PROVENANCE
`[current]` = `6009afb1…`. The model enters the project through **one bridge file**:

- `EvmAsm/Rv64/SailEquiv/StateRel.lean` — `import LeanRV64D`; `open LeanRV64D.Functions`;
  builds `SailState` on `PreSail.SequentialState RegisterType trivialChoiceSource`,
  `SailM`, `sailRegVal`, `sailStateWithReg`, `runSail`, `StateRel`.
- The **51 lemmas** live in 6 files under `EvmAsm/Rv64/SailEquiv/`: `ALUProofs`,
  `MExtProofs`, `BranchProofs`, `ShiftProofs`, `ImmProofs`, `MemProofs` (+ supporting
  `MonadLemmas`). They `open LeanRV64D.Functions` and call `LeanRV64D.Functions.xlen`,
  `execute_*`, etc.

**Old → new namespace correspondence (verified in the vendored model):**

| Old (`dhsorens` `LeanRV64D`) | New (vendored `Out`) | Where (new) |
|---|---|---|
| `import LeanRV64D` | `import Out` | `Out.lean` (root) |
| `open LeanRV64D.Functions` | `open Out.Functions` | 109 modules use `namespace Out.Functions` |
| `LeanRV64D.Functions.xlen` | `Out.Functions.xlen` | `Out/Xlen.lean` (now its own module) |
| `execute_*` | `Out.Functions.execute_*` | `Out/InstsEnd.lean` |
| `RegisterType` | `Out.…RegisterType` | `Out/RiscvExtras.lean` |
| `trivialChoiceSource` | (in `Out/Defs.lean`) | — |
| `SailM` | (in `Out/TypesExt.lean`) | — |
| `PreSail.SequentialState` | unchanged | from `import Sail` (lean-sail) |

So step 4 is **mostly a mechanical `LeanRV64D` → `Out` rename** plus a small set of
genuine logic/symbol renames. **Known so far:** `bool_to_bit → bool_to_bits`
(`Out/Prelude.lean`), hit by `ALUProofs` SLT/SLTU/SLTI. Enumerate the rest by diffing
the regenerated model against the old vendored `Lean_RV64D` BEFORE editing lemmas
(`lake` will fetch dhsorens once; diff its `Functions` against `Out/`).

## Remaining work (ordered)

3. ✅ **DONE — Repoint the project.** `lakefile.toml`: `Lean_RV64D` git-require →
   `require out` (path `vendor/sail-riscv-zkvm-lean`). `lake update out` re-resolved
   cleanly: `Lean_RV64D`→`out`, `Sail` v3 (`49ccc5af`)→v4 (`79b4d08`), **mathlib stayed
   pinned** at `e2f607b` (avoided the bare-`lake update` float). `StateRel.lean`:
   `import LeanRV64D`→`import Out`, `open LeanRV64D.Functions`→`open Out.Functions`.
   StateRel + full downstream compile.
4. ✅ **DONE — Re-point the 51 `*_sail_equiv` lemmas.** Global `LeanRV64D → Out` across
   the 8 remaining SailEquiv files (`.Functions.{not,xlen,log2_xlen}` map 1:1; `bool_to_bit`
   unchanged). **Zero compiler-guided repair needed** — all 51 green on first build.
5. **Config:** regenerate/revalidate `riscv64im_zicclsm.json` against the *tag's* schema
   (changed since 1760ee2) and tighten — single flat RAM region; justify kept extensions
   (Zicntr/Zihpm/Zifencei) vs the zkVM standard; actually exercise `validate_config`
   (P1 only confirmed it *generates*).
6. **Scoping decision (open).** Scoped gives 163 vs 178 registers and did NOT reduce
   generation memory — decide scoped vs full-model + a coverage/scope gate, record it.
7. **Hygiene + gates:** re-run axiom hygiene (expect 0 custom axioms, `[[bv-decide-purge]]`)
   — the vendored model adds 113 files, so re-verify the trust base; no forbidden tactic
   in vendored code; wire `model_sha256`/lean-sail-rev into `check-sail-pin.sh`; de-`nix`
   the z3 path in the regen recipe; note the 9-min/7-GB regen cost in the ledger. Update
   PLAN.md; write `docs/agents/sail-phase3-bootstrap.md` (differential testing — still
   essential: GO means "builds + type-checks", not "proven correct").

## Exit criteria

evm-asm builds against the **vendored, release-pinned, current-upstream** scoped model
(lean-sail v4 on v4.30.0-rc1), `dhsorens` removed from `lakefile.toml`/manifest; all 51
`*_sail_equiv` lemmas green; axiom hygiene preserved; provenance + PLAN updated.

## Housekeeping

- **Synced.** `feat/sail-zkvm-integration` is pushed (through `ba45cc4d`); local and
  `origin` agree. No manual push pending.
- The untracked `docs/agents/phaseN-bootstrap.md` + `rollout-complete.md` are unrelated
  steering-rollout leftovers — leave them.

## Bead tree (`bd` still not installed)

```
sail-zkvm-integration (parent)
├─ p1-regen-spike            ✅ DONE — GO, proven end-to-end (docs/agents/sail-regen-spike.md)
├─ p2-foundation-migration   ✅ CORE DONE — steps 1–4 (vendored, repointed, 51 lemmas green, full build 2984/2984). Residual 5–7 → sail-phase3-bootstrap.md
├─ p3-differential-testing   ← NEXT (essential — backend is experimental). P4 (sim theorem) also unblocked & parallel.
├─ p4-consolidated-sim-theorem
├─ p5-full-rv64im-coverage   (word-ops already in model; lemmas-only)
├─ p6-gates-and-ledger       (release-pin gate; portable regen; OCaml>=5.2 pin)
└─ p7-decode-tie
```
