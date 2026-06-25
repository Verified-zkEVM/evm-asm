# Sail-zkVM integration — Phase 2 bootstrap (foundation migration)

**For:** the next session. **Goal of P2:** vendor the (now-proven) current-upstream
scoped RV64IM Lean model into evm-asm, build it in-project, drop the moving
`dhsorens` fork, and re-establish the 51 `*_sail_equiv` lemmas against it.

**Status (2026-06-25):** steps 1–2 DONE. The model is **vendored, git-pinned, and
builds 84/84 from its committed location** (commit `a2dedf448`). The next concrete
action is **step 3 (repoint the project off dhsorens)**, which immediately flows into
**step 4 (re-point the 51 lemmas)** — the real proof work. Start there.

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

3. **Repoint the project.** In `lakefile.toml`: drop the `Lean_RV64D` git require;
   add `require out from "vendor/sail-riscv-zkvm-lean"`. Update `lake-manifest.json`
   (let `lake` regenerate). In `StateRel.lean`: `import LeanRV64D` → `import Out`,
   `open LeanRV64D.Functions` → `open Out.Functions`. **This is also the step-1 test:**
   it's the first time lean-sail v4 + mathlib-`master` coexist in the *real* evm-asm
   build (the model itself doesn't pull mathlib, so risk is low but unverified). Get
   `StateRel.lean` + downstream non-proof code compiling first.
4. **Re-point the 51 `*_sail_equiv` lemmas** (the real proof work). Apply the namespace
   rename across the 6 files, then compiler-guided repair for the genuine renames
   (`bool_to_bit → bool_to_bits`, + whatever the diff surfaces). Target: all 51 green.
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

- **Push still pending.** The branch `feat/sail-zkvm-integration` has unpushed commits
  (`e445f8ac7` docs, `a2dedf448` vendor). Auto-mode denied `git push` last session —
  the user runs it: `git push origin feat/sail-zkvm-integration`.
- The untracked `docs/agents/phaseN-bootstrap.md` + `rollout-complete.md` are unrelated
  steering-rollout leftovers — leave them.

## Bead tree (`bd` still not installed)

```
sail-zkvm-integration (parent)
├─ p1-regen-spike            ✅ DONE — GO, proven end-to-end (docs/agents/sail-regen-spike.md)
├─ p2-foundation-migration   ← THIS PHASE. steps 1–2 ✅ (vendored + builds, a2dedf448); NEXT: step 3 → 4
├─ p3-differential-testing   (essential — backend is experimental)
├─ p4-consolidated-sim-theorem
├─ p5-full-rv64im-coverage   (word-ops already in model; lemmas-only)
├─ p6-gates-and-ledger       (release-pin gate; portable regen; OCaml>=5.2 pin)
└─ p7-decode-tie
```
