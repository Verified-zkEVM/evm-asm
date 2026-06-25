# Sail-zkVM integration — Phase 2 bootstrap (foundation migration)

**For:** the next session. **Goal of P2:** vendor the (now-proven) current-upstream
scoped RV64IM Lean model into evm-asm, build it in-project, drop the moving
`dhsorens` fork, and re-establish the 51 `*_sail_equiv` lemmas against it. P1 is
done — verdict **🟢 GO, proven end-to-end** (generation + a patch-free 84/84 `lake
build` of the matched pair). This bootstrap reflects what's PROVEN vs. what REMAINS.

> Read first: `docs/agents/sail-regen-spike.md` (validated report — note the two
> hard requirements: OCaml ≥5.2, and all three `--lean-non-beq-type`). Then
> `sail-import/PROVENANCE.toml [target]` and `scripts/regen-sail-model.sh` (the
> validated, runnable recipe).

## Proven foundation (don't re-litigate)

- **Toolchain stack:** Sail **0.20.2** (opam, built on **OCaml ≥5.2** — 4.14.2
  stack-overflows, sail#1674) + sail-riscv release tag **`2026-06-22-b5a2182`** +
  external **lean-sail v4** (`79b4d08`). **Project stays on lean4 v4.30.0-rc1** — no
  bump (lean-sail v4 builds on it; its declared v4.29.0 is just CI scaffolding).
- **Generation works:** `scripts/regen-sail-model.sh --run <dir>` → 113 files,
  ~9–13 min / ~7 GB. Decode is `bv_decide`-free. Word-ops present (P5 = lemmas-only).
- **Matched pair builds patch-free:** that model + lean-sail v4 on v4.30.0-rc1 →
  `lake build` 84/84 jobs, exit 0, incl. `InstsEnd`/`DecodeExt`/`Step`/`Model`.
- A working scratch build lives at `…/scratchpad/out_v2/out` (model) wired to
  `…/scratchpad/lean-sail` (v4) — reference it when stuck.

## Remaining work (ordered)

1. **Project integration (only remaining unknown).** Build the model *inside*
   evm-asm — lean-sail v4 coexisting with the project's mathlib-`master` stack in one
   `lake` build. Lower risk (lean-sail doesn't pull mathlib) but unverified. Do this
   on a throwaway lakefile edit first to confirm before vendoring.
2. **Vendor** the regenerated model under `vendor/sail-riscv-zkvm-lean/`. Set its
   `lean-toolchain` to the project's v4.30.0-rc1 and the lakefile `require Sail` to
   lean-sail v4 (discard the generator's emitted v4.29.0/git scaffolding). Record the
   regenerated-model hash + `config_sha256` in `PROVENANCE.toml`.
3. **Repoint the project** `lakefile.toml`/`lake-manifest.json` off
   `dhsorens/sail-riscv-lean` to the vendored model + lean-sail v4; drop `rev=main`.
4. **Re-point the 51 `*_sail_equiv` lemmas.** Known rename: `bool_to_bit →
   bool_to_bits` (Prelude), hit by `ALUProofs` SLT/SLTU/SLTI. First step: a full
   `diff` of the regenerated model vs the old vendored `Lean_RV64D` to enumerate every
   rename; then compiler-guided repair until all 51 are green. ← the real proof work.
5. **Config:** regenerate/revalidate `riscv64im_zicclsm.json` against the *tag's*
   schema (it changed since 1760ee2) and tighten per spec — single flat RAM region;
   justify the kept extensions (Zicntr/Zihpm/Zifencei) against the zkVM standard;
   actually exercise `validate_config` (P1 only confirmed it *generates*).
6. **Scoping decision (open).** Scoping gives 163 vs 178 registers and did NOT reduce
   generation memory — decide scoped-generation vs. full-model + a coverage/scope
   gate on merit, and record it.
7. **Hygiene + gates:** axiom hygiene unchanged (0 custom axioms, `[[bv-decide-purge]]`);
   no forbidden tactic in vendored code (the runtime's lone `try bv_decide` BEq macro
   is pre-existing); de-`nix` the z3 path in the regen recipe; pin release tags; note
   the 9-min/7-GB regen cost in the compliance ledger. Update PLAN.md; write
   `docs/agents/sail-phase3-bootstrap.md` (differential testing — still essential: the
   backend is experimental; GO means "builds + type-checks", not "proven correct").

## Exit criteria

evm-asm builds against the **vendored, release-pinned, current-upstream** scoped
model (lean-sail v4 on the unchanged v4.30.0-rc1), `dhsorens` removed; all 51
`*_sail_equiv` lemmas green; axiom hygiene preserved; provenance + PLAN updated.

## Bead tree (`bd` still not installed)

```
sail-zkvm-integration (parent)
├─ p1-regen-spike            ✅ DONE — GO, proven end-to-end (docs/agents/sail-regen-spike.md)
├─ p2-foundation-migration   ← THIS PHASE (only open unknown: in-project integration)
├─ p3-differential-testing   (essential — backend is experimental)
├─ p4-consolidated-sim-theorem
├─ p5-full-rv64im-coverage   (word-ops already in model; lemmas-only)
├─ p6-gates-and-ledger       (release-pin gate; portable regen; OCaml>=5.2 pin)
└─ p7-decode-tie
```
