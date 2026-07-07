# Sail-zkVM integration — Phase 4 bootstrap (consolidated sim theorem + gates)

**For:** the next session. **Supersedes** the ordering in `sail-phase3-bootstrap.md`
(whose "start with P4" was corrected by the review, and whose item-0 trust-hygiene is now
**done**). **Read `sail-adversarial-review.md` first** — it is the evidence base for why the
P4 exit criterion below is what it is.

## Verified ground truth (re-checked 2026-06-25, not just claimed)

- `lake build EvmAsm` = **2984/2984, exit 0**.
- **51** `*_sail_equiv` lemmas in `EvmAsm/Rv64/SailEquiv/`; **0** `sorry`/`admit`; **0**
  `native_decide`/`bv_decide` in proof sources.
- Build consumes the vendored, scoped RV64IM model `vendor/sail-riscv-zkvm-lean/` (lib
  `Out`, 113 `.lean` files); `dhsorens` gone from the build.
- **Axiom footprint is NOT uniform** (key correction): pure-ALU lemmas are 3-axiom clean
  `{propext, Classical.choice, Quot.sound}`; **memory lemmas additionally carry Sail
  platform axioms** `{plat_term_write, load_reservation, match_reservation,
  sys_enable_experimental_extensions}`. This is real and verified via `#print axioms`.

## Done last session (review + trust hygiene)

- `sail-adversarial-review.md` created (6 findings, evidence-backed).
- **F1** corrected: PROVENANCE note + P4 exit criterion no longer claim "3 classical only".
- **F2** resolved: `model_sha256 = 3a49ffa5…` is correct; recipe was underspecified, now
  pinned reproducibly (`cd vendor/sail-riscv-zkvm-lean && find . -name '*.lean' -not -path
  './.lake/*' | LC_ALL=C sort | xargs sha256sum | sha256sum`).
- **F4** fixed: `PROGRESS.md`, `scripts/progress-template.md`, `README.md`, `AGENTS.md`
  (toolchain → `v4.30.0-rc1`), `docs/riscv-zkvm-compliance.md` all repointed off dhsorens
  /`.lake/packages/Lean_RV64D` onto the vendored model.

---

## P4 — Consolidated simulation theorem (headline; pure Lean, ~1 session)

**Deliverable:** `EvmAsm/Rv64/SailEquiv/StepSim.lean`, one theorem subsuming the 51
scattered lemmas:

```lean
theorem step_execute_sail_sim
    (sRv : MachineState) (sSail : SailState) (hrel : StateRel sRv sSail)
    (i : Instr) (si : SailInstr) (h : toSailInstr? i = some si) :
    ∃ sSail',
      runSail (execute si) sSail = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv i) sSail' := by
  cases i <;> ...   -- per-constructor: discharge via the existing *_sail_equiv lemma
```

**The proof is mechanical — the glue is already definitional:**
- `SailInstr := instruction` (`InstrMap.lean:45`). `execute` (`Out/InstsEnd.lean:4363`) is a
  plain `match merge_var with | .RTYPE (rs2,rs1,rd,op) => execute_RTYPE rs2 rs1 rd op | …`.
  So after `cases i`, `toSailInstr? i = some si` pins `si` to a concrete constructor (e.g.
  `.RTYPE (…, rop.ADD)`), and `simp [execute]` (or `unfold execute`) reduces `execute si`
  to the exact `execute_RTYPE …` that `add_sail_equiv` is already stated over.
- The per-instruction lemmas (`add_sail_equiv` et al., `ALUProofs/Shift/Branch/Mem/MExt`)
  have **identical conclusion shape** to the goal — see `ALUProofs.lean:71` for the
  template. So each `cases` arm is: `simp [toSailInstr?, execute] at h ⊢; exact
  <lemma> sRv sSail hrel …` (modulo `regToRegidx`/`regToSailReg` massaging that the
  lemmas already encapsulate).

**Watch-outs (from the model review):**
- **PC agreement is uniform** (review §5.5): Sail uses explicit `nextPC`/`tick_pc`; the toy
  model bakes `PC+=4` into `execInstrBr`. The existing lemmas already carry this; the
  consolidated `cases` should need no per-arm PC special-casing — confirm.
- Memory/branch arms are where the platform axioms enter — expected, not a bug.

**Exit criterion (CORRECTED — do not use "3 classical only"):**
- builds clean as part of `lake build EvmAsm`.
- `#print axioms step_execute_sail_sim` ⊆ **{propext, Classical.choice, Quot.sound}** ∪
  **{plat_term_write, load_reservation, match_reservation,
  sys_enable_experimental_extensions}** — and nothing else (no `sorryAx`, no stray model
  axiom). Enumerate the platform axioms in a doc-comment justifying each as the model's
  host/LR-SC/experimental-extension trust boundary.
- **Axiom-check recipe (proven):** `lake env lean <scratch.lean>` where the scratch
  `import`s the SailEquiv modules and `#print axioms step_execute_sail_sim`. (Do NOT
  redirect stderr to /dev/null — the Lean guardrail hook blocks it.)

---

## P6 — Gates (promoted ahead of P3; pure-repo, closes the F3 gap)

**Why now:** there is currently **NO** CI gate for axioms or forbidden tactics
(`build.yml` runs only `check-file-size`/`check-unimported`/`check-no-warnings`/
`check-progress`). The bv_decide purge (290→0) and the axiom hygiene above can silently
regress. Three scripts, then wire into `.github/workflows/build.yml`:

1. **`scripts/check-forbidden-tactics.sh`** — grep-gate: fail if `native_decide`/`bv_decide`
   appears in `EvmAsm/**.lean` (proof sources). Mirrors the CLAUDE.md convention.
2. **`scripts/check-axioms.sh`** — `lake env lean` a generated scratch that `#print axioms`
   the public SailEquiv theorems (esp. `step_execute_sail_sim`); fail if any axiom is
   outside the allowlist `{3 classical} ∪ {4 platform}`. This is the machine-enforcement of
   F1.
3. **`scripts/check-sail-pin.sh`** — assert the resolved dep matches `PROVENANCE.toml
   [target]`: recompute `model_sha256` with the **exact pinned recipe** (now reproducible —
   `3a49ffa5…`), check `lakefile.toml` has the `vendor/` path require + lib `Out`, and that
   `dhsorens` is absent from `lakefile.toml`/`lake-manifest.json`.

**Fold in residuals:** F5 (the vendored model still ships ~60 softfloat `riscv_fXX` axioms
unused by RV64IM — add a coverage assertion that they are unreachable from the shipped
`cases`, or note them as out-of-scope-but-present); F6 (run `validate_config` on
`riscv64im_zicclsm.json`, record the Zicclsm "model misaligned (free via config)"
decision from review §4 into the design doc's open-questions section).

---

## P3 — Differential testing (essential, but blocked on toolchain — can't start cold)

The one track that needs the Sail toolchain (opam switch `sail5`, Sail 0.20.2, z3 4.15.3;
de-nix the z3 store path in `scripts/regen-sail-model.sh` first). Generate the **executable**
Lean variant (`--lean-executable`) and run it against the Sail C reference sim / `riscv-tests`
on RV64IM; wire as a CI job. This is what turns "builds + type-checks" into "passes the
reference conformance suite" — the headline trust mitigation (review §1). Do P4 + P6 first
(pure-repo); pick up P3 when the toolchain environment is available.

## Recommended order for the session

1. **P4** `StepSim.lean` — the single auditable "our step *is* RISC-V" object (~1 session).
2. **P6** the three gates — lock in everything proven so far (pure-repo, fast).
3. **P3** only if the Sail toolchain is stood up.

## Proven commands (copy-paste)

```bash
# Full build
lake build EvmAsm
# Axiom footprint of a lemma (scratch file imports SailEquiv modules + #print axioms)
lake env lean /path/to/AxCheck.lean        # NO 2>/dev/null — guardrail hook blocks it
# Reproducible model hash (must run from the vendor dir, C locale, exclude .lake)
cd vendor/sail-riscv-zkvm-lean && \
  find . -name '*.lean' -not -path './.lake/*' | LC_ALL=C sort | xargs sha256sum | sha256sum
```

## Bead tree

```
sail-zkvm-integration (parent)
├─ p1-regen-spike            ✅ DONE
├─ p2-foundation-migration   ✅ CORE DONE (vendored + repointed + 51 lemmas + 2984/2984)
├─ p2.5-trust-hygiene        ✅ DONE this session (review F1/F2/F4; PROVENANCE + docs fixed)
├─ p4-consolidated-sim-theorem  ← NEXT (pure Lean; corrected axiom allowlist)
├─ p6-gates-and-ledger       ← THEN (check-forbidden-tactics/-axioms/-sail-pin; closes F3)
├─ p3-differential-testing   (essential; blocked on Sail toolchain)
├─ p5-full-rv64im-coverage   (12 word-ops; lemmas-only; after P4)
└─ p7-decode-tie             (reuses execute sim)
```
