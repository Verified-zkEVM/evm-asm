# Design: Sail-anchored zkVM RISC-V semantics — import pipeline & toy-spec removal

**Status:** Draft / RFC — for review before any proof work begins.
**Author:** drafted in-session (2026-06-24), for @pirapira / Verified-zkEVM.
**Scope decision taken:** "Investigate & write design doc" (no proof code this session).
**Companion:** [`sail-zkvm-model-review.md`](sail-zkvm-model-review.md) — a four-way
deep review of the Sail model, the Lean export, and the Sail Lean backend.
Findings marked **[PLAN-IMPACT]** there have been folded back into this doc
(Zicclsm §2.1, backend trust §7, roadmap P5/P5b, ledger §6.1).

---

## 0. TL;DR

The EVM proofs today rest on a **hand-written RV64 transition function**
(`execInstr` / `execInstrBr`) plus a **magic decoder** (`CodeMem : Word →
Option Instr`). These are audited against the official Sail model by ~50
per-instruction `*_sail_equiv` lemmas in `EvmAsm/Rv64/SailEquiv/`. That audit is
real but it is *scattered* (no single theorem), it is *partial* (decode is not
tied to Sail at all), and the Sail dependency it audits against is the **full
RV64D model pinned to a moving `rev = "main"` of a fork** — the opposite of
reproducible.

This document proposes three coupled changes, in priority order:

1. **A pinned, scoped, reproducible import pipeline** that generates Lean
   semantics for *exactly* the zkVM target ISA — `riscv64im_zicclsm` — from the
   official `riscv/sail-riscv` model, with a checked-in config that *is* the
   legible compliance artifact.
2. **One top-level simulation theorem** that subsumes the 50 scattered lemmas,
   plus a **decode tie** so that "which instruction runs at a PC" is
   Sail-derived rather than a hand-written oracle. Together these turn the
   hand-written transition into a *proven projection* of Sail — "vibe-coded" no
   longer applies.
3. **A compliance ledger + drift fitness-functions** so an Ethereum client dev
   can read one table to see how every normative line of the standard maps to a
   kernel-checked artifact, and CI fails loudly the moment the model, the
   target, or the coverage drifts apart.

We **cannot** delete `MachineState`: the entire separation-logic / CPS / opcode
proof base (≈300 KB) is built on it. The goal is not to delete the substrate but
to stop *independently authoring its semantics* — to make the transition and the
decoder *derived from and proven against* Sail.

---

## 1. Goals (from the session brief)

The integration must be simultaneously:

- **Verifiable** — everything is a kernel-checked theorem against the official
  Sail RISC-V model; the trusted base stays the 3 classical axioms (no
  `native_decide`/`bv_decide`, per existing CI gates).
- **Auditable / legible** — an Ethereum client dev (not a Lean expert) can
  check compliance with the *exact* zkVM RISC-V standard by reading a small
  number of artifacts: the target config, a coverage list, and a
  requirement→theorem ledger.
- **Maintainable / drift-evident** — when the Sail model bumps, when the
  standard changes, or when coverage regresses, CI fails with a legible diff.
  This follows the project's established "architecture fitness function"
  philosophy (`scripts/check-*.sh`): promote a convention to an automated gate
  rather than to prose an agent can ignore.

---

## 2. The exact target: `riscv64im_zicclsm-unknown-none-elf`

Source of truth: `eth-act/zkvm-standards`, `standards/riscv-target/target.md`
(plus the sibling standards listed in §6). Normative content:

| Aspect | Requirement |
|---|---|
| **Target triple** | `riscv64im_zicclsm-unknown-none-elf` |
| **Base ISA** | RV64I (64-bit) |
| **Extensions** | **M** (mul/div), **Zicclsm** (misaligned load/store to main memory) |
| **XLEN** | 64 |
| **Endianness** | Little-endian |
| **Privilege** | **Machine (M) mode only** |
| **Excluded** | Compressed (C); Float (F/D — soft-float ABI instead); any syscall/env support |
| **Memory** | Flat, no MMU, no paging |
| **Linking** | Static ELF |
| **ABI** | LP64 (soft-float variant) |

Sibling standards that constrain semantics and must be in the ledger:

- `instruction-address-misaligned-exception-semantics/` — exception behaviour for
  misaligned **instruction** addresses (distinct from Zicclsm data accesses).
- `memory-layout-restrictions/`, `memory-safety-guard-regions/` — address-space
  constraints.
- `standard-termination-semantics/` — how a guest halts (maps to our ECALL/COMMIT
  handling).
- `io-interface/` + `c-interface-accelerators/` — the ECALL surface (already
  documented in `docs/zkvm-host-io-interface.md` / `docs/zkvm-accelerators-interface.md`).

**This is a ~50-instruction ISA.** RV64I base + 13 M-extension ops + the
misaligned-access behaviour of the existing load/store ops. That is the entire
compliance surface. Everything else in the Sail model (V, F/D, C, Zicsr beyond
what M-mode needs, Vmem/paging, Zb*, Zvk*) is **out of scope** and should not be
in the trusted import.

### 2.1 ⚠️ Latent divergence to resolve: Zicclsm vs. aligned-only

The standard **mandates Zicclsm** — misaligned loads/stores to main memory must
be *supported* (defined, non-trapping). But today:

- `EvmAsm/Rv64/Basic.lean` defines `isValidDwordAccess = isValidMemAddr &&
  isAligned8` etc.; an unaligned `LD`/`SD`/`LW` has **no semantics** (evaluates
  to a stuck/`false` access).
- `AGENTS.md` codifies "All memory accesses must be aligned" as a hard rule for
  new snippets.

So the verified subset is *stricter* than the standard.

**UPDATE (post-review — see [`sail-zkvm-model-review.md`](sail-zkvm-model-review.md) §4):**
the deep review flips this. **Zicclsm is a configuration property, not new
semantics, and the misaligned-access behaviour already exists in the Sail
model** (`sys/vmem_utils.sail::split_misaligned`, gated by
`memory.misaligned.exceptions.load_store`, with `postlude/validate_config.sail`
enforcing no-AccessFault under Zicclsm). So:

- **(a) — model the full Zicclsm semantics: now essentially free.** Set
  `extensions.Zicclsm.supported = true` and
  `memory.misaligned.exceptions.load_store = {"None": null}` in the import
  config; the reference model then *defines* misaligned access. **This is the
  recommendation.** No compliance caveat is needed — the reference covers the
  full standard, and our verified guest may still keep emitting only aligned
  accesses as an internal discipline.
- **(b) — audited aligned-only assumption** (a fitness-function scanning emitted
  code for unaligned accesses; the standard already asks zkVMs to count them):
  retained only as a fallback if (a)'s config path hits a snag. Originally
  recommended; **superseded by (a)** because we no longer have to author the
  semantics we assumed (b) was avoiding.

Either way it is a *named* line in the ledger, not silent.

---

## 3. Current state — precise diagnosis

Three layers, two gaps, one provenance problem.

### 3.1 The three layers

1. **Substrate** — `MachineState` (`Rv64/Basic.lean`): registers as a function,
   memory, PC, public/private I/O. **The whole proof base lives here**:
   `SepLogic.lean` (139 KB), `CPSSpec.lean`, `GenericSpecs`, every `Evm64/`
   opcode. Not deletable.

2. **Hand-written transition** — `execInstr` (`Instructions.lean`),
   `execInstrBr` + `step` (`Execution.lean`), and the decoder
   `CodeMem : Word → Option Instr`. **This is the "toy/vibe-coded spec."**

3. **The Sail tie** — `Rv64/SailEquiv/`: `StateRel` (register + memory
   abstraction relation), `toSailInstr?` / `fromSailInstr?` (AST bridge, with
   round-trip lemma), and ~50 per-instruction lemmas of the shape

   ```
   StateRel sRv sSail →
     ∃ sSail', runSail (execute_<class> …) sSail = some (RETIRE_SUCCESS, sSail')
             ∧ StateRel (execInstrBr sRv i) sSail'
   ```

### 3.2 Gap 1 — no single statement

The 50 lemmas are never quantified into one `∀ i : Instr, …` theorem. There is
no object an auditor can point at and say "this is the proof that our step
function is RISC-V." The audit exists but is not *legible as one fact*.

### 3.3 Gap 2 — decode is entirely untied

`step` obtains its instruction from `CodeMem`, a hand-supplied oracle. Sail's
`run_hart_active` (`Step.lean`) actually `ext_decode`s the 32-bit word read from
memory. **Nothing connects `CodeMem` to Sail's decoder.** So even with all 50
execute-lemmas, the claim "the bytes in memory at PC decode to instruction `i`"
is unverified against Sail. For a zkVM — where the prover commits to *bytes* —
this is the more important half.

### 3.4 Provenance problem — the dependency is a moving, over-scoped fork

`lakefile.toml`:

```toml
[[require]]
name = "Lean_RV64D"
git = "https://github.com/dhsorens/sail-riscv-lean"
rev = "main"                      # ← moving target, not a commit
```

- **Moving `rev`.** `main` of a personal fork. `lake-manifest.json` records
  whatever it last resolved; a fresh `lake update` can silently change the
  semantics the entire project is verified against.
- **A fork, by the fork author's own README:** "neither executable nor polished
  in any way… work-in-progress."
- **Massively over-scoped.** The export is the full RV64D model: **153 Lean
  files**, 72 k-line `InstsEnd.lean`, vector/FP/CSR/paging/crypto. The
  compliance target needs ~50 instructions. ~95% of the trusted import is ISA
  surface we neither target nor want in the audit.

---

## 4. Design Part A — the import pipeline

**Objective:** a pinned, reproducible, *scoped-to-target* Lean model generated
from the official upstream, where the configuration that selects the ISA *is*
the human-readable compliance artifact.

### 4.1 The upstream pipeline (how Lean is generated)

```
riscv/sail-riscv  ──(JSON config selects extensions)──▶  Sail model
        │                                                     │
        │  rems-project/sail (Lean backend)                   │
        ▼                                                     ▼
   cmake --build --target generated_lean_rv64d  ───────▶  Lean source
                                                     (rems-project/lean-sail runtime)
```

Facts established this session:

- **Sail has a first-class module system, and sail-riscv uses it.** The model is
  `model/riscv.sail_project` — `module { requires …, files … }` blocks with
  explicit dependency edges: `prelude`, `core` (≈RV64I), `I` (`I_types`/
  `I_insts`), `M`, `A` (`Zaamo`/`Zalrsc`), `B` (`Zba`/`Zbb`/`Zbc`/`Zbs`), `C`,
  `FD`, `V`, `Zicsr`, `vector_crypto`, … e.g. `M { requires core; M_types {…};
  M_insts { requires sys, I, M_types, … } }`. **Selective inclusion is a
  built-in Sail feature, not a hack.**
- **The Lean cmake target already supports module subsetting.** `model/
  CMakeLists.txt` defines `set(SAIL_MODULES "--all-modules" CACHE STRING …)` and
  passes `${SAIL_MODULES}` into the `generated_lean_${arch}` Sail invocation. It
  is a *cache variable* — overridable with `-DSAIL_MODULES="prelude core I M …"`.
  The current full-RV64D export simply leaves the default `--all-modules`.
- Extension selection also has a **runtime JSON config** (`--config`,
  `--print-default-config`, schema-validated) for tunables (e.g. misaligned-access
  enablement) that aren't a code-module choice — relevant to Zicclsm (§2.1).
- The Lean backend uses the `lean-sail` runtime (`rev = "v3"`); the executable
  variant is `generated_lean_executable_${arch}`.
- The current fork bypasses all of this reproducibility by shipping a
  pre-generated, `--all-modules` (full-ISA) Lean tree pinned to a moving branch.

### 4.2 Proposed structure

Introduce a small **vendored, pinned, regenerable** package — call it
`sail-riscv-zkvm-lean` (could live in-tree under `vendor/` or as a pinned dep we
control), produced by:

1. **Pin three upstream commits**, recorded in a single provenance manifest
   (`sail-import/PROVENANCE.toml`): `riscv/sail-riscv` commit, `rems-project/sail`
   commit (Lean backend), `rems-project/lean-sail` commit. No moving `rev`s.
2. **Check in the module selection + runtime config.** Two artifacts:
   - `sail-import/modules.txt` — the explicit `SAIL_MODULES` list (the
     transitive `requires`-closure of `prelude core I M` plus whatever Zicclsm
     needs). **This is the primary legibility artifact** (§6): "we import
     exactly these Sail modules" is something a client dev reads directly off
     `riscv.sail_project`, far more legible than a hand-trimmed source tree.
   - `sail-import/riscv64im_zicclsm.json` — runtime config (from
     `--print-default-config`) for M-mode, little-endian, misaligned-access
     enablement (§2.1) — the tunables that aren't a module choice.
3. **A regeneration script** `scripts/regen-sail-model.sh` that runs the upstream
   pipeline with the pinned commits + config and emits the Lean tree.
4. **Vendor the generated Lean** (checked in), so the normal `lake build` does
   *not* require an OCaml/Sail toolchain — only regeneration/CI does.

### 4.3 Scoping: full model vs. trimmed model

Two sub-options for "scoped to target" — and the module system (§4.1) changes
the balance decisively in favour of trimming:

- **A1 — Trim at generation (preferred).** Drive `generated_lean_${arch}` with
  `-DSAIL_MODULES="<closure of prelude core I M …>"` so the Lean tree *literally
  contains only the target ISA*. This is no longer a deep spike: Sail's module
  system + the overridable `SAIL_MODULES` cache var support it directly. The
  residual risk is narrow config-engineering, not research:
  1. compute the correct minimal `requires`-closure for `riscv64im_zicclsm`
     (note `core` already drags in `A_types`, `Zicbop_types`, `PM_types` —
     *type* deps, far smaller than the *instruction* modules);
  2. confirm the Lean backend emits a well-typed subset (no dangling refs) for
     that closure;
  3. decide whether to define a new `${arch}` (e.g. `rv64im_zicclsm`) or reuse
     `rv64d` with a module override.
- **A2 — Fence by gate.** A fitness-function asserting our proofs/`toSailInstr?`/
  decode tie reference *only* in-scope `execute_*` / `instruction` constructors.

Recommendation: **A1 is the target, and the gate from A2 is its completeness
check — keep both.** Pursue A1 (a ~1-spike config task given the module system),
and ship the A2 scope-gate alongside so CI proves the trim is complete and stays
complete. If the A1 closure spike hits an unexpected snag, A2 lets the
toy-spec-removal work (Part B) proceed against the full model meanwhile, since
Part B is independent of how the model was scoped.

### 4.4 Migration off the fork

Switch the dependency from `dhsorens/sail-riscv-lean @ main` to either upstream
`opencompl/sail-riscv-lean` at a **pinned commit**, or our regenerated package.
The README already names "switching back to upstream once toolchains converge"
as the goal; the pinned-commit move is a prerequisite for any audit story and
should happen regardless of A1/A2.

---

## 5. Design Part B — removing the toy spec

Reframing: we keep `MachineState` (substrate) but make the **transition** and
the **decoder** derived-and-proven from Sail. Four levels, each independently
shippable; B1+B2 together are the core deliverable.

### B0 (prerequisite) — extend the model to the exact target surface

Audit `toSailInstr?` coverage against the §2 instruction list. The bridge today
covers RV64IM + loads/stores + system. Confirm it is exactly the target set
(no more — e.g. it should *not* bridge C/F/D; no less — every target instruction
present). Resolve the Zicclsm question (§2.1).

### B1 — one consolidated simulation theorem  *(cheap; ~1 session)*

Prove a single theorem dispatching to the existing 50 lemmas:

```lean
theorem step_execute_sail_sim
    (sRv : MachineState) (sSail : SailState) (i : Instr) (si : SailInstr)
    (hrel : StateRel sRv sSail) (hpc : pcAgrees sRv sSail)
    (hi : toSailInstr? i = some si) :
    ∃ sSail',
      runSail (execute si) sSail = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv i) sSail'
```

This is the legible "our step function is RISC-V" object. Proof is `cases i` +
the per-instruction lemmas (already proven). Low risk, high legibility payoff.
Also add the AUIPC/branch PC-agreement bookkeeping uniformly (currently an extra
hypothesis on some lemmas).

### B2 — tie the decoder to Sail  *(substantial; the real gap)*

Connect `CodeMem`/fetch to Sail's `ext_decode`. Concretely: a theorem that if
the 4 bytes at PC in `MachineState` memory equal a 32-bit word `w`, and
`toSailInstr? i = some si`, then Sail's `ext_decode w = si` and our
`CodeMem`-supplied `i` matches. The honest end-state is

```
bytesAt sRv pc = w  →  decode-via-Sail w = some i  →  step sRv = some (execInstrBr sRv i)
```

so that `step` is justified end-to-end (fetch → decode → execute) against Sail,
with no oracle. This is genuine RISC-V binary-decode work but is the half that
matters most for a zkVM (the prover commits to bytes, not to an `Instr` AST).

### B3 — definitional derivation (optional hardening)

Define `execInstrFromSail sRv i := project (runSail (execute (toSailInstr? i))
(embed sRv))` via an `embed : MachineState → SailState` / `project` pair, and
prove `execInstrFromSail = execInstrBr` (B1 *is* this proof, restated as an
equation). Then the *defining reference* of the transition is Sail; `execInstrBr`
survives only as a compute-friendly, proven-equal view. Strongest "no
independently-authored semantics" story. Defer until B1/B2 land — the payoff is
mostly rhetorical once B1+B2 exist.

### B-not — full substrate migration (rejected)

Rebuilding `SepLogic`/`CPSSpec`/opcodes on Sail's `ExtHashMap`-based
`SequentialState` would delete the toy model entirely but is a ground-up rewrite
of the verified core. Out of scope; not recommended.

---

## 6. Design Part C — legibility, audit, drift (the maintainability layer)

This is where the "Ethereum client dev can check compliance" goal is met. Two
instruments.

### 6.1 The compliance ledger

A single (eventually CI-regenerated) document —
[`docs/riscv-zkvm-compliance.md`](riscv-zkvm-compliance.md), **drafted v1 now** —
with one row per normative requirement of the standard (and siblings), each
mapping to the artifact that discharges it and the gate that guards it. The v1
already carries the full instruction-by-instruction inventory and surfaced the
RV64 word-op coverage gap:

| Requirement (standard §) | Lean artifact | Drift gate |
|---|---|---|
| RV64I base, XLEN=64 | Sail config + `step_execute_sail_sim` | `check-sail-pin.sh`, coverage gate |
| M extension (13 ops) | `*_sail_equiv` (MExtProofs) + sim theorem | coverage gate |
| Zicclsm (misaligned LS) | import config (`Zicclsm=true`, misaligned=`None`); semantics from `split_misaligned` (§2.1 opt a) | `check-sail-config.sh` |
| M-mode only / no C/F/D | scope gate: no out-of-target constructors referenced | `check-isa-scope.sh` |
| Termination + ECALL host interface (host-call abstraction vs Sail trap-to-M — review §5.4) | ECALL/COMMIT handler specs; **named divergence**, no `ecall_sail_equiv` by design | existing conformance floor |
| Decode = bytes→instr | B2 decode tie (+ confirm `bv_decide`-free, review §5.6) | coverage gate |
| **Sail→Lean backend faithful** (experimental; trust item 2) | differential test vs Sail C sim / `riscv-tests` (P5b) | `check-sail-pin.sh` + diff-test CI |

The intent: an auditor reads *this table top to bottom*, follows each link to a
named kernel-checked theorem or a named assumption, and is done — no grep
spelunking. This mirrors `docs/notable-specs.md` but organized by *standard
requirement* rather than by opcode.

### 6.2 Fitness functions (new `scripts/check-*.sh`, in the established style)

Promote each invariant to an automated gate (blocking unless noted):

- **`check-sail-pin.sh`** — the three upstream commits + the config file hash in
  `PROVENANCE.toml` match the resolved dependency; fails on any moving-`rev`
  drift. *(Directly fixes the §3.4 problem.)*
- **`check-isa-scope.sh`** — `toSailInstr?` / the decode tie reference **only**
  in-target `instruction` constructors; flags accidental import of C/F/D/V/CSR
  surface. Enforces "scoped to target" even under import option A2.
- **`check-isa-coverage.sh`** — the set of instructions our sim theorem covers
  equals the standard's instruction list, regenerated from a checked-in list;
  fails if the standard gains/loses an instruction or our coverage regresses.
  *(This is the "evident if something breaks" gate the brief asks for.)*
- **`check-unaligned-access.sh`** (advisory→blocking) — scans emitted codegen for
  unaligned load/stores; backs the §2.1(b) assumption. The standard already asks
  zkVMs to count unaligned accesses; we gate on zero.
- **Ledger regen check** — `docs/riscv-zkvm-compliance.md` regenerates
  identically from the registry (same pattern as `check-progress.sh` /
  `check-drift.sh`).

All seeded green on the current tree (the steering review's rule: a gate that
red-lights day one is friction, not signal).

---

## 7. Trust boundary after this work

What remains *assumed* (and must be stated in the ledger), smallest possible:

1. **Sail itself faithfully encodes RISC-V** — the Sail model is the reference;
   we don't prove Sail against silicon. (Unchanged; this is the accepted anchor.)
2. **🔴 The experimental Sail→Lean backend is faithful** — *the headline trust
   item.* The review (`sail-zkvm-model-review.md` §1) found the backend is
   labelled "HIGHLY EXPERIMENTAL," carries **no soundness/faithfulness claim**,
   and is a translation tool, not a verified transformation. It does **fail
   loud** (`failwith`) in its known-unsupported cases rather than mistranslate
   silently — mild comfort. **Active mitigation required, not just pinning:**
   generate the *executable* Lean variant and **differential-test it against the
   Sail C reference simulator / `riscv-tests` on the target ISA subset**, so the
   generated artifact passes the same conformance suite as the reference even
   though the translator is unverified. Keeping the imported subset small (§4.3)
   minimizes the backend surface exercised.
3. **The Zicclsm config is set correctly** (§2.1 option (a)) — a config-review
   item, no longer a semantic assumption.
4. **The 3 classical axioms** — unchanged; `native_decide`/`bv_decide` stay
   forbidden and CI-gated. *Watch:* the generated decoder must be confirmed
   `bv_decide`-free (the `match_bv` fallback, review §5.6).

Everything else — transition correctness, decode correctness, ISA scope, ISA
coverage, dependency provenance — becomes a kernel theorem or an automated gate.

---

## 8. Phased roadmap & effort

| Phase | Deliverable | Effort | Risk |
|---|---|---|---|
| **P0** | Pin the dependency to a commit; `PROVENANCE.toml` + `check-sail-pin.sh` | ~½ session | low |
| **P1** | B1 consolidated `step_execute_sail_sim` + B0 coverage audit | ~1 session | low |
| **P2** | `check-isa-scope.sh` + `check-isa-coverage.sh` + compliance ledger v1 | ~1 session | low |
| **P3** | §2.1 Zicclsm resolution (assumption + `check-unaligned-access.sh`) | ~1 session | low |
| **P4** | B2 decode tie (fetch→`ext_decode`→execute end-to-end) | several sessions | medium |
| **P5** | Import pipeline A1 (scoped generation via `SAIL_MODULES` closure, ~14 modules; review §3) + regen script + `PROVENANCE.toml` + diff CI | config spike + ~1–2 sessions | low–medium (closure well-typed by construction; risks are `sys` state residue §3 + lean4/lib version skew §1.1) |
| **P5b** | **Differential testing** of the generated *executable* Lean model vs. Sail C sim / `riscv-tests` on the RV64IM subset — the active mitigation for the experimental backend (trust item 2) | ~1–2 sessions | medium |
| **P6** | B3 definitional derivation (optional) | ~1–2 sessions | low |

Two spike sub-items folded into P5 from the review: **(i)** measure the actual
generated `Register` enum after trimming and decide whether the `sys`-pulled
vector/CSR type residue is acceptable; **(ii)** confirm the generated decoder for
the subset is `bv_decide`-free (`match_bv` fallback, review §5.6) so the
forbidden-tactic gate does not trip.

Recommended order: **P0 → P1 → P2 → P3 → P4 → P5**, with P6 optional. P0–P3 are
cheap, reuse existing proofs, and deliver the bulk of the *legibility/audit*
value. P4 closes the real semantic gap. P5 is the deepest but is decoupled and
can proceed in parallel once P0 pins provenance.

---

## 9. Decisions needed from maintainers

1. **Import scope A1 vs A2** (§4.3) — given Sail's module system makes trimming
   first-class (`SAIL_MODULES` override), pursue A1 (scoped generation) as the
   target with the A2 scope-gate as its completeness check?
   *(Recommendation: A1 + A2-gate together.)*
2. **Zicclsm** (§2.1) — model misaligned semantics (a), or audited
   aligned-only assumption + scan (b)? *(Recommendation: b now, a later.)*
3. **Where the regenerated model lives** — in-tree `vendor/`, or a pinned repo we
   control vs. upstream `opencompl` at a pinned commit? *(Recommendation: pinned
   upstream commit short-term; our regenerable package long-term.)*
4. **Sequencing** — is P4 (decode tie) in scope soon, or is the
   provenance+consolidation+ledger bundle (P0–P3) the near-term target?

---

## 10. References

- zkVM RISC-V target: `eth-act/zkvm-standards` `standards/riscv-target/target.md`
  (`riscv64im_zicclsm-unknown-none-elf`).
- Sibling standards: `instruction-address-misaligned-exception-semantics/`,
  `memory-layout-restrictions/`, `standard-termination-semantics/`,
  `io-interface/`, `c-interface-accelerators/`.
- Official Sail RISC-V model: https://github.com/riscv/sail-riscv (JSON-config
  extension selection; `generated_lean_rv64d` cmake target).
- Sail (Lean backend): https://github.com/rems-project/sail ;
  `lean-sail` runtime: https://github.com/rems-project/lean-sail (`rev v3`).
- Current export (full RV64D, to be replaced/pinned):
  https://github.com/dhsorens/sail-riscv-lean ;
  upstream https://github.com/opencompl/sail-riscv-lean.
- In-repo: `EvmAsm/Rv64/SailEquiv/` (StateRel, InstrMap, `*Proofs`),
  `EvmAsm/Rv64/{Basic,Instructions,Execution}.lean`,
  `AGENTS.md` ("All memory accesses must be aligned"),
  `docs/agent-progress-steering-review.md` (fitness-function philosophy).
</content>
</invoke>
