# Review: the Sail RISC-V model, the Lean export, and the import surface

**Status:** Findings report (2026-06-24). Companion to
[`sail-zkvm-integration-design.md`](sail-zkvm-integration-design.md). Produced by
a four-way deep review of: (1) the generated Lean model we consume
(`.lake/packages/Lean_RV64D`), (2) the `lean-sail` runtime
(`.lake/packages/Sail`), (3) the upstream `riscv/sail-riscv` model source, and
(4) the Sail compiler's module system, config system, and **Lean backend**.

This document records *what is actually true* about the artifacts, with
`file:line` citations, so the integration plan rests on verified facts rather
than assumptions. Five findings change the plan; they are called out as
**[PLAN-IMPACT]**.

---

## 1. The trust anchor is "Sail **+ an experimental, unverified Sail→Lean backend**" — not "Sail" **[PLAN-IMPACT]**

This is the single most important finding for the audit story.

- The Sail→Lean backend is labelled **"HIGHLY EXPERIMENTAL"** in Sail's own
  CHANGELOG (v0.19, carried unchanged through v0.20.2): *"It is currently highly
  experimental, and will likely not compile all Sail programs."*
- There is **no soundness, verification, or faithfulness claim** anywhere in the
  backend (`src/sail_lean_backend/{sail_plugin_lean.ml, pretty_print_lean.ml}`).
  It is a translation tool, not a verified transformation.
- It has **hard limitations that `failwith` (abort) rather than mistranslate**:
  `when`-clauses in patterns outside `matchbv` (`pretty_print_lean.ml:728`),
  complex lvalue assignments (`:1023`), several `Nexp`/type/expression forms
  (`:242,:318,:1052,:1307`). The *reassuring* corollary: in its known failure
  modes the backend **stops** rather than emit silently-wrong Lean.

**Implication.** Our existing design-doc §7 listed "the Sail→Lean backend is
faithful" as a mitigated assumption — correct, but it must be **elevated to a
first-class, prominently-stated trust item**, and it needs an active mitigation
beyond pinning:

> **Recommended mitigation — differential testing of the *generated artifact*.**
> Even though the *translator* is unverified, the *output* can be validated
> behaviourally: generate the **executable** Lean variant
> (`--lean-executable`, the `generated_lean_executable_${arch}` target) and run
> it against the Sail C simulator (and/or the official `riscv-tests` /
> riscv-arch-test vectors) on the target ISA. This turns "trust the translator"
> into "the generated model passes the same conformance suite as the reference
> C model on our ISA subset." Keeping the imported subset **small** (§3) also
> minimizes the backend surface exercised, hence the mistranslation surface.

### 1.1 Version skew to resolve **[PLAN-IMPACT]**

The backend hardcodes its target toolchain (`sail_plugin_lean.ml:97-100`):

```
lean_version  = "lean4:v4.29.0"
mathlib_version = "v4.29.0"
lib_default_rev = "v4"     # lean-sail support library
```

But the project currently consumes `lean-sail` **rev v3** (per
`lake-manifest.json`) via the `dhsorens` fork, on toolchain **`lean4:v4.30.0-rc1`**
(verified from `lean-toolchain` — note the stale CLAUDE.md/AGENTS.md "4.28"
references are wrong). So the project is **ahead** of the backend's hardcoded
v4.29.0 target. Regenerating from current upstream Sail would emit **v4.29.0 /
lean-sail v4** output — i.e. *older* than the project. The migration is therefore
a **reconciliation**, not a simple forward bump: pick a Sail commit + lean-sail
rev whose generated Lean is compatible with v4.30.0-rc1, or align the project
toolchain to the backend target. This is precisely the kind of skew the
`dhsorens` fork was created to absorb. The pipeline plan must treat "which Sail /
lean-sail / toolchain triple we pin to" as an explicit, recorded decision (the
`PROVENANCE.toml` of design-doc §4.2).

---

## 2. The module system makes scoped generation real and well-typed **[PLAN-IMPACT, positive]**

Confirmed against both the model and the compiler:

- `.sail_project` modules declare `requires` edges; Sail computes the
  **transitive closure** of a chosen root set via a module graph
  (`src/lib/project.ml:642-644` `required_modules`, `ModGraph.prune`), loads them
  in topological order, detects cycles (`:650-666`), and **enforces that a module
  can only reference definitions from modules it `requires`**
  (`doc/asciidoc/modules.adoc:4-7`). So **a closure-selected subset is guaranteed
  well-typed with no dangling references** — A1 (trim-at-generation) is sound by
  construction, not a gamble.
- Module selection is `--all-modules` (default) vs. an explicit module list
  (`src/lib/frontend.ml:425-435`, `src/bin/sail.ml`). The sail-riscv cmake
  threads this through `SAIL_MODULES` into the Lean target.

**This confirms and strengthens the design-doc §4.3 recommendation: pursue A1.**

---

## 3. The exact RV64IM closure — ~14 modules / ~77 files (down from 153) **[PLAN-IMPACT]**

Computed from `model/riscv.sail_project`:

```
prelude, core, exceptions, pmp, sys,
I_types, I_insts, M_types, M_insts, postlude
  + core's unconditional TYPE deps: A_types, Zicbop_types, Zicbom_types, PM_types
```

Excluded entirely (no instructions imported): **C/Zca/Zcb, F/D/Zfh, V + vector_crypto,
B (Zba/Zbb/Zbc/Zbs), A instructions (Zaamo/Zalrsc), K/crypto, H (hypervisor),
S/U privilege beyond M, most Z* utility extensions.**

⚠️ **Caveat — `sys` is heavyweight.** `sys` itself
`requires V_core, Smcntrpmf, Zicfilp_regs, A_types, Stateen, Zicbop_types,
PM_utils`. So module-trimming removes every out-of-scope *instruction*, but `sys`
still drags in some vector/CSR **register-type** modules. Net effect:

- **Instruction surface:** shrinks to exactly RV64I + M (the target). ✅
- **State vector:** shrinks a lot, **but not to a pristine 50-instruction
  machine** — `V_core` etc. via `sys` may keep some register/type baggage. The
  A1 spike must measure the actual generated `Register` enum and decide whether
  the residue is acceptable or warrants an upstream `sys` refactor.

This refines the design doc's "scoping shrinks the state vector twice" claim:
true for instructions and most state, with a `sys`-shaped asterisk.

---

## 4. Zicclsm is configuration, and the semantics already exist **[PLAN-IMPACT — flips §2.1]**

Zicclsm has **no instructions and no decode** — it is a config/platform property
(`model/core/extensions.sail:265-268`: `config extensions.Zicclsm.supported`).
The misaligned load/store *behaviour* is already in the model:

- `model/sys/vmem_utils.sail:56` `split_misaligned` splits a misaligned access
  into aligned chunks or byte-by-byte, governed by config knobs
  `memory.misaligned.{byte_by_byte, order_decreasing, allowed_within_exp}`
  (`:28,:34,:51`).
- `model/sys/mem.sail:89-94` decides trap vs. allow from
  `memory.misaligned.exceptions.{load_store,vector}`
  (`core/platform_config.sail:74-87`).
- `model/postlude/validate_config.sail:543-550` **enforces** that with Zicclsm
  enabled, misaligned scalar/vector accesses must be `None` or
  `AlignmentException` — never `AccessFault`.

**[PLAN-IMPACT]** This **flips the §2.1 recommendation.** Full Zicclsm compliance
is **option (a) — model the misaligned semantics — and it is essentially free**:
set `extensions.Zicclsm.supported = true` and
`memory.misaligned.exceptions.load_store = {"None": null}` in the config. The
Sail model then *defines* misaligned access (via `split_misaligned`); we are no
longer choosing between "model it" and "assume it away." The earlier audited
aligned-only assumption (b) was a workaround for semantics we wrongly assumed we
would have to author. (Note: this *also* means our verified guest is free to keep
emitting only aligned accesses as a discipline; the point is the **reference**
now covers misaligned, so there is no compliance gap to caveat.)

Relevant config keys (`config/config.json.in`): `base.xlen=64`,
`extensions.{M=true, A/F/D/V/S/U=false, Zicsr=true, Zicclsm=true}`,
`memory.misaligned.exceptions.load_store={"None":null}`, `memory.regions=`
single flat RAM. `validate_config.sail` also requires S and U to be
enabled/disabled together — for M-mode-only, set **both** false.

---

## 5. The generated semantics: clean core, rich edges

### 5.1 State and monad (consumed surface)
- `SailM = PreSailM RegisterType trivialChoiceSource exception`
  (`Lean_RV64D/.../Defs.lean:1942`); state is registers (`ExtDHashMap`), byte
  memory (`ExtHashMap Nat (BitVec 8)`), cycle count, output
  (`Sail/Sail.lean:467-480`). Nondeterminism is **parametric and defeated by
  `trivialChoiceSource`** — base ISA is deterministic.
- The `Register` enum is the *full* RV64D set (~256: x0–x31, f0–f31,
  vr0–vr31 `BitVec 256`, full CSR file, 64×PMP, TLB, `satp`)
  (`Defs.lean:1540-1900`). Our `StateRel` relates only x0–x31 + memory — sound
  abstraction; §3's scoping is what shrinks this.
- `ExecutionResult` (`Defs.lean:1470-1482`) distinguishes
  `Retire_Success` / `Trap` / `Memory_Exception` / `Illegal_Instruction` / …;
  `Step` (`:1519-1526`) wraps it with fetch/interrupt staging.

### 5.2 The RV64IM core is clean
`execute_RTYPE/ITYPE/LOAD/STORE/MUL/DIV/REM` are plain `rX_bits`/`wX_bits` over
`BitVec` with **no CSR side-effects** (`InstsEnd.lean:67363+`, etc.). This is why
the existing `*_sail_equiv` lemmas go through. CSR entanglement appears only in
system/trap paths.

### 5.3 Everything is `noncomputable`
All `execute_*` are `noncomputable` (the `--lean-noncomputable` flag,
`sail_plugin_lean.ml:128`). **`rfl`/`decide` will not reduce instruction
execution** — proofs must go through `simp [simp_sail]` + the project's
`MonadLemmas`/`runSail_*` lemmas. Confirms design-doc note that "definitional
derivation" (B3) is a *proof*, never `rfl`.

### 5.4 ECALL / traps are a genuine semantic seam **[PLAN-IMPACT]**
In Sail, `ECALL`/`EBREAK` and any fault **do not retire**: they raise an
exception and `exception_handler` traps to M-mode (writes MEPC/MCAUSE/MTVEC,
redirects PC). The toy model treats `ECALL` as a **host-call abstraction**
(syscall dispatch / halt) and `EBREAK`/`FENCE` as no-ops. Consequently the clean
`RETIRE_SUCCESS`-shaped `*_sail_equiv` **cannot hold for ECALL**, and indeed the
project has equiv lemmas for ALU/mem/branch but **none for ECALL**. This is the
boundary between "guest ISA + host interface" and "full machine," and it must be
an explicit, named line in the compliance ledger, tied to the
`standard-termination-semantics` and `io-interface` zkVM standards.

### 5.5 `runBlock`-relevant footguns (for whoever does B1/B2)
- **x0:** the raw register store does not protect x0, but the `wX_bits` write
  wrapper does (and the project models x0-writes as no-ops via `sailStateWithReg`
  — consistent). Verify, don't assume.
- **PC discipline:** Sail uses explicit `nextPC` + `tick_pc`; the toy model bakes
  PC+=4 into `execInstrBr`. The existing AUIPC/branch lemmas already carry the
  PC-agreement hypothesis — B1 should make this uniform.
- **Memory:** width-based `read_mem`/`write_mem`; alignment is decided per
  PMA region (§4), not automatically.

### 5.6 `lean-sail` runtime is axiom-clean — with one watch item
No `sorry`/`unsafe`/`opaque`/`native_decide` in proof-relevant runtime code.
**Watch item:** the `match_bv` macro emits a `bv_decide` fallback when a
bitvector match lacks an `else` (`Sail/BitVec.lean:231`). If the **generated
decoder** (`encdec_backwards`) uses `match_bv` without an else, a `bv_decide`
could enter a proof term we depend on — which this project forbids and CI-gates
(`check-forbidden-tactics.sh` / `check-axioms.sh`). The decode tie (B2) must
verify the generated decode for the target subset is `bv_decide`-free, or route
around it.

---

## 6. Reproducible regeneration — the exact input set

To pin a regeneration (the `PROVENANCE.toml` + `regen-sail-model.sh` of
design-doc §4.2), record **all** of:

1. `riscv/sail-riscv` commit.
2. `rems-project/sail` (compiler) commit/version — and note its hardcoded
   `lean4:v4.29.0` / `mathlib v4.29.0` targets (§1.1).
3. `lean-sail` support-library rev (backend default **v4**; project currently
   **v3**).
4. The **module list** (`SAIL_MODULES`, §3) — the legible scope artifact.
5. The **config JSON** (`rv64*…json` + the §4 keys) — the legible ISA-tunables
   artifact.
6. Lean backend flags: `--lean-noncomputable`, `--lean-output-dir`,
   `--lean-import-file` (pulls in `handwritten_support/RiscvExtras.lean`),
   optionally `--lean-executable` (for §1 differential testing),
   `--lean-matchbv` (interacts with §5.6).

cmake recipe (per `model/CMakeLists.txt:406-475`): per `xlen∈{32,64}` it builds
`generated_lean_${arch}` with `${SAIL_MODULES} ${project_file}` and a per-xlen
config; override `-DSAIL_MODULES="--module prelude --module core … --module
M_insts --module postlude"`.

---

## 7. Net changes to the integration plan

| # | Finding | Change to `sail-zkvm-integration-design.md` |
|---|---|---|
| 1 | Lean backend is experimental, unverified, fails-loud | Elevate backend faithfulness to a **headline** trust item (§7); add **differential-testing** mitigation (executable model vs. Sail C sim / riscv-tests) as a new roadmap phase. |
| 1.1 | Backend targets lean4/mathlib v4.29.0, lib v4; project on v3 | Pipeline work entails a **toolchain/lib-version decision**; record in `PROVENANCE.toml`. |
| 2 | Module closure is well-typed by construction | Strengthen A1 from "preferred" to "sound by construction"; keep A2 gate as completeness check. |
| 3 | Closure = ~14 modules/~77 files, but `sys` drags vector/CSR types | Keep A1; add a spike task to **measure the generated `Register` enum** and decide on the `sys` residue. |
| 4 | Zicclsm = config; misaligned semantics already in model | **Flip §2.1 to option (a)** — model misaligned via config; no compliance caveat needed. |
| 5.4 | ECALL/traps diverge (host-call vs trap-to-M) | Add an explicit **ECALL/termination** ledger line; note no `ecall_sail_equiv` exists by design. |
| 5.6 | `match_bv`→`bv_decide` risk in generated decode | Add a B2 sub-check: confirm target-subset decode is `bv_decide`-free (else the forbidden-tactic gate trips). |

All `file:line` citations above are against the in-`.lake` packages and the
scratchpad clones of `riscv/sail-riscv` and `rems-project/sail` as of
2026-06-24.
</content>
