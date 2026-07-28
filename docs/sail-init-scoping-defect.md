# Sail model defect: `sail_model_init` cannot boot (module-scoping dropped `currentlyEnabled` clauses)

**Status:** diagnosed, kernel-checked. No fix applied (maintainer decision pending).
**Date:** 2026-07-10. **Branch:** `feat/sail-tier-b-stores`.
**Affects:** the vendored scoped Sail model `vendor/sail-riscv-zkvm-lean/` (package `out`, lib `Out`).

> **Partial-resolution note (2026-07-28, `fix/sail-zicsr-scope`, #10688).** The
> 2026-07-27-9901550 regen widened the module scope by `Zicsr_insts`, restoring
> the `Ext_Zicsr` arm of `currentlyEnabled`. That fixed the *JALR* consequence
> of this same scoping defect: `update_elp_state` no longer faults, so
> `jalr_sail_equiv` is no longer vacuous and JALR is covered at run level (see
> `update_elp_state_noop` in `RunInv.lean` and `jalr_sideCond_of_runInv` /
> `jalr_sideCond_satisfiable` in `StepRun.lean`). **`sail_model_init` itself is
> still broken**, kernel-checked against the new model: `currentlyEnabled`
> still has no arms for `Ext_Zkr`, `Ext_Zicboz`, `Ext_Zicbom` (nor `Ext_Zicntr`
> / `Ext_Zfhmin`), and `legalize_senvcfg` — init's first monadic step — still
> binds `← currentlyEnabled Ext_Zicboz` first, so
> `∃ e s', legalize_senvcfg o v s = .error e s'` remains provable for all
> args/states (`legalize_mseccfg` likewise errors via `Ext_Zkr`). The
> initializer tie-in stays blocked until the scope also includes the
> `zicbo`/`zkr` (and, for totality, `zicntr`/`zfh`) modules or the model is
> generated unscoped.

## TL;DR

`sail_model_init` — the vendored Sail RISC-V model's platform initializer — **errors for
every input state**. It throws inside the CSR-legalization routine `legalize_senvcfg`
because the *scattered* function `currentlyEnabled` lost its clauses for
`Ext_Zicsr`, `Ext_Zkr`, `Ext_Zicboz`, `Ext_Zicbom`, `Ext_Zicntr`, `Ext_Zfhmin` when the
model was generated with the module scope `{main, I_insts, M_insts}`. Those extensions'
`currentlyEnabled` clauses live in extension modules that were excluded from the scope,
but `main`'s CSR postlude still calls `currentlyEnabled` on them, so the calls hit the
`_ => assert false; throw Error.Exit` fallthrough.

This is **not** an extraction bug, **not** an upstream sail-riscv bug, and **does not**
affect any existing proof (all 49 `*_sail_equiv` lemmas + the `StepSim` fold take
`BareModeInv` as a *hypothesis* and never run `sail_model_init`). It only blocks the
"initializer tie-in" — deriving a bare-mode `SailState` from the model's own boot routine.

## Symptom (kernel-checked)

The following theorem is provable (axioms: the 3 classical + `sys_enable_experimental_extensions`,
i.e. the SailEquiv track's normal allowlist; no `sorry`, no `bv_decide`/`native_decide`):

```lean
theorem sail_model_init_run_none (s : SailState) :
    runSail (sail_model_init ()) s = none
```

Supporting facts (also kernel-checked):

```lean
-- currentlyEnabled has no arm for these → throwing fallback → errors, for any state:
example (s) : runSail (currentlyEnabled extension.Ext_Zicsr)  s = none := by unfold currentlyEnabled; rfl
example (s) : runSail (currentlyEnabled extension.Ext_Zkr)    s = none := by unfold currentlyEnabled; rfl
example (s) : runSail (currentlyEnabled extension.Ext_Zicboz) s = none := by unfold currentlyEnabled; rfl

-- legalize_senvcfg (init's FIRST monadic step, model line 227) errors for ANY args/state,
-- because its first monadic bind is `← currentlyEnabled Ext_Zicboz`:
theorem legalize_senvcfg_err (o v : BitVec 64) (s : SailState) :
    ∃ e s', legalize_senvcfg o v s = .error e s' := by
  unfold legalize_senvcfg
  simp only [bind, EStateM.bind]
  unfold currentlyEnabled
  exact ⟨_, _, rfl⟩

-- writeReg always succeeds; the capstone chains through init's 14-writeReg prefix
-- via runSail_bind and lands on the legalize_senvcfg error:
theorem sail_model_init_run_none (s : SailState) : runSail (sail_model_init ()) s = none := by
  unfold sail_model_init
  simp only [runSail_bind, runSail_writeReg, legalize_senvcfg_run_none]
```

(Full scratch proof preserved off-tree; not committed — this is a *finding*, not a change.)

## Root cause

`currentlyEnabled : extension → SailM Bool` is a **scattered function** in sail-riscv —
one `clause currentlyEnabled(Ext_Foo) = …` per extension, each defined in that extension's
`.sail` module. When Sail's Lean backend flattens it into a single `match`, only the
clauses from *included* modules survive; every other constructor falls through to the
final catch-all:

```lean
| x => do
    assert false "Pattern match failure at extensions/M/mext_insts.sail:14.0-14.95"
    throw Error.Exit
```

The regen (`scripts/regen-sail-model.sh`, pins in `sail-import/PROVENANCE.toml`) scopes to
the positional Sail modules `{main, I_insts, M_insts}`. That set:

- **includes `main`** → which transitively pulls in the sys/CSR postlude, so
  `legalize_senvcfg` / `legalize_mseccfg` are present and *call* `currentlyEnabled` on
  Zicsr / Zkr / Zicbo / Zicntr / Zfh (via `Ext_S` → `Ext_Zicsr`, and directly);
- **excludes** the `zicsr` / `zkr` / `zicbo` / `zicntr` / `zfh` modules → so those
  `currentlyEnabled` clauses are dropped.

Result: `currentlyEnabled Ext_Zicsr` (etc.) hits the throw, `legalize_senvcfg` throws,
`sail_model_init` throws.

**The call chain, concretely** (line numbers in `vendor/sail-riscv-zkvm-lean/Out.lean` /
`Out/PlatformConfig.lean`):

- `sail_model_init` (Out.lean:203) runs a prefix of 14 plain `writeReg`s, then at line 227
  binds `← legalize_senvcfg (Mk_SEnvcfg zeros) zeros` — the first monadic step.
- `legalize_senvcfg` (PlatformConfig.lean:1665) binds `← currentlyEnabled Ext_Zicboz` first.
- `currentlyEnabled` (PlatformConfig.lean:1427) has no `Ext_Zicboz` arm → throw.

(`legalize_mseccfg` at init line 228 would also throw — via `currentlyEnabled Ext_S`
→ `Ext_Zicsr` and `Ext_Zkr` — but init already dies at 227.)

## Confirmation against the full model

The old **unscoped** dhsorens full model (`.lake/packages/Lean_RV64D/`) has the arms and
would init fine:

```
LeanRV64D/Types.lean:734:  | Ext_Zkr   => (pure (hartSupports Ext_Zkr))
LeanRV64D/Types.lean:748:  | Ext_Zicsr => (pure (hartSupports Ext_Zicsr))
```

So the *full* `currentlyEnabled` is total over the real extensions; only the scoped
regen drops clauses.

## Why this cost nothing to gain nothing

`scripts/regen-sail-model.sh` and the regen spike (`docs/agents/sail-regen-spike.md`)
already flag scoping as an open question and record that **"scoping did NOT reduce
generation memory."** So the `{main, I_insts, M_insts}` scope bought a broken initializer
for zero memory benefit.

## Impact assessment

- **No existing proof is affected.** `ld_sail_equiv`, `s{d,w,h,b}_sail_equiv`, the load
  variants, and the `StepSim` consolidated fold all take `BareModeInv` as a *hypothesis*.
  `bareModeWitnessState` (`VmemConstruction.lean`) is a *manually constructed* bare-mode
  state whose `pma_regions` is transcribed verbatim from `sail_model_init`'s source. None
  of these execute `sail_model_init`.
- **What is blocked:** the "initializer tie-in" — proving the model's own boot routine
  produces a state satisfying `BareModeInv` (i.e. that our `BareModeInv` precondition is
  *reachable*/non-vacuous w.r.t. the real boot config, not just assumed). That derivation
  is impossible while init errors.

## Fix options (not yet applied)

1. **Re-scope the regen** — add the modules that define the needed `currentlyEnabled`
   clauses (`zicsr`, `zkr`, `zicbo`, `zicntr`, `zfh`) to `SAIL_MODULES` in
   `scripts/regen-sail-model.sh`. Minimal, but requires enumerating the exact module names
   from the sail-riscv `riscv.sail_project` at tag `2026-06-22-b5a2182`.
2. **Drop scoping — generate the full model.** Guarantees `currentlyEnabled` is total.
   Since scoping gave no memory benefit, this is the low-risk choice (larger file count).

Either way it's a **trust-anchor change**: regenerate → re-vendor → re-point the 49
`*_sail_equiv` lemmas (mind renames, e.g. `bool_to_bit`→`bool_to_bits`) → re-validate
`lake build` + axiom footprint + the `model_sha256` pin in `PROVENANCE.toml` /
`check-sail-pin.sh`. Best done as its own focused effort, not folded into unrelated work.

**Toolchain feasibility (this machine):** the active `sail5` opam switch (OCaml 5.4.1,
Sail 0.20.2) and z3 4.15.3 at `/nix/store/x6z3sjmccszacl1xvdlpi7bd4ps7mhci-z3-4.15.3`
match the regen script's pins exactly. Regen needs network to clone sail-riscv and
~9–13 min / ~7 GB.

## Relation to the zkVM standard

(Refs: `eth-act/zkvm-standards` `standards/riscv-target/target.md`,
`memory-layout-restrictions/`, `memory-safety-guard-regions/`.)

This defect has a real relation to the standard, and it cuts two ways.

**1. The dropped extensions are exactly the ones the standard puts out of scope — so
excluding them was correct.** The missing `currentlyEnabled` arms are `Zicsr`, `Zkr`,
`Zicboz`, `Zicbom`, `Zicntr`, `Zfhmin`. None are in the standard's target ISA
(`RV64I` + `M` + `Zicclsm`; F/D excluded, hence no `Zfh`/`Zfhmin`; no
crypto/cache-management/counter extensions listed; Privileged Mode = Machine only;
Syscalls/Environment = None). So this is **not** "we wrongly scoped out a required
extension" — the scope choice is faithful to `target.md`.

**2. The defect exposes a mismatch between the Sail model's *boot sequence* and the
standard's *machine model*.** The standard mandates Machine-mode only, no supervisor,
`Syscalls/Environment = None`, flat memory / no MMU / no paging. Yet `sail_model_init`
runs a full privileged-platform CSR bring-up:

- `legalize_senvcfg` — the **Supervisor** Environment Config CSR (an S-mode register that
  doesn't architecturally exist in an M-mode-only machine);
- `legalize_mseccfg` — Machine Security Config, whose fields (pointer-masking `PMM` via
  `Smmpm`, etc.) are themselves out-of-target extensions.

Those legalizers are precisely what reach for the excluded extension clauses (`senvcfg`'s
first bind is `← currentlyEnabled Ext_Zicboz`; `mseccfg` binds `Ext_S`→`Ext_Zicsr` and
`Ext_Zkr`). So init is performing supervisor/security setup the standard-conformant target
has no use for, and depending on modules the target correctly omits. The scoped extraction
pulled in the full-platform boot code but not the extension logic that boot code assumes.

**3. For the tie-in, this suggests the standard-faithful target isn't `sail_model_init` at
all.** The standard's "initial state" is minimal: M-mode, flat RAM, the first-4 kB
null-trap region, a (vendor-specific) entry point, inputs preloaded — and it explicitly
leaves boot / entry point / input-loading **vendor-specific** (`memory-layout-restrictions`).
No standard prescribes a CSR init sequence. That minimal state is essentially what
`bareModeWitnessState` (`VmemConstruction.lean`) already encodes, and its PMA table matches
the standard: 2 GiB main memory at `0x8000_0000`, and `[0, 0x1000)` mapped by no region so
the first 4 kB fault (the mandated null-pointer trap). Consequences:

- The standard is **satisfied by the witness state** — it is a legitimate
  M-mode / flat-memory configuration.
- What's broken is only *deriving that state from the full RISC-V privileged boot*, which
  is exactly the part the standard says a zkVM does **not** need.

So a defensible reframing of the fix: rather than "make `sail_model_init` run," tie
`BareModeInv` to a **minimal reset predicate** (M-mode + flat RAM + the PMA map) and treat
the full privileged boot as out of scope — arguably *more* faithful to a `riscv64im_zicclsm`
M-mode-only zkVM than replaying supervisor CSR legalization would be. Regenerating the full
model (fix option 2 above) would also work, but it re-introduces boot machinery the standard
deliberately excludes; if taken, that machinery should be understood as model-internal, not
part of the conformance surface.

## Standards note (orthogonal)

Independent of this defect: the memory equivalence proofs are scoped to **aligned**
accesses/jump targets. The `Zicclsm` requirement (transparent misaligned *data* access)
is satisfied at the model level (`misaligned_exceptions.load_store = none` in every init
PMA region) but is **not yet covered by any equivalence proof**.
