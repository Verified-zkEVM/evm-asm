# Sail regeneration spike — P1 go/no-go report

**Verdict: 🟡 CONDITIONAL GO.** Scoped Lean generation for the zkVM RISC-V target
**works mechanically** in this environment, and the headline P1 risk ("can we even
run Sail's Lean backend") is gone — a working Sail compiler with the Lean backend
is installed. **But** the model it emits is **not drop-in compatible** with the
project's pinned lean-sail **v3**: there is a real version reconciliation (Sail
0.19.1 ↔ lean-sail **v4** / lean4 **v4.29.0**, vs project **v3** / **v4.30.0-rc1**),
and resolving it is the crux of P2. This corrects an earlier draft of this report
that wrongly claimed "no toolchain bump" — see "The version finding" below.

Date: 2026-06-24. Branch: `feat/sail-zkvm-integration`. No proof/model/build
changes were made to the project; all generation + build attempts happened in a
scratchpad.

---

## What works (the GO half)

1. **Sail + Lean backend is already installed** — opam switch `sail`, `sail 0.19.1`
   with `sail_lean_backend 0.19.1`. **No build-from-source.** z3 4.15.3 lives at
   the nix path in `scripts/regen-sail-model.sh` (Sail's typechecker needs it; not
   on `PATH` by default).
2. **Scoped generation runs cleanly** (exit 0, no errors) against sail-riscv
   `1760ee2` (the last commit requiring Sail 0.19.1). Output: **84 `.lean` files**
   for the `main + I_insts + M_insts` closure vs **154** for the full vendored
   RV64D model.
3. **The mechanism the design doc assumed is wrong, and the real one is recorded.**
   Sail 0.19.1 has **no `--module` flag** (it prints usage); the cmake Lean target
   **hardcodes `--all-modules`**. Scoping is done by **positional module args** to
   a **direct** `sail` call (`sail … riscv.sail_project main I_insts M_insts`),
   which pulls each module's `requires` closure transitively. `scripts/regen-sail-model.sh`
   now does exactly this (working `--run`).
4. **The generated decode is `bv_decide`-free** (review §5.6). We deliberately omit
   `--lean-matchbv`, so decode uses ordinary pattern matching. No
   `bv_decide`/`match_bv`/`by decide` in any generated decode/exec file
   (`DecodeExt`, `BaseInsts`, `MextInsts`, `InstsEnd`). (The lone `bv_decide` lives
   in the lean-sail *runtime*'s BitVec BEq macro — pre-existing, see `[[bv-decide-purge]]`.)
5. **`execute_*` *signatures* match the lemmas.** Generated
   `def execute_RTYPE (rs2 rs1 rd : regidx) (op : rop) : SailM ExecutionResult` is
   identical to how `EvmAsm/Rv64/SailEquiv/ALUProofs.lean` calls it. Same for
   ITYPE/LOAD/STORE/MUL/DIV/REM/SHIFTIOP.
6. **The validated zkVM config exists**: `sail-import/riscv64im_zicclsm.json`
   (sha256 `7dd1fa11…`) generates cleanly *and* passes `validate_config.sail`
   (M on; A/F/D/V off; S=U off; Zicclsm via `memory.misaligned`; NoFault regions).
   It is meaningfully consumed (its values are baked into the generated model;
   content differs vs the default config).
7. **Bonus — the RV64 word-op "coverage gap" is a model non-issue.** The scoped
   model already contains `execute_RTYPEW` (ADDW/SUBW/SLLW/SRLW/SRAW),
   `execute_SHIFTIWOP` (SLLIW/SRLIW/SRAIW), `execute_MULW/DIVW/REMW`, `execute_ADDIW`.
   So P5 is *lemmas-only*, not a model extension.

## What does NOT work yet (the reason it's CONDITIONAL)

**I attempted to actually type-check the generated model on v4.30.0-rc1. It fails**
— and the failures are instructive. This is the part the first draft skipped.

- The generator emits an **inline copy of the lean-sail runtime** (`Out/Sail/*`).
  That copy **does not build on v4.30.0-rc1**: it uses pre-v4.30 APIs
  (`BitVec.getMsb'`, `String`→`String.Slice` from `.take/.drop`,
  `String.Pos.Raw.get!`), plus an `omega` proof in `IntRange` that v4.30 rejects.
- The project's pinned lean-sail **v3** (`49ccc5a`, toolchain nightly-2026-03-05)
  **is exactly the v4.30-patched runtime** (`getMsb`, `(…).toString`, fixed omega).
  But wiring the 0.19.1 model to import external **v3** — i.e. the *real* dhsorens
  setup — **still fails in the model**: first a namespace drift (the model omits
  `open ConcurrencyInterfaceV1`, so `Access_variety` auto-binds → universe
  metavariable), then **API drift** (`Arch` used as a typeclass but isn't one in
  v3; `PreSail.sail_barrier` unresolved; duplicate `ExceptT.map_error`).

## The version finding (corrects the earlier draft)

The first draft claimed "Sail 0.19.1 emits against lean-sail v3 → no toolchain
bump." **That is false.** Evidence:

- lean-sail tags: **v3** = `49ccc5a` (toolchain nightly-2026-03-05, the one the
  project pins and that builds on v4.30.0-rc1); **v4** = `79b4d08` (toolchain
  **`v4.29.0`**).
- Sail **0.19.1** is contemporaneous with sail-riscv `1760ee2` and the **v4 / lean4
  v4.29.0** generation line — its emitted model assumes the v4-era runtime layout
  (the `ConcurrencyInterfaceV1`/`Arch`/`sail_barrier` shapes above), **not v3**.

So the **original review §1.1 was right** and this report's earlier "correction"
was wrong: there **is** a skew — *Sail 0.19.1 ↔ lean-sail v4 ↔ lean4 v4.29.0* on
one side, *project lean-sail v3 ↔ lean4 v4.30.0-rc1* on the other. The two lines
are mutually incompatible: v3 builds on v4.30 but doesn't match a 0.19.1 model; v4
matches a 0.19.1 model but targets v4.29.0 and (like the inline runtime) predates
the v4.30 String/BitVec API.

## The version triple — as measured (not as hoped)

| Component | Value | Status |
|---|---|---|
| Sail compiler | `0.19.1` (opam switch `sail`, Lean backend present) | installed; usable |
| sail-riscv | `1760ee2…` (last commit requiring Sail 0.19.1) | pinned |
| lean-sail the 0.19.1 model NEEDS | **v4** (`79b4d08`, lean4 v4.29.0) | ✗ not what project pins, ✗ pre-v4.30 |
| lean-sail the PROJECT pins | **v3** (`49ccc5a`, builds on v4.30.0-rc1) | ✗ doesn't match a 0.19.1 model |
| project toolchain | `leanprover/lean4:v4.30.0-rc1` | unchanged |
| z3 | `4.15.3` (nix store) | not on PATH by default |

## What P2 must decide (the reconciliation — now the explicit crux)

Pick one; all three are real and each has a cost. None is free.

- **Path A — align the project to the backend.** Move the project to lean4
  **v4.29.0** + lean-sail **v4**, then vendor the 0.19.1 scoped model drop-in.
  *Cost:* downgrades the project's Lean (v4.30.0-rc1 → v4.29.0) and re-points the 51
  lemmas. Undesirable unless v4.30 features aren't relied on.
- **Path B — keep v4.30, patch lean-sail v4 forward.** Vendor the 0.19.1 model +
  lean-sail **v4**, and backport v3's v4.30-compat fixes onto v4 (the `getMsb`,
  `String.Slice` `.toString`, and `IntRange` omega fixes — all visible in v3's
  diff). *Cost:* maintain a patched runtime; verify nothing else in v4 breaks on
  v4.30. **Most promising — keeps the project on v4.30.0-rc1.**
- **Path C — match v3 at the source.** Find/build the (older) Sail commit whose
  emitted model matches lean-sail **v3** (the one dhsorens used), and regenerate.
  *Cost:* reintroduces the "build a specific Sail from source" task P1 hoped to
  avoid; but yields a true drop-in on the project's existing, v4.30-working v3.

P2 should start by **building the 0.19.1 model against lean-sail v4** (Path B's
first half) to confirm v4 resolves the `Arch`/`sail_barrier`/`Access_variety`
drift the v3 attempt hit — the scratchpad work stopped at that boundary.

## Other measured facts (independent of the version issue)

- **State vector barely shrinks under scoping: 163 `Register` ctors (scoped) vs 178
  (full).** `sys` unconditionally `requires V_core → FD_core`, so `vr0..31`,
  `f0..31`, `vcsr/vtype/vl`, and S-mode CSRs come in regardless. Scoping trims
  instruction *logic* (~halves files), not *state* (review §3 confirmed). The 51
  lemmas are state-agnostic, so this is a legibility caveat, not a blocker.
- **Source rename in the model logic:** generated `Prelude` defines `bool_to_bits`
  where the vendored model uses `bool_to_bit`; `ALUProofs.lean` SLT/SLTU/SLTI
  `unfold bool_to_bit`. Independent of the runtime skew, this is one of the lemma
  re-pointings P2 owes.

## Reproducing

`scripts/regen-sail-model.sh --plan` prints the recipe; `--run <out-dir>` executes
it (clones sail-riscv `1760ee2`, cmake-configures, runs the scoped `sail`). Needs
the `sail` opam switch + nix z3 (both encoded in the script).
`sail-import/PROVENANCE.toml [target]` records the pins and the open reconciliation.
