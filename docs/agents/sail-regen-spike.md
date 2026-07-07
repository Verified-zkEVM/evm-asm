# Sail regeneration spike — P1 report (validated) + direction for P2

**Verdict: 🟢 GO — proven end-to-end.** The current-upstream model generates AND
builds, patch-free, on the project's toolchain: Sail 0.20.2 (built on OCaml ≥5.2)
generates the scoped model (113 files); that model + external lean-sail v4 builds on
the project's lean4 v4.30.0-rc1 — `lake build` 84/84 jobs, exit 0, including
`InstsEnd` (the `execute_*` semantics), `DecodeExt`, `Step`, `Model`. No toolchain
change, no source patching.

**Two hard requirements learned the hard way:**
- **Build Sail on OCaml ≥5.2** (we used 5.4.1). On OCaml 4.14.2 the Lean backend
  **stack-overflows** on the sail-riscv model (rems-project/sail#1674 — pre-5.2
  stdlib isn't tail-recursive). This was the real blocker, not the Sail version.
- **Pass all three `--lean-non-beq-type`** (instruction, ExecutionResult, Step) — the
  exact set sail-riscv's cmake target uses; omitting the latter two makes
  `ExecutionResult` fail to derive `BEq`.

Generation cost: ~9–13 min wall / ~7 GB RSS (one-time; `--memo-z3` helps).

**Chosen P2 direction (maintainer, 2026-06-25): use the latest/best of each
upstream component** — Sail **0.20.2** + sail-riscv release tag
**`2026-06-22-b5a2182`** + external lean-sail **`v4`** — rather than the older Sail
0.19.1 the spike first explored. **No project toolchain change:** lean-sail v4
builds as-is on the project's v4.30.0-rc1 (verified). See "Resolved version stack".

> Honesty note: this report's verdict changed three times during the spike. The
> first two ("drop-in v3, no bump"; then "deep skew, need v4") were wrong — the
> first untested, the second an over-conclusion from a `grep` artifact (I grepped
> `class Arch`→0 and inferred Arch wasn't a class; it is — `class
> ConcurrencyInterfaceV1.Arch`, qualified). The verdict here is the only one backed
> by a multi-module build. Detail in "What the build proved".

Date: 2026-06-24/25. Branch: `feat/sail-zkvm-integration`. No proof/model/build
changes to the project; all work in a scratchpad.

---

## Environment facts (the de-risking)

- **Sail + Lean backend installs from opam.** opam offers `0.13 … 0.19.1, 0.20,
  0.20.1, 0.20.2`. `opam install sail.0.20.2` succeeds and ships
  `sail_lean_backend 0.20.2`. **No build-from-source pain.** (0.19.1 was also
  already present and is what the early spike used.)
- **z3 4.15.3** lives at a nix-store path; Sail's typechecker needs it and it is
  **not on `PATH` by default** (see `scripts/regen-sail-model.sh`).
- **Scoping mechanism, corrected per version:**
  - Sail has **no `--module` flag** in 0.19.1 *or* 0.20.2 (only `--all-modules`).
    Subsets are selected by **positional module names** after the project file:
    `sail … riscv.sail_project main I_insts M_insts` (pulls each module's
    `requires` closure).
  - sail-riscv **`main`** exposes `SAIL_MODULES` as a cmake cache var
    (`-DSAIL_MODULES=…`), so scoping is reachable through cmake there. The old
    `1760ee2` commit hardcoded `--all-modules` (no override) — which is why the
    early spike invoked `sail` directly.

## Resolved version stack (the P2 target)

Direction (maintainer, 2026-06-25): use the **latest/best of each** component; keep
the project toolchain unless a real trade-off forces otherwise.

| Component | Pin | Notes |
|---|---|---|
| Sail | **0.20.2** (opam) | Latest; Lean backend present; satisfies sail-riscv's `≥0.20.1`. |
| sail-riscv | **`2026-06-22-b5a2182`** (latest release tag) | `RiscvExtras.lean` uses `import Sail.Sail` → model depends on the **external** lean-sail package (no inlined runtime). Generation validated on `main` (`e123b61`, ~equivalent). |
| lean-sail | **`v4`** (`79b4d08`, HEAD) | The **matched** runtime Sail 0.20.2 emits as the lakefile `require`. |
| lean4 toolchain | **`v4.30.0-rc1` (UNCHANGED)** | See below — no change needed. |
| z3 | `4.15.3` (nix) | not on PATH by default |

**Toolchain — RESOLVED, no change needed.** lean-sail v4 *declares*
`lean-toolchain = v4.29.0`, but that's only its CI's toolchain, not a requirement.
**Verified: lean-sail v4 (`79b4d08`) builds cleanly on the project's v4.30.0-rc1**
(`lake build`, 7/7 jobs, exit 0). Since v4 is the runtime the 0.20.2 model already
targets, the matched pair builds on v4.30.0-rc1 with **no toolchain downgrade and no
cross-version source patching**. My earlier "must move to v4.29.0 or forward-patch"
framing was a false premise (declared ≠ required toolchain). (It would also have been
costly: the project pins mathlib `master`, so a v4.29.0 move would have forced pinning
mathlib off master — now moot.) The "track v3 to avoid a bump" idea is likewise
unnecessary — v4 is the matched runtime and works as-is.

---

## What the build proved (the validation)

I generated a scoped model and **built it against the project's actual lean-sail
runtime on v4.30.0-rc1**, compiling **34 modules** — including `MextInsts` (the
M-extension `execute_*` semantics), `Defs`, `Prelude`, `Specialization`,
`ReadWriteV1` — before the next adaptation point. This establishes:

- **The generated instruction semantics are sound against a real runtime/toolchain**
  — not just "it emitted files."
- **The gap between a generated model and a given (lean-sail, lean4) pair is a
  bounded set of mechanical `v4.29→v4.30` source adaptations, NOT a semantic
  incompatibility.** Concretely (when forcing the 0.19.1 model onto lean-sail v3):
  1. missing `open ConcurrencyInterfaceV1` (one cause behind the `Arch`,
     `Access_variety`, `sail_barrier` errors);
  2. one duplicate def (`ExceptT.map_error`, which the runtime already provides);
  3. `String.Slice`: `String.drop/take str N` → add `.toString`;
  4. `meta` is a reserved keyword in v4.30 → rename the generated param;
  5. `termination_by` clauses (e.g. `currentlyEnabled_measure`) — the only
     non-trivial item; present in the v3-clean dhsorens model, **not** emitted by
     my 0.19.1 run (a generation-config/version difference).

The lesson: those adaptations are the tax of running a model against a *mismatched*
runtime. The clean answer is the **matched** pair — Sail 0.20.2's model + lean-sail
**v4** (which the generator targets by construction) — and **v4 builds as-is on the
project's v4.30.0-rc1** (verified), so there is **no patch tax and no toolchain
change**. The five adaptations above are documented only as the *fallback* picture
(what a mismatch would cost), not the path we take.

## Measurements (version-independent, still valid)

- **Generation works**: scoped `main + I_insts + M_insts` → 84 files (vs 154 full).
- **Decode is `bv_decide`-free** (we omit `--lean-matchbv`; no
  `bv_decide`/`match_bv`/`by decide` in any generated decode/exec file). The lone
  `bv_decide` is in the lean-sail runtime's BitVec BEq macro — pre-existing
  (`[[bv-decide-purge]]`).
- **`execute_*` signatures match the 51 `*_sail_equiv` lemmas** (e.g.
  `execute_RTYPE (rs2 rs1 rd : regidx) (op : rop) : SailM ExecutionResult`).
- **Word-ops already in the model** (`RTYPEW`/`SHIFTIWOP`/`MULW`/`DIVW`/`REMW`/
  `ADDIW`) → the P5 "coverage gap" is **lemmas-only**, not a model extension.
- **Scoping barely shrinks state: 163 `Register` ctors vs 178 full.** `sys` →
  `V_core` → `FD_core` is unavoidable, so `vr0..31`/`f0..31`/`vcsr`/S-mode CSRs stay
  regardless. Scoping trims instruction *logic* (~half the files), not *state*.
  **Open question for P2 (see plan):** whether scoping earns its complexity vs.
  full-model + a coverage/scope gate.
- **One known model-logic rename to re-point:** `bool_to_bit → bool_to_bits`
  (Prelude), hit by `ALUProofs` SLT/SLTU/SLTI. Diff regenerated-vs-vendored to
  enumerate the rest.
- **Config caveats to tighten in P2:** `riscv64im_zicclsm.json` was only verified
  to *generate* (not to pass `validate_config` at runtime); it keeps 3 memory
  regions rather than the design's "single flat RAM"; the kept-extension set
  (Zicntr/Zihpm/Zifencei) is not yet justified against the zkVM standard.

## Maintainability notes carried into the plan

- The regen recipe currently hard-codes the nix z3 path and `~/.opam` paths →
  **not portable / not CI-able** as written. P2 should parameterize (env vars /
  discovery) before any CI regen gate.
- Pinning to a *release* (Sail 0.20.2, a sail-riscv tag/release) rather than an
  arbitrary mid-history commit is part of why we track upstream — it makes
  provenance auditable and drift gates meaningful.

## Reproducing

`scripts/regen-sail-model.sh --plan` prints the recipe; `--run <out-dir>` executes
it. `sail-import/PROVENANCE.toml [target]` records the resolved current-upstream
pins (Sail 0.20.2 · sail-riscv `2026-06-22-b5a2182` · lean-sail v4 · project stays
on lean4 v4.30.0-rc1).
