# Sail-zkVM — consolidation bootstrap (StepSim fold + BareModeInv glue)

> **What this file is.** A self-contained kickoff for the Sail *consolidation* session —
> the follow-up the maintainer picked alongside Tier B. Open a fresh session, read only
> this file, and you have everything needed without re-deriving context.
>
> **Bootstrap files are LOCAL / UNCOMMITTED** (house convention). Deliverables (Lean
> proofs, doc updates) commit as normal; pushes are gated by the user.
>
> Start with `git fetch origin && git checkout -b feat/sail-consolidation origin/main`
> (after the Tier B branch `feat/sail-tier-b-stores` merges — otherwise branch off it).

## Status going in (2026-07-09, end of the Tier B session)

- **All 49 bridged instructions have unconditional per-instruction equivalence
  theorems.** Build green, `check-forbidden-tactics` OK, axioms within the
  `{3 classical} ∪ {4 platform}` allowlist.
  - 29 ALU/imm/shift/M-ext: consolidated in `step_execute_sail_sim_uncond`
    (`EvmAsm/Rv64/SailEquiv/StepSim.lean`), plain `StateRel` + `h_nextpc`.
  - 9 control-flow: per-instruction `*_step_sail_equiv` under `StateRelPC`
    (`StepProofs.lean`; AUIPC in `ALUProofs.lean`).
  - 7 loads: `ld_sail_equiv` (`VmemReduction.lean`), `l{w,wu,h,hu,b,bu}_sail_equiv`
    (`VmemReductionLoads.lean`) — `StateRel` + `BareModeInv` + per-access facts
    (alignment / PMA readable / MMIO-disjoint / byte presence).
  - 4 stores (NEW, Tier B): `s{d,w,h,b}_sail_equiv` (`VmemReductionStores.lean`),
    chain in `VmemWriteReduction.lean` — same bundle, **no byte-presence hyps**,
    PMA `writable` + `within_mmio_writable` instead of the readable variants.
- `MemProofs.lean` is a pointer-comment husk; no `h_exec` anywhere.

## Goal of this session (two deliverables)

### 1. The consolidated fold (`step_execute_sail_sim` over all 49)

Extend `Instr.simulableUncond` → a full `Instr.simulable` and state ONE theorem
dispatching every bridged constructor. Design constraints discovered earlier
(StepSim header has the tier map):

- The invariant must be `StateRelPC` (or `StateRel` + explicit `PC`/`nextPC` hyps —
  the control-flow lemmas already take `h_nextpc`; main strengthened all 32
  per-instruction lemmas with `h_nextpc` threading).
- Memory ops need a **per-instruction side-condition predicate**
  (`sideCond : Instr → SailState → MachineState → Prop`) carrying the
  `BareModeInv` + per-access facts; the theorem is stated as
  `∀ i, simulable i → sideCond i sSail sRv → …`. For non-memory instructions
  `sideCond` should be `True` (definitional match).
- Dispatch: explicit `cases i with` + per-arm `apply <lemma>` (the `sim_step` /
  `no_sim` macro pattern in StepSim; NEVER a `first|` search — blows past 2 min).
- Loads additionally return-value-match through `extend_value`; the existing lemma
  statements are exactly the arm shapes, so arms should be `apply`-level.
- Exit criterion: axioms `{propext, Classical.choice, Quot.sound}` ∪
  `{load_reservation, match_reservation, plat_term_write,
  sys_enable_experimental_extensions}`; zero warnings (CI gate covers all EvmAsm/).

### 2. `BareModeInv` construction glue (the Tier A review's 🟡 note)

`hclint/hsig/hhtif/h_match` are abstract per-call-site obligations with no
construction lemma. Needed:

- A "RAM address ⇒ MMIO-disjoint ∧ readable/writable region" lemma from the concrete
  `sail_model_init` platform state (CLINT/SIG ranges in `Out/Platform.lean:203/214`,
  HTIF via the `htif_tohost_base` register, PMA region list in `pma_regions`).
- A mechanized non-vacuity witness `example`: a concrete bare-mode `SailState` +
  RAM dword satisfying every hypothesis of `ld_sail_equiv` (and now `sd_sail_equiv`).
- This serves both the fold's `sideCond` discharge and the eventual end-to-end use.

## Tier B technique notes (reusable; full detail in the memory note `[[sail-zkvm-integration]]`)

- 🛑 `8*i` lexes as the Sail `*i` Int-mul token in any file importing the vendored
  model — always space binary `*` before an identifier starting with `i`.
- `execute_STORE`/`execute_LOAD` index arithmetic elaborates as **unreduced lambdas**
  (`(fun x y => x - y) (…) 1`); `rw [show … from by decide]` patterns must spell the
  `*i`/`-i` notation with the exact coercion placement (first operand ↑-cast, second a
  plain Int literal). `omega` fails on the lambda form; `decide` works.
- Width expressions inside `extractLsb`/`updateSubrange` type indices are a
  dependent-type wall — state helper lemmas at the exact index *shape*
  (`8*w - 1`, not the literal) per concrete width.
- `Std.ExtHashMap.getD_insert` chains: resolve per-case with explicit
  `rw [if_neg (by simp), …, if_pos (by simp)]` (default simp cancels `a+m = a+n`);
  conditional-rewrite side conditions do NOT discharge via `simp +decide only`.
- Keep default `simp`/`simpa` away from goals containing the insert chain (whnf
  timeout); use targeted `rw` + `exact` — `exact` sees through `set`-bound states
  by defeq.
- `rcases eq_or_ne a' addr with rfl | hne` substitutes **a'** away when `addr` is
  `set`-bound — write the rfl branch in terms of `addr`.

## Verification checklist (every session)

1. `lake env lean <file>` per file → `lake build EvmAsm` (full, background).
2. `scripts/check-forbidden-tactics.sh`.
3. `#print axioms` on each new top-level theorem (scratchpad import file) —
   allowlist only, no `sorryAx`, no `bv_decide`/`native_decide` axioms.
4. Zero warnings (the no-warnings CI gate covers all of `EvmAsm/`).
