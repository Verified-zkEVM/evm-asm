/-
  MainProgress

  Entry point for `lake exe progress-report`. With no argument it prints the
  registry-driven sections of `PROGRESS.md` to stdout; with the argument `drift`
  it prints the body of the TCB / "what is NOT proven" ledger `DRIFT.md`. The
  shell wrappers (`scripts/progress-report.sh`, `scripts/drift-report.sh`)
  compose this with grep-derived sections and a snapshot banner.
-/

import EvmAsm.Progress
import EvmAsm.Progress.Obligations

open EvmAsm.Progress
open EvmAsm.Progress.Obligations

private def tierLabel : ProofTier → String
  | .proven      => "proven"
  | .partly      => "partial"
  | .conditional => "conditional"
  | .execSpec    => "execSpec"
  | .notStarted  => "notStarted"

private def tierIcon : ProofTier → String
  | .proven      => "✅"
  | .partly      => "🟡"
  | .conditional => "🔶"
  | .execSpec    => "⏳"
  | .notStarted  => "✗"

private def fmtRow (e : OpcodeEntry) : String :=
  let proofCell := e.proofRef.getD "—"
  let notesCell := if e.notes.isEmpty then "" else e.notes
  let cyclesCell := match e.cycleBound with
    | some n => s!"{n}"
    | none   => "—"
  s!"| {tierIcon e.tier} {e.name} | {tierLabel e.tier} | `{proofCell}` | {cyclesCell} | {notesCell} |"

private def renderRegistry : String :=
  let header :=
    "| Opcode | Tier | Witness theorem | Cycles (N) | Notes |\n\
     |---|---|---|---:|---|"
  let rows := String.intercalate "\n" (registry.map fmtRow)
  header ++ "\n" ++ rows

private def renderCounts : String :=
  s!"## Verification depth — A.2 opcode coverage

By **registry entry** (parameterized families collapsed; total = {totalEntries}):

| Tier | Count |
|---|---:|
| ✅ proven      | {provenCount} |
| 🔶 conditional | {conditionalCount} |
| 🟡 partial     | {partialCount} |
| ⏳ execSpec    | {execSpecCount} |
| ✗ notStarted   | {EvmAsm.Progress.notStartedCount} |


By **opcode byte** (PUSH/DUP/SWAP/LOG families expanded; total = {totalBytes}):

| Tier | Bytes |
|---|---:|
| ✅ proven      | {provenBytes} |
| 🔶 conditional | {conditionalBytes} |
| 🟡 partial     | {partialBytes} |
| ⏳ execSpec    | {execSpecBytes} |
| ✗ notStarted   | {notStartedBytes} |
"

/-! ## Obligation matrix (Phase 2, R-A1)

    Status labels are rendered with a *space* ("not started", not the camelCase
    `notStarted` tier label) so the deterministic `scripts/progress-delta.sh`
    `count_field` parser — which keys on `| <icon> <tier-label> |` — cannot
    mis-read an obligation row as a tier-count row. The whole section is emitted
    *before* `### Per-opcode registry`, so `opcode_tiers` (which only scans from
    that header onward) never sees it either. -/

private def statusCell : ObligationStatus → String
  | .done       => "✅ done"
  | .blocked    => "🟡 blocked"
  | .notStarted => "✗ not started"

private def blockerCell (o : Obligation) : String :=
  match o.status, o.blockedBy with
  | .done, _ => o.witness.getD "—"
  | _, []    => "—"
  | _, bs    => String.intercalate ", " (bs.map Blocker.render)

private def fmtObligationRow (o : Obligation) : String :=
  s!"| {o.id} | {o.name} | {statusCell o.status} | {blockerCell o} |"

private def renderObligations : String :=
  let rows := String.intercalate "\n" (obligations.map fmtObligationRow)
  s!"## Guest-program obligations (kernel-checked)

The nine obligations a complete L1 stateless block-validation guest program must
satisfy, each with the opcodes/infrastructure blocking it. This is the
*direction* axis: opcode-tier counts cannot tell you which obligation is blocked
by what. Source of truth, per-status counts, and the opcode cross-check live in
[`EvmAsm/Progress/Obligations.lean`](EvmAsm/Progress/Obligations.lean)
(`doneCount_eq = {doneCount}`, `blockedCount_eq = {blockedCount}`,
`notStartedCount_eq = {Obligations.notStartedCount}`, and `blocker_opcodes_in_registry`,
which fails the build if any opcode blocker stops naming a real registry entry).

| Status | Count |
|---|---:|
| ✅ done | {doneCount} |
| 🟡 blocked | {blockedCount} |
| ✗ not started | {Obligations.notStartedCount} |

| # | Obligation | Status | Blocked by |
|---|---|---|---|
{rows}
"

/-! ## DRIFT.md — TCB / "what is NOT proven" ledger (Phase 2, R-C3 / G3.3) -/

private def opcodeNamesAtTier (t : ProofTier) : List String :=
  (registry.filter (fun e => e.tier == t)).map (·.name)

private def fmtTierLedgerRow (e : OpcodeEntry) : String :=
  let notesCell := if e.notes.isEmpty then "—" else e.notes
  s!"| `{e.name}` | {notesCell} |"

private def renderTierLedger (t : ProofTier) : String :=
  let rows :=
    String.intercalate "\n" ((registry.filter (fun e => e.tier == t)).map fmtTierLedgerRow)
  "| Opcode | Why not (yet) fully proven |\n|---|---|\n" ++ rows

private def renderDrift : String :=
  let execSpecList := String.intercalate ", " (opcodeNamesAtTier .execSpec)
  s!"# DRIFT — trusted base & \"what is NOT proven\" ledger

> **Generated** by `lake exe progress-report drift` from the kernel-checked
> registry + obligation tracker in `EvmAsm/Progress.lean` and
> `EvmAsm/Progress/Obligations.lean`. `scripts/check-drift.sh` fails the build if
> this file drifts from the regenerated output — do **not** hand-edit. To
> refresh: `scripts/drift-report.sh --write`.

This is evm-asm's explicit assumptions / trusted-computing-base ledger, in the
spirit of the seL4 and CompCert assumptions lists. The Lean kernel makes every
*proven* statement unhackable; this file enumerates what the kernel does **not**
cover, so a green dashboard is never mistaken for a fully closed guest program.

{renderObligations}

## What is NOT proven

### 🔶 `conditional` opcodes — proven only on a restricted input domain

A complete top-level Hoare triple exists, but gated by a non-vacuous
precondition; the excluded domain is **unverified**.

{renderTierLedger .conditional}

### 🟡 `partly` opcodes — no complete top-level triple yet

Pure-spec / `<op>_correct` lemma proven, but no end-to-end stack-spec wrap.

{renderTierLedger .partly}

### ⏳ `execSpec` opcodes — handler/bridge semantics only, no RV64 subroutine

These {execSpecCount} opcodes have executable-spec / handler / host-bridge
semantics only; **no RV64 subroutine is proven to produce the EVM result**:

{execSpecList}.

### ✗ `notStarted` opcodes — not represented in `EvmOpcode`

{renderTierLedger .notStarted}

## Trust boundaries (unverified by design)

- **Codegen is unverified by design.** The RISC-V lowering, the ziskemu
  emulator, and the deferred codegen milestones (M5 EVM-interpreter loop and
  beyond) are explicitly outside the kernel-checked core. Drift is *fenced* by
  build-time `#guard` round-trip tests (`Codegen/RoundTripTests.lean`) and the
  conformance floor (`check-conformance-floor.sh`), not *proven*.
- **RV64 instruction-model fidelity.** The Lean RV64 semantics are tied to the
  official Sail RISC-V model via `Rv64/SailEquiv/` (the `dhsorens/sail-riscv-lean`
  fork pinned in `lakefile.toml`); the tie itself is a trusted reference, not a
  kernel theorem about real silicon.
- **EVM reference semantics.** Conformance is measured against
  `ethereum/execution-specs` (pinned submodule); that the pinned spec faithfully
  encodes consensus rules is assumed, not proven here.
- **Gas / memory cost modeling.** Per-opcode `cpsTripleWithin N` bounds are a
  verified *step-count surrogate*; the EVM gas schedule mapping is modeled, not
  proven equivalent to the yellow-paper schedule.
- **Trusted axiom base.** Only the three classical axioms
  (`propext`, `Classical.choice`, `Quot.sound`); `native_decide`/`bv_decide`
  trust axioms are forbidden (CI-gated by `check-axioms.sh` /
  `check-forbidden-tactics.sh`).
"

def main (args : List String) : IO Unit := do
  if args.contains "drift" then
    IO.println renderDrift
  else
    IO.println renderObligations
    IO.println ""
    IO.println renderCounts
    IO.println ""
    IO.println "### Per-opcode registry"
    IO.println ""
    IO.println renderRegistry
