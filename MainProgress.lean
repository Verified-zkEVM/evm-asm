/-
  MainProgress

  Entry point for `lake exe progress-report`. With no argument it prints the
  registry-driven sections of `PROGRESS.md` to stdout; with the argument `drift`
  it prints the body of the TCB / "what is NOT proven" ledger `DRIFT.md`. The
  shell wrappers (`scripts/progress-report.sh`, `scripts/drift-report.sh`)
  compose this with grep-derived sections and a snapshot banner.
-/

import EvmAsm.Progress
import EvmAsm.Progress.Correspondence
import EvmAsm.Progress.Obligations

open EvmAsm.Progress
open EvmAsm.Progress.Obligations
open EvmAsm.Progress.Correspondence (countVerdict countBasis)

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


/-! ### Correspondence (axis F)

    Rendered from `EvmAsm/Progress/Correspondence.lean`, which answers a
    different question from the tier registry above: not "how deep is this
    proven?" but "does the spec it is proven against match the reference?".
    The `basis` column is the load-bearing part — a verdict without a stated
    basis is an unverified claim. -/

private def verdictLabel : EvmAsm.Progress.Correspondence.Verdict → String
  | .agrees => "agrees"
  | .domainRestricted => "domain-restricted"
  | .stricter => "stricter ⚠"
  | .looser => "**looser — false-accept**"
  | .noCounterpart => "no counterpart"
  | .unproven => "n/a — unproven"

private def basisLabel : EvmAsm.Progress.Correspondence.Basis → String
  | .diff => "diff"
  | .bridged => "bridged"
  | .machineOnly => "machine-only"
  | .inspection => "inspection"
  | .none => "—"

private def kindLabel : EvmAsm.Progress.Correspondence.Layer → String
  | .guest => "guest"
  | .model => "model"

private def fmtCorrRow (e : EvmAsm.Progress.Correspondence.Entry) : String :=
  let spec := match e.spec with | some t => s!"`{t}`" | none => "—"
  s!"| `{e.family}` | {kindLabel e.kind} | `{e.routine}` | {spec} | {verdictLabel e.verdict} | {basisLabel e.basis} | {e.reference} |"

private def renderCorrespondence : String :=
  let rows := String.intercalate "\n" (EvmAsm.Progress.Correspondence.registry.map fmtCorrRow)
  s!"## F.2 — Spec-correspondence audit

Does a proven routine prove the *right* thing? A whole-routine triple ties
RISC-V to the Lean spec beside it and says nothing about whether that spec
matches the external reference. Emitted from the kernel-checked registry in
[`EvmAsm/Progress/Correspondence.lean`](EvmAsm/Progress/Correspondence.lean),
which also proves `no_looser_verdicts` (no audited routine accepts input the
reference rejects) and `verdict_requires_spec`.

Method: [`docs/agents/spec-correspondence.md`](docs/agents/spec-correspondence.md).

| Verdict | Count |
|---|---|
| agrees | {countVerdict EvmAsm.Progress.Correspondence.Verdict.agrees} |
| domain-restricted | {countVerdict EvmAsm.Progress.Correspondence.Verdict.domainRestricted} |
| stricter | {countVerdict EvmAsm.Progress.Correspondence.Verdict.stricter} |
| **looser** | {countVerdict EvmAsm.Progress.Correspondence.Verdict.looser} |
| no counterpart | {countVerdict EvmAsm.Progress.Correspondence.Verdict.noCounterpart} |
| n/a — unproven | {countVerdict EvmAsm.Progress.Correspondence.Verdict.unproven} |

| Basis | Count | Meaning |
|---|---|---|
| diff | {countBasis EvmAsm.Progress.Correspondence.Basis.diff} | backed by `lake exe correspondence-check` |
| bridged | {countBasis EvmAsm.Progress.Correspondence.Basis.bridged} | tied to the shared model, inherits the differential |
| machine-only | {countBasis EvmAsm.Progress.Correspondence.Basis.machineOnly} | spec restates the rules locally; differential does NOT transfer |
| inspection | {countBasis EvmAsm.Progress.Correspondence.Basis.inspection} | read both sides; no executable backing |
| — | {countBasis EvmAsm.Progress.Correspondence.Basis.none} | no verdict to support |

`diff` is 0 at *routine* granularity by construction: the differential validates
the shared **model** (`EL.RLP` vs the pinned reference, 0 divergences), and
routines inherit that through `bridged`. A `machine-only` row does **not**
inherit it — its spec restates the reference's rules locally, so a drift between
predicate and model would be invisible to both the differential and the proof.

A **model** row is a pure Lean function whose evidence is the executable
differential; a **guest** row is a RISC-V routine whose evidence is a
whole-routine spec. A family where the model agrees but every guest row is
`unproven` is reporting exactly that: the semantics are right, and whether the
assembly implements them is the open obligation.

| Family | Layer | Routine / function | Spec | Verdict | Basis | Reference |
|---|---|---|---|---|---|---|
{rows}"

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
- **Handler glue is proven per-opcode, not universally.** Each opcode is
  `.proven` on its verified *body* spec, but the subroutine the codegen emits,
  `h_<OP>`, wraps that body in glue — a stack-underflow guard prologue, any
  `preBody` clobber-saves / `la` address loads, and the advance-`x10`/`ret`
  tail — that the body spec does not cover. This handler glue is separately
  kernel-proven (guard + body + tail, both underflow and no-underflow paths)
  for `ADD` (`Codegen.Proofs.evmAddGuardedHandlerSpec`) and `CALLDATALOAD`
  (`Codegen.Proofs.evm_calldataload_staged_guarded_handler_spec`); for the other
  `.proven` opcodes (`MOD`, `EXP`, `ADDMOD`, …) the preBody glue is **not yet
  proven**. The final tie from the proven Program to the emitted ELF bytes is
  machine-checked for `h_ADD` only (`scripts/check_guarded_handler_bytes.py`);
  for `CALLDATALOAD` the `la` targets are proven relative to reconstruction
  hypotheses, with the byte-tie deferred.
- **`RETURNDATACOPY`'s image omits the framed-out high-limb operand guards.**
  The `.proven` witness `evm_returndatacopy_body_stack_spec_within` covers the
  body (`base → base+80`: bounds guards, operand pop / pointer setup, copy loop),
  but the emitted handler additionally runs, *between* the operand loads and the
  frame materialization, two blocks the modeled image excises along with the
  dynamic-gas / MSIZE glue: (i) `memDynamicU256RangeOogGuardAsm`, which sends a
  high-limb `size` — and, when `size ≠ 0`, a high-limb `destOffset` — to
  `.exit_outofgas`; and (ii) an `ld`/`or`/`or`/`bnez` check sending a high-limb
  *source offset* (`dataOffset` limbs 1–3) to `.exit_invalid`. The triple is a
  statement about that excised image, so it describes only the path on which
  those guards fall through; on operands with nonzero high limbs the emitted
  handler exits before this body's postcondition is reached. Note the three
  bridging hypotheses `h_destOff`/`h_srcOff`/`h_sizeV`
  (`operand.getLimbN 0 = BitVec.ofNat 64 n`) are **naming** bridges from the
  stack limbs to the `Nat` offsets — they place no constraint on the high limbs
  and are not where this residual lives. Closing it means modeling those blocks
  in the guard image (shifting every guard branch offset) or proving the
  framed-out region. CALLDATACOPY carries the same class of residual — its
  source-offset normalization block is likewise `preBody` glue.

  *Why each excised guard is safe to excise — three different arguments, none of
  them in the proof.* Read this before treating a `RETURNDATACOPY: proven` row as
  covering wide operands; the justifications do not share a shape:

  | assumed by | justified by | holds at `size = 0`? | reasoning lives in |
  |---|---|---|---|
  | high-limb `size` | **gas** — `copy_gas_cost` and memory expansion both explode ⇒ `OutOfGasError` | yes | `EvmMemoryGas.lean` `memDynamicU256RangeOogGuardAsm` docstring |
  | high-limb `destOffset` | **gas, but conditional on `size ≠ 0`** — quadratic expansion ⇒ `OutOfGasError`; at `size = 0` `calculate_gas_extend_memory` `continue`s and charges nothing, so the spec *accepts* it | **no — spec accepts** | same docstring; the guard's `beqz <size>` ordering mirrors `gas.py`'s `if size == 0: continue` |
  | high-limb source offset (`dataOffset`) | **not gas** — the spec's explicit `Uint(start) + Uint(size) > ulen(return_data)` ⇒ `OutOfBoundsRead` | yes — rejecting is *required*, not over-strict | the `h_RETURNDATACOPY` comment in `Codegen/Programs/NoopReturnData.lean` |

  So each excised guard matches a real execution-specs outcome (Amsterdam
  `vm/instructions/environment.py`, `vm/gas.py`): excising them costs coverage
  but hides no divergence, and in particular the guest does **not** over-reject
  the `size = 0` / high-limb-`destOffset` case the spec accepts.
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
- **Per-opcode handler glue.** Even for `.proven` opcodes, the handler
  `preBody`/tail glue around the verified subroutine — gas accounting
  (`copyWordGasAsm`), MSIZE / memory-expansion bookkeeping
  (`updateActiveMemorySizeAsm`), OOG guards, and offset normalization — is
  unverified `.custom` asm (the CALLDATACOPY #9880 convention). A dedicated
  gas-glue verification track is deferred work; until it lands, the `.proven`
  tier certifies the opcode's data effect, not its gas/expansion glue.
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
    IO.println ""
    IO.println renderCorrespondence
