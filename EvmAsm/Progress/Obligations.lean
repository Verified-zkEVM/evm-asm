/-
  EvmAsm.Progress.Obligations

  Kernel-checked tracker for the **nine guest-program obligations** that
  "evm-asm is a complete L1 stateless block-validation guest program" must
  satisfy (Phase 2 of the agent-progress-steering rollout, report R-A1).

  Where `EvmAsm.Progress` answers *"how deep is each opcode proven?"*, this
  module answers the orthogonal *direction* question: *"am I on track to finish
  the obligations, and which opcodes/infra block each one?"* Opcode-tier counts
  alone cannot say "obligation #5 (full opcode coverage) is blocked by DIV/MOD
  full `n=4`"; this matrix can.

  What is kernel-checked here:
  * the per-status obligation counts (`by decide`), exactly like the tier counts
    in `Progress.lean`;
  * a cross-reference theorem (`blocker_opcodes_in_registry`) asserting every
    `Blocker.opcode` mnemonic is a real `Progress.registry` entry name — so a
    renamed/deleted opcode fails this file's elaboration rather than silently
    leaving a dangling blocker.

  What is *not* kernel-forced: the `witness` pointer on a `done` obligation is a
  human-readable reference (module/theorem), not an `abbrev`-checked witness like
  `proofRef` in `Progress.lean` — the closure conditions (e.g. "halt convention
  holds") are not single named theorems. The honest kernel-checked content is the
  counts + the opcode cross-check.

  See `MainProgress.lean` for the rendered "obligation × blocker" matrix and the
  generated `DRIFT.md` TCB ledger.
-/

import EvmAsm.Progress

namespace EvmAsm.Progress.Obligations

open EvmAsm.Progress

/-- Direction status of one guest-program obligation. Deliberately three-valued
    (mirrors `ProofTier` conventions): an in-progress obligation with remaining
    blockers is `blocked`, not `done`. -/
inductive ObligationStatus
  /-- Closure condition met; no remaining blockers. -/
  | done
  /-- Has known remaining blockers (opcodes or infra). Covers both
      actively-in-progress and not-yet-begun-but-dependency-pinned obligations. -/
  | blocked
  /-- No work begun and no blockers enumerated yet. -/
  | notStarted
  deriving DecidableEq, BEq, Repr

/-- A single thing standing between an obligation and `done`. Split so the
    opcode-valued blockers can be kernel-cross-checked against the registry,
    while free-form infrastructure/milestone blockers stay legible. -/
inductive Blocker
  /-- An EVM opcode that is not yet fully verified. `mnemonic` MUST be a
      `Progress.registry` entry `name` (enforced by `blocker_opcodes_in_registry`). -/
  | opcode (mnemonic : String)
  /-- A non-opcode blocker: codegen milestone, decoder phase, host bridge, etc. -/
  | infra (label : String)
  deriving DecidableEq, BEq, Repr

/-- Render a blocker for the markdown matrix. -/
def Blocker.render : Blocker → String
  | .opcode m => s!"`{m}`"
  | .infra l  => l

/-- One guest-program obligation. -/
structure Obligation where
  /-- Obligation number, 1–9 (stable identity used in prose cross-references). -/
  id : Nat
  /-- Short obligation name. -/
  name : String
  /-- Direction status. -/
  status : ObligationStatus
  /-- What must land before this obligation is `done`. Empty for `done`. -/
  blockedBy : List Blocker := []
  /-- For a `done` obligation: human-readable pointer to where the closure
      condition is discharged (module/theorem). NOT an `abbrev`-checked witness. -/
  witness : Option String := none
  /-- Richer one-line status prose carried verbatim into the matrix. -/
  note : String := ""
  deriving Repr

/-! ## The nine obligations

    Source: the "What 'evm-asm is a complete guest program' means" table that
    previously lived hand-maintained in `scripts/progress-template.md`. This is
    now the single source of truth; the template renders from here. -/

def obligations : List Obligation := [
  { id := 1, name := "RV64 ELF for `riscv64im_zicclsm-unknown-none-elf`",
    status := .blocked,
    blockedBy := [.infra "codegen emits `rv64imac` (one extension off `zicclsm`)"],
    note := "substrate ✅; codegen target one extension off" },
  { id := 2, name := "`read_input` / `write_output` per the IO interface",
    status := .done,
    witness := some "Rv64/SyscallSpecs.lean (codegen M4 wired)",
    note := "verified syscall specs; codegen M4 wired" },
  { id := 3, name := "RLP-decode the (block, witness) input",
    status := .blocked,
    blockedBy := [.infra "RV64 RLP decoder phases 1–3 (in progress)"],
    note := "pure-Lean RLP ✅; RV64 decoder in progress" },
  { id := 4, name := "EVM interpreter loop on the decoded block",
    status := .blocked,
    blockedBy := [.infra "codegen M5 (tiny EVM interpreter) not shipped"],
    note := "`InterpreterLoop.lean` + handler-table simulation ✅; codegen M5 pending" },
  { id := 5, name := "Full opcode coverage with verified handlers",
    status := .blocked,
    blockedBy :=
      [.opcode "MOD", .opcode "SDIV",
       .opcode "SMOD", .opcode "ADDMOD", .opcode "MULMOD", .opcode "EXP",
       .opcode "CALLDATACOPY", .opcode "PUSH2..32",
       .infra "execSpec-tier opcodes have no RV64 subroutine (axis A.2)"],
    note := "MOD/SDIV proven only on `b.getLimbN 3 = 0` (n=4 uncovered); see axis A.2" },
  { id := 6, name := "Accelerator ECALL bridges per `zkvm_accelerators.h`",
    status := .blocked,
    blockedBy := [.infra "per-precompile EL bridges not yet codegen-wired"],
    note := "vendored header + EL bridges; not codegen-wired" },
  { id := 7, name := "MPT verification of pre-state witness proofs",
    status := .notStarted,
    note := "not started" },
  { id := 8, name := "Verified post-state root → public output",
    status := .blocked,
    blockedBy :=
      [.infra "obligation #4 (interpreter loop)",
       .infra "obligation #5 (opcode coverage)",
       .infra "obligation #6 (accelerator bridges)",
       .infra "obligation #7 (MPT verification)"],
    note := "blocked on 4 + 5 + 6 + 7" },
  { id := 9, name := "Halt convention per `standard-termination-semantics`",
    status := .done,
    witness := some "`--halt linux93` default; docs/host-io-halt-convention.md",
    note := "halt convention implemented + documented" },
  -- #11579: the witness-read spine's summit. Registered as an obligation so
  -- PROGRESS.md shows the spine's burn-down rather than a flat count of leaf
  -- triples. Its blockers ARE the open leaf issues plus the two connective gaps
  -- that issue names; each one closing moves this row, which is the point.
  { id := 10, name := "Witness reads are sound (get_account_optional composition)",
    status := .blocked,
    blockedBy :=
      [ .infra "account_decode ↔ decode_account_from_leaf (#11345)",
        .infra "account_is_eip161_empty ↔ account_exists_and_is_empty (#11346)",
        .infra "mpt_node_kind ↔ _decode_witness_node dispatch (#11347)",
        .infra "compact_to_nibbles flag decode (#11422)",
        .infra "bal_canonical_sort ordering + permutation (#10817)",
        .infra "trie-walk loop spec over mptNodeIs/nodeDbIs — the three-tier \
resolve (appended DB / resolve cache / witness section) vs SpecRef's single node \
source; divergence stated in docs/4ch8f-slstate-specref-correspondence.md:164",
        .infra "node/code DB build routines (no spec yet; codeDbIs is #11573)" ],
    note := "⭐ THE SOUNDNESS CORE OF STATELESSNESS (#11579). A wrong witness read \
is the false-ACCEPT shape directly: #11508's four witness-missing accepts, \
#11522's untouched-leaf bytes, #11523's non-canonical leaves. Everything \
downstream (state tracker, verdict) consumes what this spine produces, and \
bv_fail=1 (terminal state-root, 447 of 582 rows in #11542) is where its \
divergences surface unlocalized -- stated triples along the spine turn those \
investigations from re-derivation into citation. Spine: input deserialize (done) \
-> node/code DB build -> trie walk -> mpt_node_kind -> nibble path \
(bytes_to_nibbles done, compact_to_nibbles open) -> account_decode -> EIP-161 \
classification. Summit is SpecRef/WitnessReads.lean's get_account_optional" },
]

/-! ## Counts (kernel-checked) -/

def countStatus (s : ObligationStatus) : Nat :=
  obligations.countP (fun o => o.status == s)

def doneCount       : Nat := countStatus .done
def blockedCount    : Nat := countStatus .blocked
def notStartedCount : Nat := countStatus .notStarted
def totalObligations : Nat := obligations.length

theorem doneCount_eq        : doneCount        = 2 := by decide
theorem blockedCount_eq     : blockedCount     = 7 := by decide
theorem notStartedCount_eq  : notStartedCount  = 1 := by decide
theorem totalObligations_eq : totalObligations = 10 := by decide

/-! ## Cross-check: every opcode blocker names a real registry entry

    Keeps the obligation tracker honest against `Progress.registry` drift: if an
    opcode is renamed or removed from the registry, the `.opcode` blocker here
    becomes a dangling reference and this `by decide` theorem fails, breaking the
    build (the obligations analogue of `Progress.lean`'s witness `abbrev`s). -/

/-- The mnemonics named by every `Blocker.opcode` across all obligations. -/
def blockerOpcodeNames : List String :=
  (obligations.flatMap (·.blockedBy)).filterMap
    (fun b => match b with | .opcode m => some m | .infra _ => none)

/-- The set of registry entry names. -/
def registryNames : List String := registry.map (·.name)

theorem blocker_opcodes_in_registry :
    blockerOpcodeNames.all (fun m => registryNames.contains m) = true := by
  decide

/-- Ids are exactly 1..9, in order (guards against a copy-paste id collision). -/
theorem obligation_ids_eq : obligations.map (·.id) = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  decide

/-- A `done` obligation must carry a `witness` pointer and have no remaining
    blockers. This is **not** a kernel proof of closure — `witness` is a
    human-readable pointer, not an `abbrev`-checked theorem (see the module
    docstring). What it buys: flipping a status to `done` no longer slips through
    as a one-token tier edit; the agent must *also* fabricate a witness string
    and clear the blocker list, a larger and more review-visible diff in a file
    the tamper scan already watches. Combined with the `…Count_eq` theorems
    (which force the matching count literal to change too), a false-green
    `done` flip can't be silent. -/
theorem done_obligations_well_formed :
    (obligations.filter (fun o => o.status == .done)).all
      (fun o => o.witness.isSome && o.blockedBy.isEmpty) = true := by
  decide

end EvmAsm.Progress.Obligations
