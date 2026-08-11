/-
  EvmAsm.Progress.Obligations

  Kernel-checked tracker for the **ten guest-program obligations** that
  "evm-asm is a complete L1 stateless block-validation guest program" must
  satisfy (Phase 2 of the agent-progress-steering rollout, report R-A1).

  Where `EvmAsm.Progress` answers *"how deep is each opcode proven?"*, this
  module answers the orthogonal *direction* question: *"am I on track to finish
  the obligations, and which opcodes/infra block each one?"* Opcode-tier counts
  alone cannot say "obligation #5 (full opcode coverage) is blocked by the three
  `.conditional` terminating opcodes and the 14 `.execSpec` rows"; this matrix
  can.

  What is kernel-checked here:
  * the per-status obligation counts (`by decide`), exactly like the tier counts
    in `Progress.lean`;
  * a cross-reference theorem (`blocker_opcodes_in_registry`) asserting every
    `Blocker.opcode` mnemonic is a real `Progress.registry` entry name — so a
    renamed/deleted opcode fails this file's elaboration rather than silently
    leaving a dangling blocker;
  * `no_proven_opcode_blockers`, asserting no `Blocker.opcode` names an entry
    that already reached `.proven`. Existence alone was not enough: #11803 found
    obligation 5 citing eight opcodes that had all been proven for weeks, which
    the existence check happily accepted.

  **A blocker list is a claim about the present, and it decays.** The two
  defects #11803 found were a row citing a shipped codegen milestone and a row
  citing finished opcodes; a third (obligation 7) claimed "not started" about
  work with three axiom-gated lemmas behind it. `no_proven_opcode_blockers`
  makes the opcode-valued half of that decay a build failure; the `infra`-valued
  half cannot be gated the same way (the labels are free text by design), so
  those rows carry `auditedAt` instead — a date + commit that lets the next
  reader see the age of the claim rather than re-deriving the audit.

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
  /-- When this row's `blockedBy`/`status` was last checked against the live
      registries, as `"YYYY-MM-DD @<commit>"`. A blocker list is a *claim about
      the present*, and #11803 showed the failure mode: obligation 4 cited a
      shipped codegen milestone and obligation 5 named eight already-`.proven`
      opcodes, with nothing in the row to reveal how old the claim was. Rendered
      into the matrix so the next reader can tell a fresh row from a stale one
      without re-deriving the audit. `none` = never audited since this field
      was introduced. -/
  auditedAt : Option String := none
  deriving Repr

/-! ## The nine obligations

    Source: the "What 'evm-asm is a complete guest program' means" table that
    previously lived hand-maintained in `scripts/progress-template.md`. This is
    now the single source of truth; the template renders from here. -/

def obligations : List Obligation := [
  { id := 1, name := "RV64 ELF for `riscv64im_zicclsm-unknown-none-elf`",
    status := .blocked,
    blockedBy := [.infra "codegen emits `rv64imac` (one extension off `zicclsm`)"],
    auditedAt := some "2026-08-10 @372162cc2",
    note := "substrate ✅; codegen target one extension off. Re-audited 2026-08-10 \
(#11803) and still accurate: `Codegen/Driver.lean:82` assembles with \
`-march=rv64imac`, as do `scripts/codegen-eest-stateless-check.sh:809,1222` and \
`scripts/codegen-zisk-stateless-verdict-debug-smoke.sh:93`" },
  { id := 2, name := "`read_input` / `write_output` per the IO interface",
    status := .done,
    witness := some "Rv64/SyscallSpecs.lean (codegen M4 wired)",
    note := "verified syscall specs; codegen M4 wired" },
  { id := 3, name := "RLP-decode the (block, witness) input",
    status := .blocked,
    blockedBy :=
      [.infra "`rlp_item_span` is `.conditional` short-list+WalkedSpanForm only \
(#11577 closed the zero-triple gap; long-list outer and non-SpanForm walked \
items still uncovered)",
       .infra "`rlp_item_size` covers short forms only — long string `0xb8`–`0xbf` \
and long list `0xf8`–`0xff` uncovered (`Correspondence.lean` `rlp_item_size`)",
       .infra "nested-list decode bridges: `rlpItemDecode`'s list arms check a \
span fit and say nothing about the payload, while `decodeAux` rejects a malformed \
interior — a strength mismatch, tracked at #11795 with the relation-side decision \
scoped at #11898"],
    auditedAt := some "2026-08-10 @11577",
    note := "pure-Lean RLP ✅; the RV64 decoder registry is 36 rows / 26 proven / \
10 conditional / 0 partly (`Progress/Routines.lean`). #11577 landed \
`rlp_item_span_spec_within` (domainRestricted/machineOnly) — the prior \
\"no machine triple\" blocker is gone; the domain gate remains. Other blockers \
unchanged (size long forms; nested-list span-vs-payload strength mismatch)" },
  { id := 4, name := "EVM interpreter loop on the decoded block",
    status := .blocked,
    blockedBy :=
       [.infra "no simulation bridge from dispatched handlers to the SpecRef \
interpreter — #11801 is the one-opcode `h_ADD` pilot for that bridge",
        .infra "`stage_system_call` has no machine post yet; #11578 rescoped off \
derive_* shims (NOT leaves) to `execution_requests_hash` validation-accept \
prefix (landed domainRestricted); hash half + stage_system_call still residual"],
     auditedAt := some "2026-08-11",
     note := "`InterpreterLoop.lean` + handler-table simulation ✅. Re-audited \
2026-08-10 (#11803): the previous blocker (\"codegen M5 (tiny EVM interpreter) \
not shipped\") cited SHIPPED work — PLAN.md:23 has listed M0–M10 done, including \
M5's runtime fetch/decode/dispatch and 91 wired opcodes, for weeks. The real gap \
is the simulation relation, which that row was hiding. #11578 lands \
`execution_requests_hash_validation_accept` (parked until block_state_root + \
requests_hash_verify port); does not close `stage_system_call`" },
  { id := 5, name := "Full opcode coverage with verified handlers",
    status := .blocked,
    blockedBy :=
      [.opcode "RETURN", .opcode "REVERT", .opcode "SELFDESTRUCT",
       .infra "14 `.execSpec` entries have no RV64 subroutine (axis A.2): \
KECCAK256, BALANCE, EXTCODESIZE, EXTCODECOPY, EXTCODEHASH, SLOAD, SSTORE, \
LOG0..4, CREATE, CALL, CALLCODE, DELEGATECALL, CREATE2, STATICCALL"],
    auditedAt := some "2026-08-10 @372162cc2",
    note := "Re-audited 2026-08-10 (#11803): every one of the eight opcodes this \
row used to name — MOD, SDIV, SMOD, ADDMOD, MULMOD, EXP, CALLDATACOPY, \
PUSH2..32 — is now `.proven`, and `partialCount = notStartedCount = 0`, so the \
old note's \"`b.getLimbN 3 = 0` (n=4 uncovered)\" caveat is also retired (DIV/MOD \
are full-domain v6). What remains is exactly the 3 `.conditional` terminating \
opcodes plus the 14 `.execSpec` rows. `no_proven_opcode_blockers` below now \
fails the build if a `.proven` opcode is ever listed here again" },
  { id := 6, name := "Accelerator ECALL bridges per `zkvm_accelerators.h`",
    status := .blocked,
    blockedBy := [.infra "per-precompile EL bridges not yet codegen-wired"],
    note := "vendored header + EL bridges; not codegen-wired" },
  -- Audited as part of #11803. Not one of the rows that issue named, but the
  -- same defect class pointing the other way: a row understating its own
  -- progress hides that the work is startable, which is just as misleading to
  -- something steering by this matrix.
  { id := 7, name := "MPT verification of pre-state witness proofs",
    status := .blocked,
    blockedBy :=
      [.infra "trie-walk loop spec for `mpt_walk` over `mptNodeIs`/`nodeDbIs` \
against `trieLookup` (#11799)",
       .infra "witness-ingest DB builder triples against \
`build_node_db`/`build_code_db` (#11800)",
       .infra "three-tier resolve coherence (appended DB / resolve cache / \
witness section) vs SpecRef's single node source — where `resolveCacheValidIs` \
(`Evm64/MptAssertions.lean`) earns its keep"],
    auditedAt := some "2026-08-10 @372162cc2",
    note := "Re-audited 2026-08-10 (#11803): was `.notStarted` with no blockers, \
which understated real progress. The MPT assertion vocabulary exists \
(`Evm64/MptAssertions.lean`) and three of its lemmas are already axiom-gated — \
`nodeDbIs_snoc`, `nodeDbLookupSpec_eq_build_node_db`, `rlpToMutableNode_rlp` \
(`Progress/AxiomWitnesses.lean`) — with #11347 (`mpt_node_kind`) and #11422 \
(`compact_to_nibbles`) closed. Work has begun and the remaining steps are \
enumerable, which is `.blocked`, not `.notStarted`. Overlaps obligation 10, \
which consumes the same two triples from the witness-read side" },
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
  -- triples. Its blockers ARE the open leaf issues; each one closing moves this
  -- row, which is the point — so a closed issue must be REMOVED from the list,
  -- not left to pad it (three had been, until #11803's audit).
  { id := 10, name := "Witness reads are sound (get_account_optional composition)",
    status := .blocked,
    blockedBy :=
      [ .infra "account_decode ↔ decode_account_from_leaf (#11345)",
        .infra "bal_canonical_sort ordering + permutation (#10817)",
        .infra "trie-walk loop spec for `mpt_walk` over mptNodeIs/nodeDbIs \
against trieLookup (#11799) — carries the three-tier resolve (appended DB / \
resolve cache / witness section) vs SpecRef's single node source; divergence \
stated in docs/4ch8f-slstate-specref-correspondence.md:164",
        .infra "witness-ingest DB builder triples against \
build_node_db/build_code_db (#11800)",
        .infra "no `cpsTripleWithin` for `witness_codes_index_build` / \
`witness_codes_lookup_by_hash` — the code-DB *routines* (the predicate side is \
done; see #11573 / PR #11902)" ],
    auditedAt := some "2026-08-10 @04de93895",
    note := "⭐ THE SOUNDNESS CORE OF STATELESSNESS (#11579). Re-audited \
2026-08-10 (#11803): three blockers dropped as CLOSED — #11346 \
(account_is_eip161_empty), #11347 (mpt_node_kind) and #11422 \
(compact_to_nibbles) — and the two former no-issue-number \"connective gap\" \
blockers now cite the issues #11579 asked to be filed once their premises \
closed: #11799 (trie walk) and #11800 (DB builders). ⚠️ CORRECTING MY OWN \
BLOCKER from that same audit: it read \"codeDbIs predicate for code_db_buckets \
(#11573)\", and both halves were wrong. `codeDbIs` has existed since \
`73c8ea6a6` (2026-07-05, `Evm64/WitnessAssertions.lean`), a month before #11573 \
was filed; and `code_db_buckets` is a DEAD scheme-A anchor whose only mention in \
the tree is `Codegen/RegionMap.lean:198` — no emitted instruction references it, \
so no predicate was ever going to be built over it. I took #11573's premise on \
trust instead of checking the tree, which is the same class of error the #11803 \
audit was fixing. The live gap is the code-DB *routines* \
(`witness_codes_index_build` / `witness_codes_lookup_by_hash`, raw asm with \
whole-guest byte-identity pins and no triple), which is what the blocker now \
says. A wrong witness read \
is the false-ACCEPT shape directly: #11508's four witness-missing accepts, \
#11522's untouched-leaf bytes, #11523's non-canonical leaves. Everything \
downstream (state tracker, verdict) consumes what this spine produces, and \
bv_fail=1 (terminal state-root, 447 of 582 rows in #11542) is where its \
divergences surface unlocalized -- stated triples along the spine turn those \
investigations from re-derivation into citation. Spine: input deserialize (done) \
-> node/code DB build -> trie walk (#11799 open) -> mpt_node_kind machine \
`.proven` (#11799 dep landed) -> nibble path (bytes_to_nibbles done, \
compact_to_nibbles closed #11422) -> account_decode -> EIP-161 classification. \
Summit is SpecRef/WitnessReads.lean's get_account_optional" },
]

/-! ## Counts (kernel-checked) -/

def countStatus (s : ObligationStatus) : Nat :=
  obligations.countP (fun o => o.status == s)

def doneCount       : Nat := countStatus .done
def blockedCount    : Nat := countStatus .blocked
def notStartedCount : Nat := countStatus .notStarted
def totalObligations : Nat := obligations.length

theorem doneCount_eq        : doneCount        = 2 := by decide
theorem blockedCount_eq     : blockedCount     = 8 := by decide
theorem notStartedCount_eq  : notStartedCount  = 0 := by decide
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

/-! ## Cross-check: no `.opcode` blocker names an already-`.proven` opcode

    `blocker_opcodes_in_registry` above checks that a blocker mnemonic *exists*
    in the registry. #11803 showed that is not enough: it kept passing for weeks
    while obligation 5 listed eight opcodes — MOD, SDIV, SMOD, ADDMOD, MULMOD,
    EXP, CALLDATACOPY, PUSH2..32 — that had every one reached `.proven`. The
    names were all real, so the existing gate had nothing to say.

    A blocker naming finished work is worse than a missing blocker: it makes the
    dashboard read as "this obligation is further from done than it is" *and*
    hides whatever genuinely blocks it behind plausible-looking rows. Promote the
    property to a build-checked one, in the spirit of `AGENTS.md`'s architecture
    fitness functions — when a convention starts to matter, gate it rather than
    restating it in prose an agent can ignore.

    Deliberately keyed on `.proven` only: `.conditional` and `.execSpec` opcodes
    are legitimate blockers (obligation 5 names three `.conditional` ones), and
    `.partly`/`.notStarted` are even more so. -/

/-- Blocker mnemonics whose registry entry has already reached `.proven` — i.e.
    stale blockers citing finished work. Must stay empty. -/
def staleOpcodeBlockers : List String :=
  blockerOpcodeNames.filter (fun m =>
    match registry.find? (fun e => e.name == m) with
    | some e => e.tier == .proven
    | none   => false)

/-- No obligation is blocked by an opcode that is already `.proven`. Fails the
    build when an opcode reaches `.proven` and its blocker row is not cleared —
    the #11803 staleness class. -/
theorem no_proven_opcode_blockers : staleOpcodeBlockers = [] := by decide

/-- Ids are exactly 1..10, in order (guards against a copy-paste id collision). -/
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
