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
— the zero-triple gap is closed (that issue landed `rlp_item_span_spec_within`); \
long-list outer and non-SpanForm walked items are still uncovered",
       .infra "`rlp_item_size` covers short forms only — long string `0xb8`–`0xbf` \
and long list `0xf8`–`0xff` uncovered (`Correspondence.lean` `rlp_item_size`)",
       .infra "nested-list decode bridges: model-side strength mismatch CLOSED by the \
two-level split — `rlpItemDecode` stays the core's lenient span relation and \
`rlpItemDecodeStrictW` (`Rv64/RLP/WalkNextStrict.lean`) is the wrapper's relation \
with the recursive payload condition in its list arms, and the reverse bridge \
(`decodeAux` acceptance → wrapper relation, both arms) is proven there. \
⭐ TRANSCRIPTION NO LONGER BLOCKS THIS — both programs landed (that issue \
closed): `rlpWalkNextShared_prog` (`Codegen/Programs/RlpWalk.lean:162`) and \
`rlpValidatePayload_prog` (`:237`), each with its `_eq_prog` drift guard. \
⭐ The machine tie now exists for the NON-LIST half: \
`rlp_walk_next_shared_nonlist_strict_spec_within` \
(`Codegen/Programs/RlpWalkNextStrictTie.lean`) is a `cpsTripleWithin` over \
`rlpWalkNextShared_prog` at `GuestAddrs.rlp_walk_next_shared` (unioned with the \
proven lenient core) whose post carries `rlpItemDecodeStrictW` as a conclusion; \
the recursive-payload conjunct is discharged by the wrapper's own prefix load \
and `bltu t1, 0xc0`, not by a model bridge. STILL OPEN: the LIST arms, i.e. the \
runs that actually enter `rlp_validate_payload`. Those need a termination \
measure for the `shared → validate_payload → nested → shared` cycle, for which \
this repo has no precedent"],
    auditedAt := some "2026-08-12 @12129-staleness",
    note := "pure-Lean RLP ✅. ⚠️ NO EMBEDDED REGISTRY COUNTS HERE, deliberately: \
this note used to carry a hand-written decoder-registry tally and had drifted to \
being wrong on every figure in it (the live values move several times a day). The \
counts live in `Progress/Routines.lean` as `routineCount_eq`, \
`routineProvenCount_eq`, `routineConditionalCount_eq` and `routinePartlyCount_eq`, \
which are `decide`-checked and therefore CANNOT go stale — a wrong number there \
fails the build. Read them from there; `scripts/check-embedded-counts.sh` now \
enforces that this file does not restate them. `rlp_item_span_spec_within` \
(domainRestricted/machineOnly) landed, so the prior \"no machine triple\" blocker \
is gone; the domain gate remains. Other blockers unchanged (size long forms; \
nested-list span-vs-payload strength mismatch)" },
  { id := 4, name := "EVM interpreter loop on the decoded block",
    status := .blocked,
    blockedBy :=
       [.infra "no simulation bridge from dispatched handlers to the SpecRef \
interpreter. The one-opcode `h_ADD` pilot's FOUNDATION landed \
(`Codegen/Proofs/ExecuteSeamBridge.lean`: `guestExec` relation, \
`add_limb_result_eq_add`) and its issue closed; the one-step simulation itself is \
NOT claimed there. ⚠️ Its single blocker is representation: `.dispatch_loop` is \
emitted as a raw String (`Codegen/Dispatch.lean:1199`) and no `dispatchLoop_prog` \
exists, so the dispatch-step lemma is not statable. That is also why the \
per-opcode gas debit is unobservable to any triple — it EXISTS, at \
`Dispatch.lean:1208-1214` (loads `opcode_gas_costs`, compares `env+568`, \
`sub`/`sd`, table modelled at `Proofs/OpcodeTables.lean:229`), and is simply \
inside the untranscribed dispatcher. Ranked in `docs/4ch8f-transcription-queue.md`",
         .infra "`stage_system_call` has no machine post yet, and the \
`execution_requests_hash` hash-half compose is still open. (The \
validation-accept prefix landed domainRestricted; that work is DONE and its \
issue closed — the surviving dependency is the two items named here)",
         .infra "`assemble_execution_requests` machine triple + \
`requests_hash_verify` callWithin still open — not a residual dependency. (The \
Program conversion itself is DONE, byte-identity waived, ELF byte-identical; \
its issue closed)",
         .infra "`erh_hash_one` empty+nonempty tops under residual h_sha \
(shaCallWithinShape) landed; the discharge owner is a machine triple \
`zkvm_sha256_spec_within`, which STILL DOES NOT EXIST anywhere in the tree (its \
issue closed; the name appears only in prose). Representation is NOT the blocker \
— `zkvmSha256_prog` exists (`Codegen/Programs/HashBridge.lean:34`, 121 insns) and \
is already carried through `CodeReq.ofProg` in a landed proof. Four phase modules \
exist (`HashBridgeSha256{Setup,Block,Outer,Frame}`) with padding/digest/output \
explicitly deferred (`…Outer.lean:71`). ⚠️ For sizing: keccak needed 19 \
`HashBridgeKeccak*` modules to reach its top triple. Hash-half five-slot compose \
after validation_accept still open"],
      auditedAt := some "2026-08-12 @12129-staleness",
      note := "`InterpreterLoop.lean` + handler-table simulation ✅. Re-audited \
2026-08-10 (#11803): the previous blocker (\"codegen M5 (tiny EVM interpreter) \
not shipped\") cited SHIPPED work — PLAN.md:23 has listed M0–M10 done, including \
M5's runtime fetch/decode/dispatch and 91 wired opcodes, for weeks. The real gap \
is the simulation relation, which that row was hiding. #11578 lands \
`execution_requests_hash_validation_accept`; #12011 retargets consumer to \
`requests_hash_verify` (block_state_root has no jal erh) and lands assemble \
Program (String residual retired) + erh_hash_one under h_sha DEPENDENCY \
(not input gate); does not close `stage_system_call`" },
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
    blockedBy :=
      [.infra "55 accelerator-site bridges remain after the landed `zkvm_keccak256` \
pilot: secp256k1 recovery (0x01), BN254, P256VERIFY, BLS G1, and the curve/complex \
accelerator families 0x802–0x80A; the 56-site census is recorded in #10552 and the \
family inventory is `docs/4ch8f-crypto-kernel-inventory.md`; the 56 figure counts \
decoded CSRRS encodings, while that inventory's 64 counts raw pre-encoded `.4byte` \
sites, so the two populations are not yet reconciled"],
    auditedAt := some "2026-08-11 @84e000579",
    note := "Pilot landed: `EvmAsm.Codegen.Proofs.zkvm_keccak256_spec_within` in \
`HashBridgeKeccakTop.lean:283`, a genuine accelerator-site triple. One site is \
covered; the other 55 sites and the remaining accelerator families are still open." },
  -- Audited as part of #11803. Not one of the rows that issue named, but the
  -- same defect class pointing the other way: a row understating its own
  -- progress hides that the work is startable, which is just as misleading to
  -- something steering by this matrix.
  { id := 7, name := "MPT verification of pre-state witness proofs",
    status := .blocked,
    blockedBy :=
      [.infra "trie-walk loop spec for `mpt_walk` over `mptNodeIs`/`nodeDbIs` \
against `trieLookup` — arm pieces + kind callWithin landed (that issue closed); \
the surviving residual is the callee `witness_lookup_by_hash` machine triple \
for the HIT/general domain, tracked at #12036. TRANSCRIPTION DONE (PR 12111) \
and the empty-section miss triple landed (#12036). Both `wlCallWithinShape` \
repairs are now DONE: walk `fullCode` unions `wlhCr` (#12152), and the six \
`wlh_*` telemetry cells join `wlCallEntry`/`wlCallReturn` (#12162), so the \
generic residual is SATISFIABLE rather than vacuous. PRODUCTION empty-miss \
at walk sites is now enable=1: `wlCallWithinShapeEn` + three discharges \
`root/branch/ext_wl_enabled_empty_establishes_shape` via \
`wlhCallWithin_enabled_empty` over the enabled_empty top (#12183). Nested \
stack needs `stackFree sp0 16` (SAY SO). LEGACY enable=0 three-site \
`MptWalkWlEmpty` kept. The hit residual (`wlCallWithinShapeHit`) remains a \
DEPENDENCY. `hp_decode_nibbles` and setup/root are RETIRED.",
        .infra "machine triple `witness_lookup_by_hash_spec_within` at \
GuestAddrs.witness_lookup_by_hash for the GENERAL/HIT domain — production \
empty-miss enable=1 is proved and consumed at three walk sites (#12183); \
what remains is the indexed hit/binary-search path plus contracts for \
cross-jal callees on non-empty domains (`zkvm_keccak256`, \
`witness_lookup_by_hash_indexed` general loop)",
        .infra "witness-ingest DB builder triples against \
`build_node_db`/`build_code_db` (#11800)",
        .infra "three-tier resolve coherence (appended DB / resolve cache / \
witness section) vs SpecRef's single node source — where `resolveCacheValidIs` \
(`Evm64/MptAssertions.lean`) earns its keep"],
    auditedAt := some "2026-08-12 @12183-enable-restate",
    note := "Re-audited 2026-08-12 (#12183): production empty-miss residual \
restated onto enable=1 with three-site discharge under walk fullCode; nested \
sf16 SAY SO. Hit residual remains DEPENDENCY. mpt_node_kind and hp_decode are \
`.proven`. Overlaps obligation 10" },
  -- #12130: FIRST audit of this row. It was the only `blocked` obligation with
  -- no `auditedAt` at all — pure indirection ("blocked on 4+5+6+7"), which hides
  -- the blockers that are NOT any of those four. Two of them are now named.
  { id := 8, name := "Verified post-state root → public output",
    status := .blocked,
    blockedBy :=
      [.infra "obligation #4 (interpreter loop)",
       .infra "obligation #5 (opcode coverage)",
       .infra "obligation #6 (accelerator bridges)",
       .infra "obligation #7 (MPT verification)",
       .infra "guest-image `CodeReq` coverage: `guestImageCodeReq` pins only \
PART of `.text` — for the current byte counts and percentage read the generated \
`docs/4ch8f-guest-image-coverage.md` (§1 Summary), produced by \
`scripts/guest_image_coverage.py`; it is NOT the coverage-floor constant. This \
cell used to quote the figures inline and two of the three literals had gone \
stale, which is the class `scripts/check-obligation-claims.sh` now gates. A \
`cr` that does not pin an address the run executes makes the triple FALSE, \
not weak — \
`Codegen/Proofs/TopComposition.lean:cpsTripleWithin_needs_entry_code` proves \
the entry-address case. So this obligation cannot be closed at the image \
CodeReq until coverage is complete (incl. unconverted `_start`), independently \
of 4/5/6/7",
       .infra "framing footprint: `guestFraming` now owns the measured halt-\
boundary registers x5, x10 and x17 in BOTH `scratch` and `residue`. The \
generic forcing lemmas still apply to any register omitted by a framing, but \
the unconverted `_start` shell remains the inherited whole-image clobber \
residual (#12166), so this narrow boundary set is not yet a complete image \
clobber theorem",
       .infra "the composition itself is NO LONGER a blocker: \
`TopComposition.lean:runStatelessGuestSound_of_phases` proves \
`runStatelessGuestSound` from six named phase hypotheses, and \
`runStatelessGuestSound_demo` shows that family is jointly satisfiable \
(so it is not a vacuous implication)"],
    auditedAt := some "2026-08-12 @12130",
    note := "Audited 2026-08-12 (#12130), first time ever. The row said only \
\"blocked on 4+5+6+7\"; that was incomplete — image-CodeReq coverage and the \
register-free framing bundle block it on their own. The sequencing/halt-wrap \
half is now DONE (six named phase hypotheses, jointly satisfiable); what \
remains is discharging those six and repairing the two framing/coverage \
defects above" },
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
      [ .infra "bal_canonical_sort ordering + permutation — the digit extractor's \
descriptor↔semantic-key agreement landed (that issue closed); the remaining \
blocker is the `.Lbalsort_pop` work-list loop's lexicographic measure, which has \
no precedent anywhere in `EvmAsm/Codegen/Proofs/`. ⚠️ Key uniqueness is a \
PRECONDITION discharged by the producer, and it is discharged for only 2 of the \
6 live sort call sites (#12102)",
         .infra "trie-walk loop spec for `mpt_walk` over mptNodeIs/nodeDbIs \
against trieLookup — arm pieces + kind callWithin + path-preserve landed (that \
issue closed); residual only hit/general `witness_lookup_by_hash` machine \
(#12036). Both `wlCallWithinShape` repairs are DONE (#12152, #12162), so the \
generic residual is satisfiable rather than vacuous. The three empty-section \
discharges at walk sites are on the production-UNREACHABLE \
`section_len = 0`/`widx_enabled = 0` domain per #12183; discharged and \
satisfiable is not the same as reached. The informative indexed domain is \
`widx_enabled = 1`, tracked at #12181 with a count-0 callee triple now existing. \
hp_decode_nibbles and setup/root are RETIRED. Three-tier resolve divergence \
stated in docs/4ch8f-slstate-specref-correspondence.md:164",
         .infra "machine triple `witness_lookup_by_hash_spec_within` (#12036) — \
transcription landed (PR 12111) and the `section_len = 0` whole-routine triple is \
proved and consumed at the empty-section walk sites (#12162). Remaining: the \
indexed linear scan loop at a symbolic trip count + contracts for \
`zkvm_keccak256` and `witness_lookup_by_hash_indexed` in the informative \
`widx_enabled = 1` domain (#12181)",
         .infra "witness-ingest DB builder triples against \
build_node_db/build_code_db (#11800)",
         .infra "no `cpsTripleWithin` for `witness_codes_index_build` / \
`witness_codes_lookup_by_hash` — the code-DB *routines*. The predicate side is \
DONE and its issue closed; only the routine triples remain" ],
    auditedAt := some "2026-08-12 @12162-wl-ambient",
    note := "⭐ THE SOUNDNESS CORE OF STATELESSNESS (#11579). Re-audited \
2026-08-12 (#12162): both wlCallWithinShape repairs are DONE, so the generic \
residual is satisfiable rather than vacuous; the three empty-section discharges \
are on the production-UNREACHABLE `section_len = 0`/`widx_enabled = 0` domain per \
#12183, and satisfiable-and-discharged is not the same as reached. The informative \
indexed `widx_enabled = 1` domain is tracked at #12181 with a count-0 callee \
triple now existing; hit wl remains a DEPENDENCY. Spine: input deserialize (done) \
-> node/code DB build -> trie walk (loop spec landed, residual wl hit at #12036) \
-> mpt_node_kind \
`.proven` -> hp_decode_nibbles `.proven` -> nibble path (bytes_to_nibbles done, \
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
