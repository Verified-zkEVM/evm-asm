/-
  EvmAsm.Progress.Correspondence

  Kernel-checked registry of **spec-correspondence verdicts**: for each audited
  guest routine, whether the Lean spec proven about it agrees with the external
  reference implementation, and on what evidence.

  Where `EvmAsm.Progress` answers *"how deep is each opcode proven?"* and
  `EvmAsm.Progress.Obligations` answers *"which obligations remain?"*, this
  module answers a third, orthogonal question: **does a proven routine prove the
  right thing?** A whole-routine Hoare triple ties RISC-V to the Lean spec beside
  it and says nothing about whether that spec matches the reference. Stricter than
  the reference ⇒ false-rejects on valid chain data; looser ⇒ a false-accept, the
  one gate that never relaxes (`docs/agents/spec-alignment-doctrine.md` §2).

  Method: `docs/agents/spec-correspondence.md`.
  Per-family findings and prose: `docs/<family>-spec-correspondence.md`.

  What is kernel-checked here:
  * the per-verdict and per-basis counts (`by decide`), as in `Progress.lean`;
  * `no_looser_verdicts` — the soundness invariant, stated so that recording a
    `looser` row fails elaboration until someone deliberately amends the theorem
    (a divergence should not be able to land quietly);
  * `verdict_requires_spec` — a routine with no spec cannot carry a verdict other
    than `unproven`/`noCounterpart`, since the question is unanswerable without a
    spec;
  * `basis_diff_requires_spec` — a `diff`-graded row must name a spec;
  * `portDefect_cites_issue` — a row blaming the `SpecRef` port must name the
    issue tracking that defect, so "the port is wrong" cannot be asserted without
    something to fix it against. Note this is a field, not a verdict: `Verdict`
    grades the guest, and keeping the port on its own axis is what stops a
    false-accept from being graded around `no_looser_verdicts`;
  * the **`abbrev` witnesses at the bottom**, which make every `spec` string real:
    renaming or deleting a named theorem fails this file's elaboration rather than
    silently leaving a stale row. This is the same device as
    `Progress.lean`'s witness block and is the whole reason this registry exists
    in Lean rather than in markdown.

  What is *not* kernel-forced: the `verdict` and `basis` values themselves. Those
  are human judgements backed by the evidence named in `note` — for `diff` rows,
  by `lake exe correspondence-check <family>`. The registry records and drift-gates
  them; it cannot derive them.

  NOTE ON BUILD COST: this module is in the **heavy** tier — it must import the
  proof modules in order to witness their theorems. The correspondence *harness*
  (`EvmAsm/Tests/Correspondence/Harness.lean`) is deliberately Mathlib-free so it
  can gate per-PR; do not confuse the two.
-/

import EvmAsm.Progress
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.RLP.ContentToU256Be
import EvmAsm.Rv64.RLP.ContentToU256BeBridge

namespace EvmAsm.Progress.Correspondence

/-! ### Grading a restriction: ask *whose* limit it is

    Every non-`agrees` verdict answers one question — **which side is limited?** —
    and the four answers are not interchangeable:

    | limit lives in | verdict | is it a defect? |
    |---|---|---|
    | the **proof** (we did not cover the case) | `domainRestricted` | no — prove more |
    | the **triple's precondition** (the ABI obliges the caller) | `domainRestricted` | no, but it can be *violated* |
    | the **guest** (it refuses input the spec accepts) | `stricter` | **yes, guest-side** |
    | the **port** (it accepts input the Python rejects) | `portDefect` field | **yes, reference-side** |

    ⚠️ The last row is **not a verdict**. `Verdict` grades the *guest* only, and a
    port defect is recorded orthogonally on `Entry.portDefect`, because the two
    facts are independent: all four combinations of (guest right/wrong) ×
    (port right/wrong) occur, and a row must be able to say both. Folding the port
    into `Verdict` would also open a hole in `no_looser_verdicts` — a row that
    ought to be `looser` could be graded "port defect" instead and the invariant
    would still pass.

    So grade by asking "does the *guest* reject this, or did we merely not prove
    it?" — and, when the guest does reject, "is the *port* the thing that is
    wrong?". Reaching for `domainRestricted` because a restriction is benign
    collapses the first three rows together, which is how #11493 started: a guest
    rejection was wearing a verdict whose docstring says "Not a defect", and
    `stricter` had zero occurrences despite describing the most safety-relevant
    outcome in the schema. -/
/-- How a routine's spec relates to the external reference.

    The vocabulary is **asymmetric on purpose**: `looser` is a soundness finding,
    `stricter` is a false-reject risk, and `domainRestricted` is not a defect at
    all. Collapsing them to a boolean would discard exactly the distinction the
    audit exists to make. -/
inductive Verdict where
  /-- Spec and reference agree on the routine's whole domain. -/
  | agrees
  /-- Agrees, but the spec covers strictly less input than the reference accepts.
      Not a defect; a coverage gap callers must respect.

      Covers two situations that are both benign but make different promises: a
      **coverage gap** (the guest may well handle the case; we have not proved it)
      and an **ABI precondition** (the triple obliges the caller). The second can
      be violated, the first cannot — the row's note must say which it is. -/
  | domainRestricted
  /-- We reject input the reference accepts → false-rejects on valid chain data. -/
  | stricter
  /-- We accept input the reference rejects → **false-accept; file immediately.** -/
  | looser
  /-- A guest-specific operation with no reference function to compare against. -/
  | noCounterpart
  /-- No spec exists, so the question is not answerable. An honest result. -/
  | unproven
  deriving DecidableEq, BEq, Repr

/-- How much weight a verdict carries. This column is the product: a verdict
    without a basis is an unverified claim, which is the failure mode the audit
    exists to prevent. -/
inductive Basis where
  /-- Backed by the executable differential (`lake exe correspondence-check`). -/
  | diff
  /-- The spec is stated over, or tied by a cited bridge lemma to, the shared
      model, so it inherits the `diff` result. -/
  | bridged
  /-- The spec is tied by a **cited and consumed** bridge lemma to a `SpecRef`
      **port** of the reference that is not itself differentially backed.

      Stronger than `inspection` — the tie is machine-checked, not read. Weaker
      than `bridged` — there is no `diff` result to inherit, so the row's value is
      bounded by the port's fidelity to the Python.

      ⚠️ **A row may only claim this rung if it records a port-fidelity clause
      table**: a clause-by-clause comparison of the port against the vendored
      source, with every non-syntactic restatement either proved or named as an
      assumption. Without that requirement this rung is `machineOnly` with a
      friendlier name. The worked example is `check_gas_limit`, where the port
      writes clause 2 as `gl + delta ≤ p` while `fork.py` writes
      `gl ≤ p - delta` — algebraically equal only because `delta ≤ p`, proved as
      `clause2_port_faithful` rather than assumed.

      Introduced in #11341 because the schema previously forced such rows onto
      `machineOnly`, whose *description* ("stated over a locally defined
      predicate") is false for them even though its *operative* clause ("the
      differential does not transfer") is true. -/
  | ported
  /-- The spec is stated over a *locally defined* machine predicate that
      re-derives the reference's rules independently of the shared model. The
      differential result does **not** transfer. -/
  | machineOnly
  /-- Established by reading both sides; no executable or formal backing. -/
  | inspection
  /-- No basis applies (the row has no verdict to support). -/
  | none
  deriving DecidableEq, BEq, Repr

/-- Which layer a row is about.

    BAL forced this distinction. Its *model* is differential-backed while every
    *guest* routine is unproven — a shape the schema could not express when every
    row was assumed to be a guest routine with a theorem. Recording only the
    guest rows would hide the result; recording the model row as if it were a
    routine would misreport what is proven. -/
inductive Layer where
  /-- A guest RISC-V routine. Its evidence is a whole-routine spec. -/
  | guest
  /-- A pure Lean model function. Its evidence is the executable differential,
      not a theorem. -/
  | model
  deriving DecidableEq, BEq, Repr

/-- One audited routine or model function. -/
structure Entry where
  /-- Guest routine or model function? -/
  kind : Layer := .guest
  /-- Family name; matches the `correspondence-check` subject and the doc page. -/
  family : String
  /-- Guest routine symbol as it appears in the linker facts. -/
  routine : String
  /-- Whole-routine spec theorem, if one exists. Backed by an `abbrev` witness
      below when present. -/
  spec : Option String := none
  verdict : Verdict := .unproven
  basis : Basis := .none
  /-- The reference function this row is compared against. -/
  reference : String := ""
  /-- A defect in the **`SpecRef` port** — the port diverges from the Python — as
      the GitHub issue tracking it.

      Orthogonal to `verdict` on purpose. `verdict` grades the **guest**; this
      grades the **reference side**, and the two are independent facts: a row may
      have a correct guest and a broken port, a broken guest and a correct port,
      or both. Folding this into `Verdict` made the "guest agrees AND port is
      wrong" combination unrepresentable, since choosing that constructor erased
      the guest grade — and it put an alternative beside `looser` in the same
      enum, which would let a false-accept be graded around `no_looser_verdicts`.

      `portDefect_cites_issue` rejects `some 0`: "the port is wrong" cannot be
      recorded without something to fix it against. -/
  portDefect : Option Nat := none
  note : String := ""
  deriving Repr

/-! ## The registry

    RLP rows: see `docs/rlp-spec-correspondence.md`. Row list is the linker
    facts (`scripts/asm-fixtures/symbol-addresses.tsv`), filtered to `rlp_*`.

    SSZ is deliberately **not** enumerated here yet: its guest tower was built
    independently of `SpecRef/SszCodec.lean` and its reference codec is a
    separate external package, so no row could carry a basis better than
    `inspection`. `docs/ssz-spec-correspondence.md` records that as prose until
    a shared model exists. Registering unbacked verdicts would be the exact
    unaudited-measurement failure this registry is meant to prevent. -/

def registry : List Entry := [
  { family := "rlp", routine := "rlp_walk_init",
    spec := some "rlp_walk_init_spec_within",
    verdict := .agrees, basis := .bridged,
    reference := "decode_to_sequence entry",
    note := "9 paths; bridged via Rv64/RLP/WalkDecodeBridge.lean" },
  { family := "rlp", routine := "rlp_walk_next",
    spec := some "rlp_walk_next_spec_within",
    verdict := .agrees, basis := .bridged,
    reference := "decode_item_length + decode_joined_encodings loop",
    note := "18 paths → 6 statuses; predicate rlpItemDecode, bridged" },
  { family := "rlp", routine := "rlp_content_to_u64",
    spec := some "rlp_content_to_u64_spec_within",
    verdict := .agrees, basis := .inspection,
    reference := "_deserialize_to_uint at U64",
    note := "canonical-strict (len>8 → status 2, leading zero → status 3); \
matches U64 exactly, stricter on a Uint field — differential does not reach the typed layer" },
  { family := "rlp", routine := "rlp_content_to_u256_be",
    spec := some "rlp_content_to_u256_be_scalar_spec_within",
    verdict := .agrees, basis := .bridged,
    reference := "_deserialize_to_uint at U256",
    note := "was machineOnly — the machine triple states its outcome as a right-aligned \
`copyN` plus the literal byte test `getByteAt srcBytes srcOff = 0`, mentioning no model \
function. Bridged in #11341 (`Rv64/RLP/ContentToU256BeBridge.lean`) by \
`ctu256_reject_iff_decodeScalar_none` (the byte test IS `decodeScalar`'s leading-zero \
rule) and `ctu256_accept_decodeScalar` (the 32-byte buffer denotes exactly the value \
`decodeScalar` returns, via `fromBytesBE_replicate_zero_append` — right-alignment is \
value-preserving). The row names the consumer, which restates the triple's outcome \
disjunction over `decodeScalar`. U256 FIELDS ONLY, and now precisely: the bridge is \
scoped to `len ≤ 32`, so the status-2 arm is excluded — that arm is the U256 width \
rejection and `decodeScalar` is untyped, so it is the one outcome the shared model does \
not speak to (`from_be_bytes` at U256 is a layer above it). ⚠️ `len > 32` IS REACHABLE — \
`a1` is the content length `rlp_walk_next` returns, unclamped, and all 7 call sites \
(`accountExtractBalance`, `txEip2930Decode` x4, `txEip1559Decode`, `headerExtendedDecode`, \
`balAccountNonstorageFinals`) test `bnez a0` and fail, i.e. they RELY on the status-2 \
rejection. So `hle32` is not an ABI hypothesis the way `hbound` is on the size rows; it \
scopes the BRIDGE, not the routine. The verdict stays `.agrees` because the reference \
is `_deserialize_to_uint` AT U256, which rejects >32 bytes exactly as the guest does — \
the two agree on the whole domain. What `len > 32` limits is the BASIS: that one arm \
has no counterpart in the untyped shared model, so it rests on the machine triple \
(which does cover it) rather than on the differential" },
  { family := "rlp", routine := "rlp_item_size",
    spec := some "rlp_item_size_spec_within",
    verdict := .domainRestricted, basis := .bridged,
    reference := "decode_item_length",
    note := "short forms only (SpanForm); long string 0xb8-0xbf and long list 0xf8-0xff uncovered" },
  { family := "rlp", routine := "rlp_item_span",
    verdict := .unproven, basis := .none,
    reference := "decode_item_length",
    note := "RlpItemSpanSpec.lean is cursor algebra + CodeReq plumbing; no machine triple" },
  { family := "rlp", routine := "rlp_list_count_items",
    spec := some "rlp_list_count_items_spec_within",
    verdict := .agrees, basis := .machineOnly,
    reference := "decode_joined_encodings" },
  { family := "rlp", routine := "rlp_list_nth_item",
    spec := some "rlpListNthItem_spec_within",
    verdict := .agrees, basis := .bridged,
    reference := "decode_to_sequence + index" },
  { family := "rlp", routine := "rlp_field_to_u64",
    spec := some "rlpFieldToU64_spec_within",
    verdict := .agrees, basis := .inspection,
    reference := "_deserialize_to_uint at U64 ∘ walk",
    note := "walk layer bridged; scalar layer inspection-only" },
  { family := "rlp", routine := "rlp_field_to_u256_be",
    spec := some "rlpFieldToU256Be_spec_within",
    verdict := .agrees, basis := .inspection,
    reference := "_deserialize_to_uint at U256 ∘ walk",
    note := "walk layer bridged; scalar layer inspection-only" },
  { family := "rlp", routine := "rlp_bytes_encoded_size",
    spec := some "rlpBytesEncodedSize_encode_spec",
    verdict := .agrees, basis := .bridged,
    reference := "len(encode_bytes(...))",
    note := "was machineOnly — `rbesSize` is standalone arithmetic, not \
(encode …).length. Bridged in #11341 by `rbesSize_eq_encodeBytes_length` \
(`Codegen/Programs/RlpBytesEncodedSizeBridge.lean`), whose load-bearing sublemma \
`u64ByteLen_eq_toBytesBE_length` identifies the guest's 9-way length-of-length \
ladder with `(Nat.toBytesBE ·).length`. The row now names the model-facing \
`rlpBytesEncodedSize_encode_spec` (post: `a0 = (encodeBytes xs).length`), a one-rewrite \
consequence of the untouched machine triple `rlpBytesEncodedSize_spec`. Full domain: \
the `hbound` side condition is 64-bit non-overflow on the register. That is a \
REPRESENTABILITY guard, not a domain restriction, and the distinction is what keeps this \
row `.agrees` rather than `.domainRestricted`: `domainRestricted` means the reference \
accepts inputs the spec excludes, whereas a `List Byte` of length ≥ 2^64 - 9 has no \
representation on the target at all, so `hbound` excludes no input the routine could ever \
be handed. Every byte string the guest can physically be called on is inside the claim" },
  { family := "rlp", routine := "rlp_list_encoded_size",
    spec := some "rlpListEncodedSize_encode_spec",
    verdict := .agrees, basis := .bridged,
    reference := "len(encode_sequence(...))",
    note := "was machineOnly, and weaker than its sibling: the size formula was \
written INLINE in `rlpListEncodedSize_spec`'s statement and never named, so there \
was nothing to compare against the reference. Bridged in #11341 by \
`rlesSize_eq_encode_list_length` (`Codegen/Programs/RlpListEncodedSizeBridge.lean`), \
which names the formula as `rlesSize` and ties it to `(encode (.list items)).length` \
via `encode_list_short`/`encode_list_long` and the shared sublemma \
`u64ByteLen_eq_toBytesBE_length`. Stated against the item list whose encoded payload \
is the register argument — the guest sees only that length, and so does \
`len(encode_sequence(...))`" },
  { family := "rlp", routine := "rlp_encode_uint_be",
    spec := some "reub_spec_within",
    verdict := .domainRestricted, basis := .bridged,
    reference := "encode(Uint) → encode_bytes(to_be_bytes()) — unbounded",
    note := "whole-routine triple landed in #11040, so the ≤55 bound is now a proven property \
of the ROUTINE rather than a documented property of the model — which is exactly the condition \
this row's previous note said would move it off `unproven`. `domainRestricted` because the \
reference accepts any length while the spec needs the stripped payload ≤ 55; `bridged` because \
reub_spec_encode_within restates the post over encodeBytes ∘ toBytesBE ∘ fromBytesBE via \
reubOut_eq_encode_toBytesBE." },
  { family := "rlp", routine := "rlp_encode_list_prefix",
    spec := some "rlp_encode_list_prefix_short_pinned_spec_within",
    verdict := .domainRestricted, basis := .bridged,
    reference := "header of encode_sequence",
    note := "no unified dispatch theorem; lenlen ≥ 2 (payload ≥ 256 B) uncovered" },
  { family := "rlp", routine := "rlp_encode_bytes",
    spec := some "reb_spec_within",
    verdict := .agrees, basis := .bridged, reference := "encode_bytes",
    note := "whole-routine triple over `encodeBytes` itself — the function SpecRef's \
encoders call (`encR := EL.RLP.encode`, `encode (.bytes d) = encodeBytes d` definitionally), \
so no bridge lemma is even needed; `agrees` on the full domain (total function, both sides \
of 55/56 covered; resource preconditions only). Witnessed in `Progress/Routines.lean`, \
not here — this file deliberately does not import Codegen (see the Witnesses block)." },
  { family := "rlp", routine := "rlp_encode_u64",
    verdict := .unproven, basis := .none, reference := "encode(U64)",
    note := "drift guard only" },
  { family := "rlp", routine := "rlp_list_truncate_to_n_fields",
    verdict := .noCounterpart, basis := .inspection,
    note := "signing-hash truncation is guest-specific" },
  { family := "rlp", routine := "rlp_prefix_to_buffer",
    verdict := .noCounterpart, basis := .inspection,
    note := "header emission; no standalone counterpart. Also has NO drift guard" },
  { family := "rlp", routine := "withdrawal_decode",
    spec := some "withdrawal_decode_spec_within",
    verdict := .agrees, basis := .machineOnly,
    reference := "inverse of withdrawalToRlpItem (SpecRef/BlocksRlp): RLP → (index, \
validatorIndex, address, amount)",
    note := "whole-routine triple `wdPrologue ;; wdBBField0` proven against LOCAL \
`Decoded`/`DecodeFailure` predicates. SpecRef carries withdrawal ENCODE (`withdrawalToRlpItem`) \
and SSZ decode (`sszToWithdrawal`) but NO RLP decoder, so there is nothing to bridge to and the \
differential does not transfer — `machineOnly`, not `bridged`. Registered in #11291; this row \
added in #11342 because a witnessed routine with no Correspondence row passed the #11335 gate \
vacuously (absence is weaker than an `unproven` row yet was not caught). Witnessed in \
`Progress/Routines.lean`, not here — this file deliberately does not import Codegen." },

  -- BAL canonical ordering. The model is differential-backed; every guest
  -- routine is unproven because BalCanonicalSort.lean defines only Strings —
  -- no `Program`, so no triple is statable (issue #10817). That split IS the
  -- finding: the ordering is right, and whether the asm implements it is open.
  { family := "bal", kind := .model, routine := "_build_from_builder",
    verdict := .agrees, basis := .diff,
    reference := "block_access_lists.py _build_from_builder (vendored)",
    note := "1149/1149 records agree via `lake exe correspondence-check bal`; \
covers account order (byte-lexicographic), slot order (numeric, NOT \
encoded-byte), per-index orders, and the read/write exclusion" },
  { family := "bal", routine := "bal_canonical_sort",
    verdict := .unproven, basis := .none,
    reference := "the ordering _build_from_builder imposes",
    note := "BalCanonicalSort.lean is String-only; no `: Program`, so no \
cpsTripleWithin is statable. Live path: 6 calls in bal_serializer_rebuild_hash" },

  -- #11344: MPT key expansion. Row mandatory once the symbol is witnessed (#11342).
  { family := "mpt", routine := "bytes_to_nibbles",
    spec := some "bytesToNibblesFlat_spec",
    verdict := .agrees, basis := .ported,
    reference := "keyToNibbles (SpecRef/WitnessState.lean:78); also the \
nibble-expansion half of compact_to_nibbles",
    note := "PORT-FIDELITY CLAUSE TABLE (required by `.ported`). The reference is a \
one-line `List.flatMap` producing `[b >>> 4, b &&& 0x0F]` per byte. TWO clauses differ \
from the guest, both PROVED not assumed: (1) the machine writes `BitVec.truncate 8 \
(b.zeroExtend 64 >>> 4)` where the reference writes `BitVec.ofNat 8 (b.toNat >>> 4)` — \
`highNibble_eq`; (2) the machine ANDs against `signExtend12 15` where the reference uses \
`&&& 0x0F` — `lowNibble_eq`. The accumulator/flatMap shape difference is the third and \
largest: `nibblePrefix` appends on the RIGHT while `flatMap` builds on the LEFT, tied by \
`nibblePrefix_eq_keyToNibbles_take` (induction via `List.take_add_one`). Nothing else \
differs. WHY `.ported` AND NOT `.bridged`: the MPT/witness family has no executable \
differential, so there is no `diff` result to inherit. FULL DOMAIN: the only side \
conditions are ABI (region wf, non-overlap, non-overflow), and `len <= srcBytes.length` \
is the ABI contract, not an input-domain gate" },

  -- #11349: the header gas-limit rule. Row is mandatory once the symbol is witnessed
  -- in Routines.lean -- #11342 showed an absent row passes the cross-registry gate
  -- vacuously.
  { family := "header", routine := "check_gas_limit",
    spec := some "checkGasLimit_ref_spec",
    verdict := .agrees, basis := .ported,
    reference := "check_gas_limit (SpecRef/SeamShell.lean:200, fork.py)",
    note := "FULL DOMAIN and no side condition, which is not the obvious reading: the \
reference is written with two additions (`gl >= p + d`, `gl + d <= p`) that are \
overflow-free only because `Uint = Nat`, so a naive bridge would carry a u64 envelope \
hypothesis and land `domainRestricted`. It needs none, because the guest never forms \
either sum -- it compares `|new - parent|` against `parent / 1024`, and those two guards \
are together equivalent to the single inequality. Tied by `cglStatus_eq_zero_iff` \
(`Codegen/Programs/CheckGasLimitBridge.lean`). WHY `.ported` AND NOT `.bridged`: the tie is \
FORMAL (machine-checked), not a local restatement, but this family has no executable \
differential for a `bridged` grade to inherit. Was `.machineOnly` before the rung existed; \
regraded in #11341. NOT claimed: the \
guest's 1-vs-2 distinction (below-minimum vs out-of-range) is guest-specific; the \
reference returns a bare false, so the bridge is an iff on ACCEPTANCE only. \
PORT-FIDELITY CLAUSE TABLE (required by `.ported`): clauses 1 and 3 are syntactically \
identical to fork.py:1259-1264; clause 2 differs — fork.py writes clause 2 as `gl <= p - delta` while the port writes \
`gl + delta <= p` (avoiding a truncating Uint subtraction). That restatement is \
algebraic, not syntactic, and is PROVED here by `clause2_port_faithful` rather than \
relied upon -- it is the one clause where the port could silently diverge from the \
Python while looking faithful" },
  -- #11351: the second `header` row. `number` is the family representative because
  -- `getN 8` is identical in BOTH fork arms, so the 23-vs-21 discriminant is a no-op
  -- for it -- see the note.
  -- ⚠️ THE TRIPLE PREDATED THIS ROW by over a week (`header_extract_number_spec_within`,
  -- HeaderExtractNumberSpec.lean, landed 27 July in c67f0a988); only the correspondence
  -- was missing. I rebuilt it from scratch in #11457 before finding it, having read "no
  -- registry row" as "no proof" after a truncated survey search. AN ABSENT ROW IS NOT
  -- EVIDENCE OF AN ABSENT PROOF -- grep the tree, unabridged, before rebuilding anything.
  { family := "header", routine := "header_extract_number",
    spec := some "header_number_of_decode",
    verdict := .domainRestricted, basis := .ported, portDefect := some 11513,
    reference := "the `number` field of `_decode_header` (SpecRef/Stateless.lean:75, \
stateless.py:244)",
    note := "TWO INDEPENDENT AXES, which is why this row carries both a verdict and a \
`portDefect` (#11493). The GUEST verdict is `.domainRestricted` on ARITY grounds ALONE; the \
content divergence is reference-side and lives in `portDefect`, not in the verdict. \
(a) ARITY -- this is the whole of the guest-side restriction: the guest never checks how many \
fields the header has, so on a list of any other \
length it still returns a value where `_decode_header` errors; the honest statement is \
`_decode_header = .ok h -> guest succeeds and value = h.number`, not an iff. So the TRIPLE'S \
DOMAIN is restricted to headers the reference accepts, and what the guest does on a \
wrong-arity header is UNPROVEN rather than known-correct -- a proof limit, taxonomy row 1, \
which is why `.agrees` would overclaim even though the content evidence points that way. \
`number` is \
`getN 8` in BOTH the 23-field (current fork) and 21-field (previous) arms, which is exactly \
why this row represents the family. (b) TWO CONTENT RESTRICTIONS, which are a PORT DEFECT: \
the guest rejects a field wider than eight bytes (`Result.tooLong`) and one with a leading \
zero byte (`Result.noncanonical`), while the port's `getN` is plain `bytesBEtoNat`, which \
tolerates both. The reference decodes via `rlp.decode_to(Header, ...)` -- a TYPED decode that \
rejects both -- so the guest matches the Python and only the port is lenient. WHY THIS IS NOT \
A VERDICT: `.stricter` would record a false-reject against the GUEST, which is the correct \
side here; and a port-defect VERDICT would erase the arity restriction in (a) and sit beside \
`looser` in the same enum, letting a false-accept be graded around `no_looser_verdicts`. So \
it is `portDefect := some 11513`, which also covers the other eight `getN` fields. ⚠️ CITATION KIND, since `.ported` requires a clause table: the \
`rlp.decode_to` clause cites an EXTERNAL package (`ethereum_rlp`), not the vendored tree, so \
`scripts/check-spec-refs.sh` cannot machine-check it the way it checks a `forks/.../x.py:NNN` \
line -- it is read, not verified. The VERSION is not the risk: `uv.lock` resolves \
`ethereum-rlp == 0.1.6` exactly with a sha256, and 0.1.6 is precisely the version that \
tightened decoding (`pyproject.toml`'s `>=0.1.6,<0.2` is a range, but only the lock is \
authoritative -- see docs/agents/spec-correspondence.md 6a). See #11513. Tied by \
`header_number_of_decode` \
(`Codegen/Programs/HeaderExtractNumberBridge.lean`), consuming the machine triple \
`header_extract_number_spec_within` and `decode_header_inv`. NOT NEEDED: any byte-string \
side condition -- `_decode_header` runs `items.mapM rlpBytes?`, which sends `.list` to \
`none`, so a successful header decode already implies every field is a byte string. WHY \
`.ported` AND NOT `.bridged`: the tie is FORMAL, but this family has no executable \
differential to inherit. PORT-FIDELITY CLAUSE TABLE (required by `.ported`): `mkHeader`'s \
`number := getN 8` is syntactically the `header.number` assignment of stateless.py:244; the \
arity guard `bs.length = 23 / 21` is the port's rendering of the fork discriminant; and the \
two dropped canonicality checks above are the one place the port is WEAKER than the Python, \
now carried by `portDefect` and gated by `portDefect_cites_issue` rather than only by this \
note" },
  -- `bal_sort_storage_writes` / `bal_sort_account_writes` had rows here while
  -- they were dead-but-present code. Both routines were deleted from the image
  -- in da930613c (GH #11054); measured absent on main 696c236f2 -- zero
  -- occurrences in the emitted asm, including the `.globl` and label, and zero
  -- in the ELF symbol table. A registry row for a symbol that does not exist
  -- misreports the unproven count, so the rows go with the routines.

  -- #11352: the guest-input u32 accessor. A row is MANDATORY here, not optional:
  -- `bgv_u32le` is now witnessed in Routines.lean, and #11342 established that a
  -- witnessed symbol with NO row passes the cross-registry gate vacuously.
  { family := "guest", routine := "bgv_u32le",
    spec := some "bgvU32leFlat_spec",
    verdict := .agrees, basis := .ported,
    reference := "the fixed-width LE reads of deserialize_stateless_input \
(SpecRef/Guest.lean:29), which reduce to bytesLEtoNat (SpecRef/Crypto.lean:38)",
    note := "PORT-FIDELITY CLAUSE TABLE (required by `.ported`). Reference: the \
fixed-width LE reads in `deserialize_stateless_input` reduce to `bytesLEtoNat` \
(SpecRef/Crypto.lean:38), a port of the SSZ uint decoder. ONE clause: `bytesLEtoNat` \
accumulates `b + 256 * rest` where the guest ORs four shifted bytes. That restatement is \
NOT syntactic and is PROVED, not assumed, by `leU32_eq_bytesLEtoNat` via `toNat_or_shift` \
(OR past the accumulated width is addition). No other clause differs. \
WHY `.ported` AND NOT `.bridged`: the guest/SSZ family has no executable differential, so \
there is no `diff` result to inherit; the row's value is bounded by the port's fidelity to \
the Python, which the clause table above is what establishes. Was `.machineOnly` when the \
rung did not exist — that grade's description was false here, since the tie is \
machine-checked rather than a local restatement. Regraded in #11341" }
]

/-! ## Counts -/

def countVerdict (v : Verdict) : Nat := (registry.filter (·.verdict == v)).length

/-- Rows carrying a `SpecRef` port defect. Counted over the orthogonal field, so
    it is independent of the guest verdict — a row appears here *and* in whichever
    `countVerdict` bucket its guest grade puts it. -/
def countPortDefect : Nat := (registry.filter (·.portDefect.isSome)).length
def countBasis (b : Basis) : Nat := (registry.filter (·.basis == b)).length
def countFamily (f : String) : Nat := (registry.filter (·.family == f)).length

def countKind (k : Layer) : Nat := (registry.filter (·.kind == k)).length

theorem registry_size : registry.length = 25 := by decide
theorem rlp_rows : countFamily "rlp" = 19 := by decide
theorem bal_rows : countFamily "bal" = 2 := by decide
/-- #11352. One row so far; the family has no differential (see the row's note). -/
theorem guest_rows : countFamily "guest" = 1 := by decide
/-- #11349, #11351. No differential for this family -- see the rows' notes. -/
theorem header_rows : countFamily "header" = 2 := by decide
/-- #11344. No differential for this family -- see the row's note. -/
theorem mpt_rows : countFamily "mpt" = 1 := by decide

theorem verdict_counts :
    countVerdict .agrees = 16 ∧ countVerdict .domainRestricted = 4 ∧
    countVerdict .stricter = 0 ∧ countVerdict .looser = 0 ∧
    countVerdict .noCounterpart = 2 ∧ countVerdict .unproven = 3 := by decide

/-- Port defects are counted separately because they are a different axis. Note
    the verdict census above is **unchanged** by #11493 — `header_extract_number`
    is still one of the four `domainRestricted` rows, on its arity restriction.
    What #11493 added is this second axis, recording that the same row also has a
    broken reference. An alternative-constructor design would have moved the row
    out of `domainRestricted` and lost the arity fact. -/
theorem port_defect_count : countPortDefect = 1 := by decide

theorem basis_counts :
    countBasis .diff = 1 ∧ countBasis .bridged = 10 ∧
    countBasis .ported = 4 ∧
    countBasis .machineOnly = 2 ∧ countBasis .inspection = 5 ∧
    countBasis .none = 3 := by decide

/-! ## Invariants

    These are the reason the registry is Lean and not markdown: each is a
    property a hand-maintained table can silently violate. -/

/-- **The soundness invariant.** No audited routine accepts input the reference
    rejects. Recording a `looser` row fails this theorem, so a false-accept
    cannot land quietly — amending it must be deliberate and visible in review. -/
theorem no_looser_verdicts : countVerdict .looser = 0 := by decide

/-- **Every port-defect row names a tracked defect.** `some 0` is rejected, so
    "the port is wrong" cannot be asserted without something to fix it against —
    the difference between a recorded defect and a note nobody acts on. -/
theorem portDefect_cites_issue :
    registry.all (fun e => match e.portDefect with
      | some issue => issue != 0
      | none => true) = true := by decide

/-- A **guest routine** with no spec cannot carry a substantive verdict: without
    a spec there is nothing to compare, so the only honest values are `unproven`
    and `noCounterpart`. Model rows are exempt — their evidence is the
    differential, not a theorem. -/
theorem verdict_requires_spec :
    registry.all (fun e =>
      e.kind != .guest || e.spec.isSome
        || e.verdict == .unproven || e.verdict == .noCounterpart) := by
  decide

/-- A `diff`-graded **guest** row must name the spec it is grading; a guest
    routine cannot inherit the differential without a theorem tying it to the
    model. -/
theorem basis_diff_requires_spec :
    registry.all (fun e => e.kind != .guest || e.basis != .diff || e.spec.isSome) := by
  decide

/-- Only model rows may be `diff`-graded without a spec — stated so that adding
    a spec-less `diff` guest row fails elaboration rather than quietly
    overclaiming. -/
theorem specless_diff_is_model_only :
    registry.all (fun e => e.basis != .diff || e.spec.isSome || e.kind == .model) := by
  decide

/-- Every row names the family it belongs to. -/
theorem families_nonempty : registry.all (fun e => e.family != "") := by decide

/-! ## Witnesses

    These `abbrev`s are what make the `spec` strings above real: renaming or
    deleting one of these theorems fails this file's elaboration instead of
    silently leaving a stale registry row. Same device as the witness block at
    the bottom of `Progress.lean`.

    Only routines whose spec lives in a module this file can import without
    cycling are witnessed here; the rest are covered by the doc page's
    grep-verified table. Extending the witness set is strictly an improvement —
    add the import and the `abbrev`.

    Codegen-proved specs (`reub_spec_within`, `reb_spec_within`, …) are
    deliberately NOT witnessed here even though they could be: since #11273,
    `check-layering.sh` L1 exempts all of `EvmAsm/Progress/**` (sound because
    L2 makes the registries pure sinks), so importing Codegen from this file
    would elaborate AND pass the gate. It stays unimported to keep this
    module's closure light. Those specs are witnessed in
    `EvmAsm/Progress/Routines.lean` instead, with `#print axioms` lines in
    `AxiomWitnesses.lean` — a rename fails *that* file's elaboration, so a
    local `abbrev` here would be a redundant convenience, not protection.
    (An earlier revision of this comment claimed L1 *forbids* the import;
    that predates the #11273 exemption and was stale — GH #11294 rider.) -/

private noncomputable abbrev _rlp_walk_init_witness :=
  @EvmAsm.Rv64.RLP.rlp_walk_init_spec_within
private noncomputable abbrev _rlp_walk_next_witness :=
  @EvmAsm.Rv64.RLP.rlp_walk_next_spec_within
private noncomputable abbrev _rlp_content_to_u64_witness :=
  @EvmAsm.Rv64.RLP.rlp_content_to_u64_spec_within
private noncomputable abbrev _rlp_content_to_u256_be_witness :=
  @EvmAsm.Rv64.RLP.rlp_content_to_u256_be_spec_within
-- #11341: the model-facing counterpart, named by the `.bridged` row above. Witnessed
-- here rather than in `Routines.lean` because this file already imports the Rv64 spec
-- module — the Codegen-side bridges cannot do that, which is why they live over there.
private noncomputable abbrev _rlp_content_to_u256_be_scalar_witness :=
  @EvmAsm.Rv64.RLP.rlp_content_to_u256_be_scalar_spec_within

end EvmAsm.Progress.Correspondence
