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
    note := "len>8 → status 2; leading-zero encodings are accepted and decoded by \
big-endian magnitude, matching U64 int.from_bytes semantics" },
  { family := "rlp", routine := "rlp_content_to_u256_be",
    spec := some "rlp_content_to_u256_be_scalar_spec_within",
    verdict := .agrees, basis := .bridged,
    reference := "_deserialize_to_uint at U256",
    note := "the machine triple states its outcome as a right-aligned `copyN` and a \
length bound. Bridged in #11341 (`Rv64/RLP/ContentToU256BeBridge.lean`) by \
`ctu256_accept_decodeScalar` (the 32-byte buffer denotes exactly the value \
`decodeScalar` returns, via `fromBytesBE_replicate_zero_append` — right-alignment is \
value-preserving). The bridge carries an explicit canonical-input hypothesis because \
the machine decoder is lenient. The row names the consumer, which restates the triple's outcome \
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
    spec := some "rlp_item_span_spec_within",
    verdict := .domainRestricted, basis := .machineOnly,
    reference := "decode_item_length",
    note := "whole-routine cpsTripleWithin under short-list outer (payload ≤ 55) + \
WalkedSpanForm on every walked prefix 0..i (#11577). Long-list outer header and \
non-SpanForm walked items uncovered. coverRef `rlp_item_span_precondition_reachable` \
([0xc1,0x80] i=0). Witnessed in Progress/Routines.lean" },
  { family := "rlp", routine := "rlp_list_count_items",
    spec := some "rlp_list_count_items_spec_within",
    verdict := .agrees, basis := .machineOnly,
    reference := "decode_joined_encodings",
    note := "⛔ BLOCKED ON #11711, and the reason is structural rather than unfinished \
work. #11341 asked for a bridge from the local `StrictPrefix` walk relation to the shared \
`DecodeChain`; PR #11694 landed the structural half (`DecodeChain.snoc`, the snoc-vs-cons \
reversal, plus the count-to-items construction) and two of the three byte-string per-item \
disjuncts. The remaining per-item obligation CANNOT BE DISCHARGED: `DecodeChain` demands \
fuel-insensitivity (`∀ m`) per link, which is sound only for byte-string items, whereas a \
nested list's `decodeAux` recurses into `decodeItems nDepth payload` and IS fuel-sensitive \
(WalkDecodeBridge.lean:405-408 says so in the tree's own words). ⚠️ AND THE DOMAIN CONTAINS \
NESTED LISTS: since #11675 this routine is called by `mpt_node_kind` to check node arity, and \
MPT branch children are either a 32-byte hash or an INLINE EMBEDDED NODE — \
`SpecRef/IncrementalMpt.lean:155` `resolveChildRefAux` has an explicit `| .list items =>` arm \
for exactly that. So the hypothesis is not merely unproven on this routine's domain, it is \
unsatisfiable, and a structural theorem whose hypothesis cannot be instantiated says nothing \
about the routine. The row therefore stays `machineOnly` until #11711 supplies a \
fuel-sensitive chain predicate; regrading it earlier would claim a differential transfer that \
does not exist. Separately noted on #11341: the machine relation accepts a list item whose \
SPAN fits without validating its interior, where `decode_joined_encodings` decodes every \
item — a looser-than-reference shape whose reachability is NOT established" },
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
    note := "⚠️ STALE CLAIM CORRECTED (#10817): this note used to say \
`BalCanonicalSort.lean is String-only; no \\`: Program\\`, so no cpsTripleWithin is statable`. \
FALSIFIED by #11046, which converted the routine to `balCanonicalSort_prog` (147 instructions, \
head ++ digit ++ tail) and registered it in the guest image -- a triple IS statable today, and \
the row stays `.unproven` because nobody has stated one, not because nobody can. \
STILL BLOCKING, and it is a PREDICATE gap rather than a Program gap: the headline obligation is \
PERMUTATION (a sort that silently drops rows is still sorted, and the end-to-end hash test \
CANNOT see it -- it compares against a model built from the DECLARED rows), and permutation \
cannot be stated without a List-indexed assertion over the row array. \
`RegionPredicates.balEntriesFrom`/`balBuffer`/`balOwn` now supply it, stride-parameterised \
because the six live calls use four distinct strides. \
INDEPENDENT KEY: available and corpus-validated -- `_build_from_builder` at 1149/1149 via \
`lake exe correspondence-check bal` (#11016), which is what a sortedness predicate must be \
stated against rather than against the guest's own digit extraction (the vacuity trap the \
module header warns about). ⚠️ Slots sort NUMERICALLY (`slot : U256`, \
block_access_lists.py:564); the reference DOCSTRING says `lexicographically` and is wrong -- \
see docs/bal-spec-correspondence.md. Live path: 6 calls in bal_serializer_rebuild_hash" },

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

  -- #11516: account-leaf decode, the pairing that issue says must be stated.
  { family := "account", routine := "account_decode",
    spec := some "account_decode_spec_within",
    verdict := .domainRestricted, basis := .bridged,
    reference := "decode_account_from_leaf (SpecRef/WitnessState.lean:117), tied by \
AccountDecodeCompose.decoded_matches_specRef",
    note := "⭐ WHY THIS ROW EXISTS AT ALL is #11516's finding: we maintain a Lean port of \
execution-specs *specifically to be the reference*, plus an asm-side predicate (`Decoded`) \
that CONTRADICTED it, and nothing noticed -- every gate we had checked a different axis \
(bytes vs Program, addresses vs image, BAL edges, TCB). The divergence surfaced only when a \
fixture failed for an unrelated reason. An unstated pairing is how a predicate drifts from \
the reference indefinitely. WHY `domainRestricted` AND NOT `agrees`: fields 2/3 were closed \
by #11483/#11484 (zero-length storage_root/code_hash now fold to EMPTY_TRIE_ROOT / \
EMPTY_CODE_HASH, matching the reference's `if decoded[2] else EMPTY_TRIE_ROOT`), but \
`Decoded` still carries l0 <= 8 and l1 <= 32 LENGTH limits on nonce/balance where the \
reference imposes no length constraint at all -- it just runs `int.from_bytes`. So a \
zero-prefixed or over-width nonce/balance is accepted by the reference and outside what we \
prove. That is #11523, still open, and this row is the thing that keeps the gap visible \
instead of assumed. It is a COVERAGE GAP, not an ABI precondition: the guest may well handle \
those inputs; we have not proved it. ⚠️ NOT a portDefect: #11516 checked \
`decode_account_from_leaf` field-for-field against witness_state.py:112-118 and found them \
identical, including the malformed case -- SpecRef modelled the folds correctly all along, so \
the outlier was our own predicate. Standing hazard from that issue, repeated here because it \
applies to this row's evidence: SpecRef is a port and drifts, so cite execution-specs at the \
pin, never SpecRef alone -- citing our own Lean to justify spec alignment is circular" },

  -- #11348: the block/receipt bloom accumulation.
  { family := "bloom", routine := "bloom_or_into",
    spec := some "bloomOrIntoFn_spec",
    verdict := .agrees, basis := .bridged,
    reference := "logs_bloom's pointwise-OR decomposition \
(SpecRef/BloomAlgebra.lean: bloomOr, logs_bloom_append)",
    note := "⭐ THE COUNTERPART HAD TO BE CONSTRUCTED, which is the whole content of \
this row. The reference `logs_bloom` (Fork.lean:128) never ORs two blooms: it folds \
*bit-sets* into one accumulator via `add_to_bloom`'s three `List.set`s, over the \
block's logs as one flat list. The guest instead materialises a bloom per receipt and \
ORs them pairwise. So before #11348 there was no reference term for this routine's post \
at all and the only honest verdict would have been `noCounterpart`. BloomAlgebra supplies \
the missing algebra: `add_to_bloom b e = bloomOr b (add_to_bloom zeroBloom e)`, whose \
proof is NOT the obvious disjoint-update argument -- the three bit indices derived from \
one entry CAN collide into the same byte, so it goes through `setOr_getD` with a case \
split per step, handling collisions by `Nat.lor` idempotence rather than avoiding them. \
That yields `logs_bloom_append`, and hence `bloomOrInto_fold_eq_logs_bloom`: folding \
this routine over per-receipt log groups from the zero bloom equals the reference bloom \
of all the logs. WHY `.bridged`: the guest side is a machine-level SAsm triple \
(`bloomOrIntoFn_spec`) whose post is `orWin src orig 32`, and it is tied to `bloomOr` by \
a Lean theorem (`orWin_full_eq_bloomOr`, BloomOrIntoBridge.lean) rather than by \
inspection -- the two shapes match definitionally because `bloomOr` was deliberately \
written in the guest's `(List.range 256).map` form. ⚠️ SCOPE: the FOLD only, per the \
issue and docs/leaf-routine-targets.md. The per-log index derivation (keccak256 + the \
11-bit extraction) is an opaque function of the entry here; a divergence in THAT would \
not be caught by this row" },

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
  { family := "header", routine := "header_validate_extra_data_length",
    spec := some "header_extra_data_length_of_decode",
    verdict := .domainRestricted, basis := .ported,
    reference := "the `extra_data` length clause of `validate_header` \
(SpecRef/SeamShell.lean:248, fork.py) over `_decode_header`'s field 12",
    note := "#11575 row 2. ⚠️ THIS ROW'S COMPARISON BOUNDARY IS NOT THE ONE THE OTHER `header` \
ROWS USE, and the method doc requires saying so (spec-correspondence.md 5). Every other \
`header_*` row ties a routine to a FIELD OF `_decode_header`. This one cannot: `extra_data` is \
plain `Bytes` in the reference, genuinely UNBOUNDED at decode time -- unlike the `FixedBytes` \
aliases that #11615 made checkable -- so there is nothing in `_decode_header` to compare a \
length against. The <=32 rule is a clause of a DIFFERENT spec function, `validate_header`. So \
the boundary is: `_decode_header` supplies the field, and the routine implements a \
`validate_header` clause over it, which is why the tie has TWO conclusions (a length equation \
on the decode side, a decision equivalence on the validation side) rather than one. \
THE DECISION IS AN IFF, not one-directional: `hvedPost`'s first two arms differ only in the \
guard -- `a0 = 0` with `not (32 <u len)` and `a0 = 1` with `32 <u len` -- so on a successful \
decode the guest's accept/reject choice is TOTAL over the field, and the honest statement is an \
equivalence with the reference's throw condition. That is stronger than row 9's field tie and \
is worth noting: the guest is not merely value-correct here, it makes the same DECISION. \
DOMAIN RESTRICTION -- ARITY ONLY (taxonomy row 1, a proof limit), as for row 1: the guest never \
checks how many fields the header has, so on a list of any other length it still returns a \
verdict where `_decode_header` errors. Field 12 exists in BOTH the 23- and 21-field arms, which \
is why this row pairs with `chain_validate_extra_data_length`. NO precondition and NO \
`portDefect`: the field needs neither, since the reference imposes no decode-time width on it. \
STEP BOUND: K20 (`rlp_list_nth_item`) only, so this row does NOT inherit #11461's \
`7 * (2^64 - 1)` factor -- same as row 1, unlike the five numeric siblings. \
Tied by `header_extra_data_length_of_decode` \
(`Codegen/Programs/HeaderValidateExtraDataLengthBridge.lean`), consuming the machine triple \
`header_validate_extra_data_length_spec_within` and `decode_header_inv`. WHY `.ported` AND NOT \
`.bridged`: the tie is FORMAL, but this family has no executable differential to inherit. \
PORT-FIDELITY CLAUSE TABLE (required by `.ported`): `mkHeaderFields`' `extraData := getB 12` is \
syntactically the `header.extra_data` assignment of stateless.py:244; the guard \
`if header.extraData.length > 32 then throw` is syntactically fork.py's clause; and the \
Word-vs-Nat comparison is PROVED equivalent rather than assumed -- the bridge derives \
`(bs.getD 12 []).length < 2 ^ 64` from the buffer bound, so `not (32 <u ofNat 64 L)` and \
`L <= 32` coincide with no wraparound. NOT NEEDED: any width side condition on the field, and \
that absence is the point -- `extra_data` is the ONE header byte field where guest and \
reference genuinely differ in KIND rather than in bound (#11615)" },
  { family := "header", routine := "header_extract_logs_bloom",
    spec := some "header_logs_bloom_of_decode",
    verdict := .domainRestricted, basis := .ported,
    reference := "the `bloom` field of `_decode_header` (SpecRef/Stateless.lean:210, \
stateless.py:244)",
    note := "#11575 row 1, the first fork of #11351's pattern -- and it lands CLEANER than \
its representative, which is the point worth recording. \
DOMAIN RESTRICTION -- ARITY ONLY, and it is taxonomy row 1 (a proof limit): the guest never \
checks how many fields the header has, so on a list of any other length it still returns a \
value where `_decode_header` errors; the honest statement is `_decode_header = .ok h -> guest \
succeeds and output = h.bloom`, not an iff. Unlike `header_extract_number` there is NO second \
restriction: no precondition on the field, no `portDefect`. \
WHY THE CONTENT AXIS IS CLEAN, WHICH IT WAS NOT BEFORE #11615: `helbRetPost`'s middle arm is \
`a0 = 2 AND Success .. 6 fo len AND len /= 256` -- the guest REJECTING a `bloom` whose content \
length is not 256. Graded against the port as it stood, that read as the guest being STRICTER, \
because `getB` was a bare `bs.getD i []` and a successful decode said nothing about width. It \
was never a guest defect: `_deserialize_to_bytes` constructs the annotated type and \
`FixedBytes.__new__` enforces `LENGTH`, so `Bloom = Bytes256` IS width-checked by the reference \
(`ethereum_types` 0.4.1 bytes.py:29-37). SECOND INSTANCE of the misattribution #11493 unpicked \
-- a port gap making a correct guest look strict -- the first being canonicality on `number` \
(#11617). ⚠️ NOT a third instance, and #11620 is NOT one either: there the reference imposes no \
bound at all (`Uint.from_be_bytes` is a plain `int.from_bytes`) while the guest bounds at 8, so \
the guest genuinely rejects more -- grouping it here would invite reading it as closable, which \
it is not (maintainer correction on #11624). The transferable shape: `guest stricter than port` \
RESOLVES DIFFERENTLY PER ANNOTATION -- matched for `FixedBytes`/`FixedUnsigned`, a genuine \
over-rejection for `Uint`. With #11615 the width is a CONCLUSION of `decode_header_inv`, so \
`header_logs_bloom_of_decode` carries no width hypothesis at all and its `len = 256` is what \
excludes the `a0 = 2` arm for a composing caller. \
GUEST-SIDE WIDTH ENFORCEMENT IS INDEPENDENTLY CONFIRMED, which matters because a LENIENT guest \
here would be a soundness gap rather than a correspondence gap: \
`headerExtractLogsBloomFunction.s:14-15` emits `li t2, 256` / `bne t1, t2, .Lhelb_size_fail`, \
and the rejection is PROVEN not merely emitted -- it is the `a0 = 2` arm of `helbRetPost` \
(`HeaderExtractLogsBloomSpec.lean:343`). See #11615 for the same check on \
`state_root`/`receipts_root`/`withdrawals_root`. \
STEP BOUND: this row does NOT inherit #11461's `7 * (2^64 - 1)` factor. Its bound's `7 * 256` \
term is the genuine 256-byte bloom copy, i.e. data-derived -- the routine calls K20 \
(`rlp_list_nth_item`) and never the K34 scalar loop that is #11461's origin. Recorded because \
the numeric siblings in #11575 DO inherit it, and the difference is not obvious from the row. \
Tied by `header_logs_bloom_of_decode` \
(`Codegen/Programs/HeaderExtractLogsBloomBridge.lean`), consuming the machine triple \
`headerExtractLogsBloom_spec_within` and `decode_header_inv`. WHY `.ported` AND NOT `.bridged`: \
the tie is FORMAL, but this family has no executable differential to inherit. \
PORT-FIDELITY CLAUSE TABLE (required by `.ported`): `mkHeaderFields`' `bloom := getB 6` is \
syntactically the `header.bloom` assignment of stateless.py:244; the arity guard \
`bs.length = 23 / 21` is the port's rendering of the fork discriminant; and the width clause is \
`fixedBytesFieldWidths`' `(6, 256)`, whose provenance is `Bloom = Bytes256` \
(amsterdam/fork_types.py:34 -> ethereum_types bytes.py:154-159) and whose enforcement is \
`decodeItemFixedBytes`, PROVED to pin the length by `decodeItemFixedBytes_inv` rather than \
assumed. ⚠️ CITATION KIND: the `FixedBytes` clause cites an EXTERNAL package, so \
`scripts/check-spec-refs.sh` cannot machine-check it -- read, not verified; `uv.lock` pins \
`ethereum-types == 0.4.1`. See #11615, #11575" },
  { family := "header", routine := "header_extract_number",
    spec := some "header_number_of_decode",
    verdict := .domainRestricted, basis := .ported,
    reference := "the `number` field of `_decode_header` (SpecRef/Stateless.lean:210, \
stateless.py:244)",
    note := "`portDefect` CLEARED in #11513; verdict STAYS `.domainRestricted`, but for a \
different reason than before and the reason is the whole content of this row. The previous note \
asserted that the guest's two rejections BOTH match `rlp.decode_to`, so that only the port was \
lenient. Only ONE of them does. \
(a) CANONICALITY -- was a real port defect, NOW FIXED. `_deserialize_to_uint` rejects a \
leading zero byte on every uint field, and the port's `getN = bytesBEtoNat` did not; \
`_decode_header` now runs `numericFieldWidths` through `decodeItemScalar`, so the port is \
faithful ON THE NUMERIC FIELDS and this row's `portDefect` is retired. The scalar bridge \
has no noncanonical machine outcome; model canonicality is an explicit input \
hypothesis rather than an assumed machine rejection. \
⚠️ SCOPE OF THAT CLAIM: it covers the nine numeric fields, which is all this row's `number` \
depends on. A SECOND, independent leniency survives on the FIXED-WIDTH BYTE fields -- \
`_deserialize_to_bytes` builds the annotated type and `FixedBytes.__new__` raises when the \
length is wrong, so the reference length-checks `Hash32`/`Address`/`Root`/`Bloom`/`Bytes32`/ \
`Bytes8`, while the port's `getB` was a bare `bs.getD i []`. #11513 dismissed those fields as \
`byte strings either way`; that was wrong, and it is NOW ALSO FIXED (#11615), separately \
because the check is ARITY-DEPENDENT -- a `length = 32` sweep would reject every 21-field \
header, where the numeric sweep was safe because `[]` passes a uint check. Neither gap affects \
this row, whose field is numeric, but together they are what let the byte-field sibling rows \
(notably `header_extract_logs_bloom`, whose success arm needs `Bloom`'s 256) be stated without \
a width hypothesis. \
(b) WIDTH -- is NOT a port defect, and NOT an FR either. It is a PROJECT-WIDE INPUT \
ASSUMPTION, i.e. the ABI-PRECONDITION flavour of `.domainRestricted` (taxonomy row 2, not row \
1) -- and per that table's requirement, this note says WHICH: precondition, not coverage gap. \
The mechanism: the width bound comes from the target type's `from_be_bytes`, NOT from \
`_deserialize_to_uint`. `FixedUnsigned.from_be_bytes` raises when the buffer exceeds the type \
(`ethereum_types` 0.4.1 numeric.py:566-577), while `Uint.from_be_bytes` is a plain \
`int.from_bytes` with NO length check (numeric.py:523-528). `number` is annotated `Uint` \
(amsterdam/blocks.py:157), so CPython ACCEPTS a nine-byte `number` and so does the fixed port, \
while the guest's `Result.tooLong` rejects it. \
WHY NOT `.stricter` -- maintainer ruling, #11620: evm-asm carries a project-wide assumption \
for exactly `difficulty`, `number`, `gasUsed`, `gasLimit` and `timestamp`, and `the \
project-wide assumptions give the guest freedom to choose its behavior`; rejecting \
out-of-assumption input is the PREFERRED behaviour, not a defect to remove. So within the \
domain the project states there is no valid input the guest false-rejects, which is what \
`.stricter` would assert. #11620 also records the follow-up @pirapira suggested: a SECOND top \
theorem proving the guest rejects out-of-assumption header values, which would turn this from \
permitted-freedom into a proven property. \
⚠️ WHAT KEEPS THIS HONEST: the precondition is EXPLICIT IN THE STATEMENT -- \
`header_number_of_decode` takes `hfits : hdr.number < 2 ^ 64`. An unstated bound wearing a \
benign verdict would be strictly worse than an FR, because an FR at least gets counted. And a \
`#guard` in Stateless.lean pins that the nine-byte `number` is ACCEPTED BY THE PORT: the \
assumption is about the GUEST's reading width, so tightening the port to 8 would convert a \
stated precondition into a port defect in the opposite direction. \
SYSTEMIC, NOT PER-FIELD: the guest is a u64 machine reading fields the spec types as \
arbitrary-precision or 256-bit. The same shape covers `gasLimit`/`gasUsed` (`Uint`) and \
`timestamp` (`U256`, reference bound 32 bytes vs guest 8 -- the field most easily missed, since \
it is bounded on both sides at different widths). The #11575 sibling rows inherit it, and each \
must state the precondition explicitly as here. Only the three `U64` fields agree outright. \
(c) ARITY is the OTHER thing `.domainRestricted` covers here, and it IS taxonomy row 1 -- a \
genuine proof limit: the guest never checks how many fields the header has, so on a list of \
any other length it still returns a value where `_decode_header` errors; the honest statement \
is `_decode_header = .ok h -> guest succeeds and value = h.number`, not an iff. `number` is \
`getN 8` in BOTH the 23-field (current fork) and 21-field (previous) arms, which is why this \
row represents the family. So this single verdict carries BOTH flavours, which the note must \
disambiguate: (b) precondition, (c) coverage. \
Tied by `header_number_of_decode` (`Codegen/Programs/HeaderExtractNumberBridge.lean`), \
consuming the machine triple `header_extract_number_spec_within` and `decode_header_inv`. Its \
one remaining hypothesis is `hfits : hdr.number < 2 ^ 64` -- the FR in (b), and phrasable over \
the VALUE only because (a) is now enforced: with no leading zeros, `at most eight bytes` and \
`< 2 ^ 64` coincide (`Nat.length_le_of_canonical_lt`). \
NOT NEEDED: any byte-string side condition -- `_decode_header` runs `items.mapM rlpBytes?`, \
which sends `.list` to `none`, so a successful header decode already implies every field is a \
byte string. WHY `.ported` AND NOT `.bridged`: the tie is FORMAL, but this family has no \
executable differential to inherit. \
PORT-FIDELITY CLAUSE TABLE (required by `.ported`): `mkHeaderFields`' `number := getN 8` is \
syntactically the `header.number` assignment of stateless.py:244; the arity guard \
`bs.length = 23 / 21` is the port's rendering of the fork discriminant; the per-field typed \
checks are `numericFieldWidths` + `decodeItemScalar`, whose `Option Nat` width argument is the \
`Uint`-vs-`FixedUnsigned` split, with the width table read off `Header`'s annotations; and \
assigning `bytesBEtoNat` alongside a passing check rather than the checked decoder's own \
result is PROVED equivalent, not assumed (`decodeItemScalar_value`). \
⚠️ CITATION KIND: the `_deserialize_to_uint` and `from_be_bytes` clauses cite EXTERNAL \
packages (`ethereum_rlp`, `ethereum_types`), not the vendored tree, so \
`scripts/check-spec-refs.sh` cannot machine-check them the way it checks a `forks/.../x.py:NNN` \
line -- they are read, not verified. `uv.lock` pins BOTH exactly \
(`ethereum-rlp == 0.1.6`, `ethereum-types == 0.4.1`); note a stale local `.venv` may carry \
0.1.5/0.3.0, and reading those inverts this row's verdict -- see \
docs/agents/spec-correspondence.md 6a. See #11513" },
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
machine-checked rather than a local restatement. Regraded in #11341" },

  -- #11574: the crypto family's first two rows. ⚠️ BOTH machine triples predate
  -- this registration by months; a name search for the routines found nothing
  -- because the specs live in sibling `*SAsm` modules. What was missing is the
  -- SpecRef vocabulary and these rows, not the proofs.
  { family := "crypto", routine := "blsg_lt_p",
    spec := some "blsgLtP_spec_specref",
    verdict := .domainRestricted, basis := .ported,
    reference := "Bls12.bytes_to_fq (SpecRef/PrecompilesBls.lean:79), a port of \
amsterdam/vm/precompiled_contracts/bls12_381/__init__.py:426-454",
    note := "WHY `domainRestricted` AND NOT `agrees`: the tie carries \
`w.length = 64` and `∀ i < 16, w.getD i 0 = 0` — the EIP-2537 wire pad. That gate is \
LOAD-BEARING, not decorative: the reference decodes all 64 bytes, so a nonzero pad byte \
makes the value ≥ 2^384 > p and the reference REJECTS, while this routine scans only the \
48 compact bytes and would not see it. \
⭐ THE GUEST DOES CHECK THE PAD, and this is a COVERAGE gap rather than a behavioural one. \
Every calldata reader of a wire felt calls `blsg_is_zero_n(ptr, 16)` and rejects on \
nonzero before scanning: `blsg_decode_g1` (Programs/Bls12G1.lean:692-700, both \
coordinates), `blsg2_decode_g2` (Bls12G2.lean:774-784, all four felts), \
`zkvm_bls12_map_fp_to_g1` (Bls12MapG1Real.lean:23-29), `zkvm_bls12_map_fp2_to_g2` \
(Bls12MapG2Real.lean:23-38). All are reachable — the precompile dispatch table wires \
0x0b..0x11 (PrecompileSharedExecute.lean:136-142). \
⚠️ WHAT IS NOT PROVED, stated so the gate is not read as narrower than it is: that \
composition. `blsg_is_zero_n(16) ∧ blsg_lt_p(48) ⟹ bytes_to_fq`'s verdict on the 64-byte \
felt is not a theorem, and cannot be one yet — those decoders exist only as assembly \
STRINGS, with no `Program`, no `_eq_prog` drift guard, and no fixture. Closing this row to \
`agrees` needs that conversion first. \
⚠️ PREDICATE agreement only: `lt_p` returns a boolean, never the field element, so value \
agreement is NOT available from this routine and is not claimed. \
PORT-FIDELITY CLAUSE TABLE (required by `.ported`), four clauses against \
__init__.py:446-454. (1) `len(data) != 64 -> InvalidParameter` is syntactically the port's \
`if data.length ≠ 64 then throw` (PrecompilesBls.lean:79). (2) `c = int.from_bytes(data[:64], \
\"big\")` vs `bytesBEtoNat data`: `data[:64] = data` follows from clause 1 and is DISCHARGED \
by the theorem's `hlen`; `int.from_bytes(·,\"big\")` vs `Nat.fromBytesBE` is READ, not \
proved. (3) `c >= FQ.field_modulus` vs `c ≥ blsP` needs `FQ.field_modulus = blsP`; py_ecc \
`fields/field_properties.py:29` gives 4002409555221667393417789825735904156556882819939\
007885332058136124031650490837864442687629129015664037894272559787, verified equal to \
`0x1a0111ea…aaab`. (4) `return FQ(c)` vs `pure c`: the port represents the element by its \
`Nat` representative and drops the `FQ` wrapper — immaterial here, since the row claims \
only the accept/reject predicate. \
⚠️ CITATION KIND: clauses 2 and 3 cite CPython's builtin and the EXTERNAL `py_ecc` \
package, not the vendored tree, so `scripts/check-spec-refs.sh` cannot machine-check them \
the way it checks a `forks/.../x.py:NNN` line — they are read, not verified. See \
docs/agents/spec-correspondence.md 6a. \
⚠️ BASE FIELD, NOT SCALAR ORDER: #11574 as filed paired this routine with \
`Kzg.bytes_to_bls_field` / `BLS_MODULUS`, the 255-bit scalar order. Different prime, \
different routine (`blsk_lt_be`). `Stateless.Crypto.blsP_ne_blsModulus` pins that they \
differ. See #11574" },
  { family := "crypto", routine := "bnf_lt_p",
    spec := some "bnfLtP_spec_specref",
    verdict := .agrees, basis := .ported,
    reference := "the `x >= field_modulus` guard of Bn128.bytes_to_g1 \
(SpecRef/PrecompilesCurve.lean:85), a port of \
amsterdam/vm/precompiled_contracts/alt_bn128.py:39-82",
    note := "⭐ NO wire-pad gate, unlike the BLS twin, and the asymmetry is real rather \
than an oversight: `bytes_to_g1` reads `buffer_read(data, 0, 32)` directly against a guest \
routine scanning the same 32 bytes, so there is no pad to relate and the restatement is \
TOTAL over 32-byte inputs. \
⚠️ THE SUBJECT IS THE CLAUSE, NOT THE FUNCTION. `bytes_to_g1` also bounds `y` and tests \
`y² = x³ + 3`; this routine looks at neither. `agrees` is graded against the \
`x >= field_modulus` conjunct named in `reference`, which is what \
`bnf_lt_p_agrees_field_bound` states. Grading it as whole-function agreement would be an \
overclaim. \
PORT-FIDELITY CLAUSE TABLE (required by `.ported`), against alt_bn128.py:59-70. \
(1) ⚠️ `len(data) != 64 -> InvalidParameter(\"Input should be 64 bytes long\")` is ABSENT \
from the port. NOT recorded as a `portDefect`: it is UNREACHABLE, because every port call \
site passes `buffer_read data k 64` (PrecompilesCurve.lean:113/115/124) and `buffer_read` \
pads to exactly `size` (Vm.lean:299-301), so the guard's precondition holds at every call. \
An unreachable defensive check is not a behavioural divergence — but a future caller \
handing `bytes_to_g1` a short list WOULD diverge, so it is named rather than dropped. \
(2) `x = int(U256.from_be_bytes(buffer_read(data,0,32)))` vs `bytesBEtoNat (data.take 32)`: \
equal given length 64, where the padding is a no-op; `U256.from_be_bytes` vs \
`Nat.fromBytesBE` is READ, not proved. (3) The Python raises separately for `x` and for \
`y`; the port MERGES them into one disjunction. Same accept/reject set, and identical \
message anyway — and immaterial to this row, which claims only the `x` conjunct. Reason \
strings are not compared (harness contract, docs/agents/spec-correspondence.md 9). \
(4) `field_modulus` is syntactically the port's `fieldModulus`, same decimal literal; \
the Python imports it from py_ecc `fields/field_properties.py:24`, verified identical. \
⚠️ CITATION KIND: clauses 2 and 4 cite CPython and EXTERNAL `py_ecc`, not the vendored \
tree — read, not machine-checked. See #11574" }
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

theorem registry_size : registry.length = 31 := by decide
theorem rlp_rows : countFamily "rlp" = 19 := by decide
theorem bal_rows : countFamily "bal" = 2 := by decide
/-- #11352. One row so far; the family has no differential (see the row's note). -/
theorem guest_rows : countFamily "guest" = 1 := by decide
/-- #11349, #11351. No differential for this family -- see the rows' notes. -/
theorem header_rows : countFamily "header" = 4 := by decide
/-- #11344. No differential for this family -- see the row's note. -/
theorem mpt_rows : countFamily "mpt" = 1 := by decide
/-- #11516. One row; the pairing that issue says must be stated. -/
theorem account_rows : countFamily "account" = 1 := by decide
/-- #11348. One row; the reference counterpart is constructed in BloomAlgebra rather
    than found in the fork spec -- see the row's note. -/
theorem bloom_rows : countFamily "bloom" = 1 := by decide
/-- #11574. Two rows, the family's first. Both machine triples predated the rows
    by months — the gap was vocabulary and registration, not proof. -/
theorem crypto_rows : countFamily "crypto" = 2 := by decide

/-- ⚠️ `stricter` is still **0**, and #11513/#11620 is the worked example of why
    that is not automatically a sign the schema has stopped discriminating.

    `header_extract_number` looked like it belonged here: the guest bounds
    `number` at eight bytes where the reference's `Uint` has no bound at all,
    which reads as a false reject. It is not one, because evm-asm states a
    project-wide assumption that these header fields arrive within their
    bit-width, and the maintainer ruling on #11620 is that this "gives the guest
    freedom to choose its behavior" — rejecting out-of-assumption input is
    *preferred*. `stricter` means "we reject input the reference accepts **and
    the project claims to handle**"; a stated precondition is not that.

    The guard against this becoming a rubber stamp is that the precondition must
    be **explicit in the theorem statement** — here `hfits : hdr.number < 2 ^ 64`
    on `header_number_of_decode`. Grading a restriction as a precondition while
    leaving it implicit in the guest's behaviour is worse than recording an FR,
    because an FR at least appears in this census. -/
theorem verdict_counts :
    countVerdict .agrees = 18 ∧ countVerdict .domainRestricted = 9 ∧
    countVerdict .stricter = 0 ∧ countVerdict .looser = 0 ∧
    countVerdict .noCounterpart = 2 ∧ countVerdict .unproven = 2 := by decide

/-- Port defects are counted separately because they are a different axis.
    **Back to 0 as of #11513**, which fixed the one defect that had been
    recorded: `_decode_header`'s numeric fields now carry the canonicality check
    `_deserialize_to_uint` performs. The axis stays in the schema — #11493's
    design argument is about representability, not about this row. -/
theorem port_defect_count : countPortDefect = 0 := by decide

theorem basis_counts :
    countBasis .diff = 1 ∧ countBasis .bridged = 12 ∧
    countBasis .ported = 8 ∧
    countBasis .machineOnly = 3 ∧ countBasis .inspection = 5 ∧
    countBasis .none = 2 := by decide

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
