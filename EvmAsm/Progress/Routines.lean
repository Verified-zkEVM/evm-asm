/-
  EvmAsm.Progress.Routines

  Drift-proof registry of **verified guest routines** — the non-opcode half of
  the verified surface (GH #11042).

  ## Why this is a second registry rather than added rows

  `EvmAsm.Progress.registry` is `OpcodeEntry`-shaped: every row is an EVM
  opcode, keyed on the mnemonic, carrying `cycleBound` and opcode-shaped
  fields. A guest routine (`rlp_encode_uint_be`, `rlp_item_size`, the RLP walk
  chain) has no opcode name to key on, so it cannot be a row there. The
  consequence, before this module existed, was that **no guest-routine spec was
  covered by `scripts/check-axioms.sh`** — the kernel-truth gate audits exactly
  what the opcode registry classifies. `rlp_encode_uint_be` is the case that
  surfaced it: the whole-routine triple `reub_spec_within` is the strongest
  claim this repo makes about that routine, and nothing was witnessing it.

  ## Why this lives beside `EvmAsm.Progress` rather than inside it

  Witnessing a guest routine means importing the module that proves it, and
  those live under `EvmAsm.Codegen.Programs.*` (815 modules) — the part of the
  tree with the most churn. `EvmAsm.Progress` is imported by
  `Progress.Correspondence`, `Progress.Obligations` and
  `Progress.AxiomWitnesses`; pulling Codegen into it would make every Codegen
  edit rebuild the opcode gate. Keeping the routine registry in a sibling
  module leaves the opcode side's rebuild cost unchanged. `ProofTier` is shared
  (imported), so the two registries stay classified on one scale.

  ## Rows are witnesses, not routines

  `symbol` **groups** rows; it is not a key. A routine covered per-form (the
  RLP walk chain proves `rlp_walk_next` separately for the scalar form and for
  account fields 0 and 1) gets one row per theorem. Collapsing those into a
  single row would have to name one theorem as *the* witness for the symbol,
  which would overstate what any one of them proves — the failure mode this
  registry exists to prevent.

  ## Reading `ProofTier` for a routine

  Every triple carries resource preconditions (dword alignment,
  `isValidByteAccess`, non-overflow of `base + len`) and the caller-supplied
  register frame. Those are the ABI, not a gap, and do **not** make a row
  `.conditional`.

  * `.proven` — whole-routine triple, resource/ABI preconditions only.
  * `.conditional` — the same, plus a **nonvacuous input-domain gate** that
    excludes inputs the routine's symbol could otherwise be asked about (an RLP
    short-form `≤ 55` bound, a `SpanForm` restriction). `gate` names it in
    prose so the registry states *what* is excluded rather than hiding it
    behind a tier constructor.

  See `EvmAsm/Progress.lean` for the opcode registry and the witness-`abbrev`
  convention this file follows.
-/

import EvmAsm.Progress
import EvmAsm.Progress.Correspondence
import EvmAsm.Rv64.RLP.WalkNextStrict
-- #12033: the machine tie for the STRICT wrapper relation.
import EvmAsm.Codegen.Programs.RlpWalkNextStrictTie
import EvmAsm.Codegen.Programs.BloomOrIntoBridge
import EvmAsm.Evm64.AccountAccessorSpec
import EvmAsm.Codegen.Programs.RlpEncodeUintBeComposeSAsm
import EvmAsm.Codegen.Programs.RlpEncodeBytesComposeSAsm
import EvmAsm.Codegen.Programs.RlpSpliceHelperSpec
import EvmAsm.Codegen.Programs.RlpItemSpanBody
-- #10780 item 3: the 2-length-byte long form, in a sibling module because
-- RlpSpliceHelperSpec is at the 1500-line cap.
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong2Spec
import EvmAsm.Codegen.Programs.RlpBytesEncodedSizeSAsm
import EvmAsm.Codegen.Programs.RlpBytesEncodedSizeBridge
import EvmAsm.Codegen.Programs.HeaderExtractNumberSpec
import EvmAsm.Codegen.Programs.HeaderExtractLogsBloomBridge
import EvmAsm.Codegen.Programs.HeaderValidateExtraDataLengthBridge
import EvmAsm.Codegen.Programs.HeaderExtractNumberBridge
import EvmAsm.Codegen.Programs.AccountDecodeCompose
-- #11516: AccountDecodeCompose imports AccountDecodeBridge, not Close6, so the
-- whole-routine triple's module has to be imported explicitly for its witness.
import EvmAsm.Codegen.Programs.AccountDecodeClose6
import EvmAsm.Codegen.Programs.AccountAccessorNonceSpec
import EvmAsm.Codegen.Programs.AccountAccessorTopSpec
import EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose6
import EvmAsm.Codegen.Programs.ReceiptExtractLogsBloomSpec
import EvmAsm.Codegen.Programs.AccountEip161LeniencyBridge
import EvmAsm.Codegen.Programs.RlpFieldToU256BeWholeSAsm
import EvmAsm.Codegen.Programs.RlpFieldToU64WholeSAsm
import EvmAsm.Codegen.Programs.RlpListEncodedSizeSAsm
import EvmAsm.Codegen.Programs.RlpListEncodedSizeBridge
import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Codegen.Programs.RlpListCountItemsSAsm
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixCanonical
import EvmAsm.Codegen.Programs.RlpItemSizeLongSpec
import EvmAsm.Codegen.Programs.RlpItemSizeTotalSpec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLoopSpec
-- #10817: `bal_canonical_sort`'s nibble extractor against a SEMANTICALLY decoded
-- key. A block lemma over the whole routine's `CodeReq`, not a routine triple.
import EvmAsm.Codegen.Programs.BalCanonicalSortDigitSpec
-- #10780 item 3, next width: the 3-length-byte long form, first arm to cite
-- `lpLolLoop` instead of unrolling the length-byte loop.
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong3Spec
-- #10780 item 3, next width: the 4-length-byte long form. Long3's ladder with
-- ONE more fall-through, plus `lpLolLoop` cited at `m := 4`.
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong4Spec
-- #10780 item 3, widths 5/6/7: each is long4's ladder with one more fall-through
-- per width, plus `lpLolLoop` cited at `m := 5`/`6`/`7`. `lenlen = 8` is NOT here —
-- its loop overflow side condition needs `outPtr.toNat + 9 ≤ 2 ^ 64`, which is one
-- byte more than `outPtr.toNat % 8 = 0` supplies.
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong5Spec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong6Spec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong7Spec
-- #12038 opening move on the signing-hash lane: the K147 EIP-7702
-- authorization-signing-hash wrapper, whole-routine, under a named
-- unproven-callee residual for K145 `tx_signing_hash`.
import EvmAsm.Codegen.Programs.Eip7702AuthSigningHashTop
import EvmAsm.Codegen.Programs.AccountDecodeCorrespondence
import EvmAsm.Codegen.Programs.SpecRefConstantPins
import EvmAsm.Codegen.Programs.RlpListCountItemsBridge
import EvmAsm.Codegen.Programs.BgvU32leSpec
import EvmAsm.Codegen.Programs.ExecutionRequestsHashBgvOffset
import EvmAsm.Codegen.Programs.CheckGasLimitBridge
import EvmAsm.Codegen.Programs.BytesToNibblesBridge
import EvmAsm.Codegen.Programs.WithdrawalDecodeClose5
import EvmAsm.Codegen.Programs.CryptoFieldLtPBridge
-- #11799 dep: whole-routine mpt_node_kind machine triple (Wrap holds the capstone).
import EvmAsm.Codegen.Programs.MptNodeKindWrap
import EvmAsm.Codegen.Programs.MptNodeKindWire
-- #11800 node-DB half: whole-routine machine triple for `node_db_lookup`.
import EvmAsm.Codegen.Programs.NodeDbLookupSpec
-- #12036: `witness_lookup_by_hash` ABI frame, telemetry idiom, and the
-- whole-routine triple on the `section_len = 0` domain.
import EvmAsm.Codegen.Programs.WitnessLookupByHashSpec
import EvmAsm.Codegen.Programs.ExecutionRequestsHashWrap
-- #12011 hash-half: erh_hash_one empty+nonempty tops under residual h_sha
-- (no whole-routine row yet; witnesses still required for axiom gate).
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneTop
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneNonemptyTop
import EvmAsm.Codegen.Programs.HpDecodeNibblesSAsmPaths
import EvmAsm.Codegen.Programs.HpDecodeCompactBridge
-- #11575 tier A: the whole-routine triples live in the `LoopClose` modules (the
-- `Spec` modules hold only the prologue/epilogue/return-path blocks), so it is
-- those that have to be imported for the witness abbrevs to force.
import EvmAsm.Codegen.Programs.ChainValidateConsecutiveNumbersLoopClose
import EvmAsm.Codegen.Programs.ChainValidatePostMergeFullSpec
import EvmAsm.Codegen.Programs.ChainValidateIncreasingTimestampsLoopClose
import EvmAsm.Codegen.Programs.ChainValidateGasUsedUnderLimitLoopClose
import EvmAsm.Codegen.Programs.ChainValidateBlobGasMultipleLoopClose
import EvmAsm.Codegen.Programs.ChainValidateBlobGasUnderMaxLoopClose
import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthLoopClose
import EvmAsm.Codegen.Programs.TxTypeDispatchTop
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTop
import EvmAsm.Codegen.Proofs.HashBridgeKeccakBridge
import EvmAsm.Codegen.Proofs.HashBridgeSha256Frame
import EvmAsm.Codegen.Proofs.HashBridgeSha256Setup
import EvmAsm.Codegen.Proofs.HashBridgeSha256Block
import EvmAsm.Codegen.Proofs.HashBridgeSha256Outer

namespace EvmAsm.Progress

/-- One row of the guest-routine registry: a **witness theorem** for a claim
    about a linked guest symbol.

    `symbol` groups rows rather than keying them — see this module's header on
    why a per-form routine gets one row per theorem. -/
structure RoutineEntry where
  /-- The guest symbol the claim is about, as it appears in the linked image
      (`rlp_encode_uint_be`, `rlp_item_size`, …). Not unique across rows. -/
  symbol : String
  /-- Verification depth, on the same `ProofTier` scale as the opcode
      registry. See this module's header for how the tiers read for a
      routine. -/
  tier : ProofTier
  /-- Witness theorem name, unqualified. Every row's `proofRef` must have a
      matching witness `abbrev` below — `scripts/gen-axiom-witnesses.py`
      cross-checks this and fails loudly on a row without one, because a row
      whose theorem is never forced is a row the axiom gate cannot see. -/
  proofRef : Option String
  /-- For a `.conditional` row: the input-domain gate, in prose. Empty for
      `.proven`. Stated so the registry says what is excluded rather than
      leaving it to be discovered in the theorem statement. -/
  gate : String := ""
  /-- Optional short note for the rendered report. -/
  notes : String := ""
  deriving Repr

/-- Smart constructor for a routine row, mirroring `EvmAsm.Progress.entry`
    (`Progress.lean`) so the defaulted trailing fields stay omittable — the
    anonymous `⟨…⟩` constructor cannot skip them. -/
def routine (symbol : String) (tier : ProofTier) (proofRef : Option String)
    (gate : String := "") (notes : String := "") : RoutineEntry :=
  { symbol, tier, proofRef, gate, notes }

/-! ## Registry

    Grouped by guest symbol. This is a **partial** enumeration of the verified
    guest surface — see `routineCount` below and the module docstring in
    `EvmAsm/Progress/AxiomWitnesses.lean` for what is not yet covered. -/
def routineRegistry : List RoutineEntry := [
  -- `rlp_encode_uint_be` — the routine whose uncovered triple surfaced #11042.
  routine "rlp_encode_uint_be" .conditional (some "reub_spec_within")
      (gate := "stripped payload `n - reubZeros xs 0 n ≤ 55` — the RLP "
        ++ "short-form bound. Above it the header byte is still computed as "
        ++ "specified but stops being an RLP header, so the routine is out of "
        ++ "domain rather than wrong")
      (notes := "whole-routine triple over the routine's own `reubOut` model; "
        ++ "all three paths (all-zero, raw single byte, header) proved and each "
        ++ "shown to fire on its own inputs"),
  routine "rlp_encode_uint_be" .conditional (some "reub_spec_encode_within")
      (gate := "same `≤ 55` short-form bound as `reub_spec_within`")
      (notes := "the same triple restated against the reference encoding "
        ++ "`encodeBytes (Nat.toBytesBE (Nat.fromBytesBE xs))`, so the claim is "
        ++ "against RLP rather than against the module's own model. The "
        ++ "reference is this repo's Lean port, not the pinned Python — a "
        ++ "port/Python divergence would not be visible here"),
  routine "rlp_encode_uint_be" .conditional (some "reub_spec_within_of_length_le")
      (gate := "`n ≤ 55` — strictly stronger than the tight bound, and the "
        ++ "form a caller can discharge without reasoning about `reubZeros`")
      (notes := "ABI-shaped corollary; every production caller passes 8 or 32"),

  -- `rlp_encode_bytes` — #10780 item 2. Total function: no input-domain
  -- restriction, so `.proven` where `reub` is `.conditional` — both sides of
  -- the 55/56 boundary are inside the claim.
  routine "rlp_encode_bytes" .proven (some "reb_spec_within")
      (notes := "whole-routine triple against `encodeBytes` — the function "
        ++ "SpecRef's own encoders call (`encR := EL.RLP.encode`, and "
        ++ "`encode (.bytes d) = encodeBytes d` definitionally). All three "
        ++ "paths (raw byte, short form, long form) proved; coverage examples "
        ++ "pin output bytes as literals on both sides of 55/56. Resource "
        ++ "preconditions only (capacity `n + 9`, alignment, validity)"),
  routine "rlp_encode_bytes" .proven (some "reb_spec_rlpItem_within")
      (notes := "the same triple with the output region phrased as "
        ++ "`rlpItemRegionFrom outPtr (.bytes data) …` — the `RLPItem` "
        ++ "vocabulary a caller encoding a SpecRef struct field composes with"),

  -- `rlp_item_size` — at its linked guest address, unlike the ∀-base walk triples.
  routine "rlp_item_size" .conditional (some "rlp_item_size_spec_within")
      (gate := "`SpanForm (bs.getD 0 0)` — single byte, short string and short "
        ++ "list forms. The `lenlen ≥ 2` long forms are the documented cut "
        ++ "(#10780 item 3)")
      (notes := "stated at `rlpItemSizeBase = GuestAddrs.rlp_item_size`, the "
        ++ "form the `rlp_item_span` / `mpt_splice_slot` compositions consume"),
  -- #10780 item 3: the two arms `SpanForm` excludes, proved per-form rather than by
  -- widening the gate (`SpanForm` has 50+ consumers; widening it is separate work).
  -- Both cite `risLenLoop` for the length-byte loop instead of unrolling it, so each is
  -- its dispatch path plus the shared idx22-34 tail.
  routine "rlp_item_size" .conditional
      (some "rlp_item_size_long_string_pinned_spec_within")
      (gate := "`0xb8 ≤ p < 0xc0` — the long-string form, one of the two arms "
        ++ "`SpanForm` excludes. Input-domain only; coverRef "
        ++ "`longStringSample_reachable` exhibits the SMALLEST such item (a "
        ++ "56-byte string, exactly the short/long boundary) and checks its span "
        ++ "identity, so the arm is not reachable only in the large")
      (notes := "per-form pinned triple; `a0 = 1 + lenOfLen + fromBytesBE lenBytes`, "
        ++ "spelled in the model's own `rlpPrefixLongBytesLenOfLen` vocabulary. Step "
        ++ "bound `7*lenOfLen + 17`. ⭐ Full identification with `(encode item).length` "
        ++ "is the separate corollary `…_encode_length_spec_within`, because it needs "
        ++ "`decode`/`readLength` facts a machine triple cannot manufacture — folding "
        ++ "them into the triple would have been a weakening"),
  routine "rlp_item_size" .conditional
      (some "rlp_item_size_long_list_pinned_spec_within")
      (gate := "`p ≥ 0xf8` — the long-list form, the other `SpanForm` exclusion. "
        ++ "coverRef `longListSample_reachable`. Every block header RLP is a long "
        ++ "list, so this arm is on the common path, not an edge case")
      (notes := "per-form pinned triple, step bound `7*lenOfLen + 18` (one dispatch "
        ++ "step more than the long-string arm). The payload's own well-formedness is "
        ++ "NOT part of the gate: `rlp_item_size` computes a span and does not descend"),
  -- #11577: whole-routine span under short-list outer + WalkedSpanForm on
  -- every walked prefix. Lifts the leaf-routine-targets exclusion (verified
  -- set includes .conditional). Callers inherit the SpanForm domain.
  routine "rlp_item_span" .conditional (some "rlp_item_span_spec_within")
      (gate := "short-list outer (`payloadLen items ≤ 55`) and "
        ++ "`WalkedSpanForm items i` (SpanForm on every walked item 0..i, "
        ++ "including the target). Long-list outer header and non-SpanForm "
        ++ "walked items uncovered. coverRef "
        ++ "`rlp_item_span_precondition_reachable`")
      (notes := "stated at `rlpItemSpanBase = GuestAddrs.rlp_item_span`; "
        ++ "callee size via offset-framed `rlp_item_size_offset_spec_within`"),

  -- The RLP walk chain / account accessors.
  routine "rlp_walk_init" .proven (some "account_rlp_walk_init_spec_within")
      (notes := "∀-base triple over `rlp_walk_init_code`; opens an "
        ++ "`encodeAccount` list and leaves the field cursor at `listBase + 2`. "
        ++ "⚠️ This is the ACCOUNT-SPECIALISED triple. The form-generic routine "
        ++ "spec is a different theorem — `EvmAsm.Rv64.RLP.rlp_walk_init_"
        ++ "spec_within` (`Rv64/RLP/WalkInit.lean`) — witnessed via the "
        ++ "correspondence registry, not from here. Two theorems share the "
        ++ "unqualified name; do not read either as the other"),
  routine "rlp_walk_init" .conditional (some "rlp_walk_init_long1_spec_within")
      (gate := "`56 ≤ payload.length` — the long-form-1 arm specifically")
      (notes := "per-form companion to the account triple above"),
  routine "rlp_walk_next" .proven (some "account_rlp_walk_next_field0_spec_within")
      (notes := "field 0 (nonce) of an `encodeAccount` list. The form-generic "
        ++ "`EvmAsm.Rv64.RLP.rlp_walk_next_spec_within` is a distinct theorem, "
        ++ "witnessed via the correspondence registry"),
  routine "rlp_walk_next" .proven (some "account_rlp_walk_next_field1_spec_within")
      (notes := "field 1 (balance) of an `encodeAccount` list"),
  routine "rlp_walk_next" .conditional (some "rlp_walk_next_scalar_spec_within")
      (gate := "`(Nat.toBytesBE n).length ≤ 55` — scalar short form")
      (notes := "form-generic scalar arm, not tied to `encodeAccount`"),
  -- #12033: the STRICT wrapper, tied to the machine. This is the first row whose
  -- post carries `rlpItemDecodeStrictW` rather than the core's lenient
  -- `rlpItemDecode`; every other `rlp_walk_next*` row above consumes the 412-byte
  -- core only. The gate is an INPUT-DOMAIN gate, not an unproven callee: the one
  -- callee this triple has (`rlp_walk_next_core`) is proven by
  -- `EvmAsm.Rv64.RLP.rlp_walk_next_spec_within` and is composed here, not assumed.
  routine "rlp_walk_next_shared" .conditional
      (some "rlp_walk_next_shared_nonlist_strict_spec_within")
      (gate := "the item's prefix byte is `< 0xc0` (a byte string, not a list) and "
        ++ "the wrapper's recursion budget `s0` is `≥ 2`. The LIST arms — the ones "
        ++ "that enter `rlp_validate_payload` and recurse — are NOT covered; that "
        ++ "needs a termination measure for the "
        ++ "`shared → validate_payload → nested → shared` cycle. coverRef "
        ++ "`rlp_walk_next_shared_nonlist_strict_instance`, which also exhibits a "
        ++ "closed `rlpItemDecodeStrictW` witness so the accept disjunct is not vacuous")
      (notes := "`cpsTripleWithin 109` over `CodeReq.ofProg GuestAddrs."
        ++ "rlp_walk_next_shared rlpWalkNextShared_prog` unioned with the core at "
        ++ "`GuestAddrs.rlp_walk_next_core`; post carries `rlpItemDecodeStrictW` as a "
        ++ "CONCLUSION. The recursive-payload conjunct is discharged by the wrapper's "
        ++ "OWN prefix load (index 13) and `bltu t1, 0xc0` (index 15), not by a "
        ++ "model-side bridge — `rlpItemDecodeStrictW_to_decodeAux` CONSUMES that "
        ++ "conjunct and so cannot supply it. Reject arms (core status 2..6) are "
        ++ "covered too, carrying `a1 ≠ 0` only"),
  routine "rlp_content_to_u64" .conditional
      (some "account_rlp_content_to_u64_nonce_spec_within")
      (gate := "`a.nonce < 2 ^ 64` — the accessor's u64 output width, narrower "
        ++ "than `Account.nonce`'s own `< 2 ^ 256` invariant")
      (notes := "step bound `7 * (Nat.toBytesBE a.nonce).length + 11`"),
  routine "rlp_content_to_u256_be" .proven
      (some "account_rlp_content_to_u256_be_balance_spec_within")
      (notes := "writes the 32-byte balance; step bound "
        ++ "`7 * (Nat.toBytesBE a.balance.toNat).length + 16`"),

  -- #11925 continuation: `account_extract_nonce` is graded .conditional NOT
  -- .proven (unlike its sibling balance accessor) because the grade is
  -- INHERITED FROM ITS CALLEE, which is already registered .conditional above:
  -- `rlp_content_to_u64` (Routines.lean:204) carries the identical
  -- `a.nonce < 2 ^ 64` gate with the prose below, and the top-level triple
  -- repeats that exact hypothesis. Two structurally identical gates cannot
  -- carry different tiers. The satisfying instance is trivial: any `Account`
  -- whose nonce fits a u64 cell.
  routine "account_extract_nonce" .conditional
      (some "account_extract_nonce_spec_within")
      (gate := "`a.nonce < 2 ^ 64` — the accessor's u64 output width, narrower "
        ++ "than `Account.nonce`'s own `< 2 ^ 256` invariant")
      (notes := "grade inherited from its callee `rlp_content_to_u64`, which is "
        ++ "`.conditional` at Routines.lean:204 with this exact gate; every "
        ++ "dead code path carries a total post; step bound 139"),

  -- #11289: the RLP size / field / list routines whose specs `Correspondence`
  -- names but nothing witnessed. All whole-routine triples at their linked
  -- guest addresses (`B := GuestAddrs.<symbol>`), confirmed via the correspondence
  -- registry's `spec` refs. Tiers read per this module's header: only a
  -- nonvacuous input-domain gate is `.conditional`; buffer-slack, alignment,
  -- `isValidByteAccess`, register encoding and u64-representability are ABI.
  routine "rlp_bytes_encoded_size" .proven (some "rlpBytesEncodedSize_spec")
      (notes := "total: computes `rbesSize` for any byte payload whose length "
        ++ "matches the `len` register; only ABI hyps (ptr/len consistency, "
        ++ "alignment, validity)"),
  -- #11341: the same triple with its post restated over the SHARED MODEL
  -- (`EL.RLP.encodeBytes`) instead of the local `rbesSize`, via the bridge
  -- `rbesSize_eq_encodeBytes_length`. Both rows are kept: the machine-level
  -- theorem is still the thing proved, and this one is what makes the
  -- Correspondence row `.bridged` rather than `.machineOnly`.
  routine "rlp_bytes_encoded_size" .proven (some "rlpBytesEncodedSize_encode_spec")
      (notes := "model-facing restatement: `a0 = (EL.RLP.encodeBytes xs).length`. "
        ++ "One rewrite over `rlpBytesEncodedSize_spec`; the extra `hbound` is a "
        ++ "64-bit non-overflow guard on the register, an ABI hyp, not a domain gate"),
  routine "rlp_field_to_u256_be" .proven (some "rlpFieldToU256Be_spec_within")
      (notes := "whole-routine triple over the `…Whole` module; 32-byte output "
        ++ "buffer, list-slack and register-encoding hyps are ABI, no form gate"),
  routine "rlp_field_to_u64" .proven (some "rlpFieldToU64_spec_within")
      (notes := "companion to `rlp_field_to_u256_be` for the u64 field width"),
  routine "header_extract_logs_bloom" .proven
      (some "headerExtractLogsBloom_spec_within")
      (notes := "field-6 (`bloom`) extractor: prologue ;; `rlp_list_nth_item` at index 6 "
        ++ ";; a 256-byte copy loop ;; epilogue. Whole-routine triple predates its "
        ++ "correspondence row, like #11351's. Its step bound is DATA-DERIVED (the "
        ++ "`7 * 256` factor is the bloom copy), so unlike the numeric siblings it does "
        ++ "NOT inherit #11461's `7 * (2^64 - 1)` tail factor. Model tie "
        ++ "`header_logs_bloom_of_decode` is unconditional on the field width: #11615 "
        ++ "made the port perform the `FixedBytes` check the reference performs, so "
        ++ "`len = 256` is derived rather than assumed"),
  routine "header_validate_extra_data_length" .proven
      (some "header_validate_extra_data_length_spec_within")
      (notes := "field-12 (`extra_data`) length rule: prologue ;; `rlp_list_nth_item` at "
        ++ "index 12 ;; compare against 32 ;; epilogue. K20 only, so NO `7 * (2^64 - 1)` "
        ++ "factor -- #11461 does not reach this routine. ⚠️ Its model tie "
        ++ "`header_extra_data_length_of_decode` crosses a DIFFERENT comparison boundary "
        ++ "from the other header rows: `extra_data` is plain `Bytes` and unbounded at "
        ++ "decode time, so the <=32 rule is a `validate_header` clause "
        ++ "(SeamShell.lean:248), not a `_decode_header` field check. The tie is an IFF on "
        ++ "the decision, because the guest's a0=0/a0=1 guard is total over the field"),
  routine "header_extract_number" .proven (some "header_extract_number_spec_within")
      (notes := "8-instruction wrapper: prologue ;; `rlp_field_to_u64` at field index 8 "
        ++ ";; epilogue. The whole-routine triple predates the correspondence row "
        ++ "(#11351) -- a missing row was never evidence of a missing proof. Its step "
        ++ "bound inherits the callee's loose `7 * (2^64 - 1)` tail factor; tracked at "
        ++ "the origin as #11461"),
  -- #11575, tier A. Both triples ALREADY EXISTED, sorry-free, and were named in
  -- `scripts/registry-coverage-allow.txt` as "registrable as .proven, not yet
  -- rowed" -- the #11637 row-existence class, where proven work counts toward
  -- nothing. #11351's note applies verbatim: a missing row was never evidence of
  -- a missing proof. Registering them here drains those two allowlist entries.
  --
  -- Graded `.proven`, not `.conditional`: every hypothesis is resource/ABI --
  -- `hspC` (frame base), `hret` (ret alignment), `hnWord` (definitional),
  -- `hN : lengths.length < 2 ^ 64`, and the six `hAll*` per-header alignment /
  -- length / slack / non-overflow / `isValidByteAccess` facts. Per this module's
  -- header those are the ABI, not a gap. There is NO input-domain gate: the
  -- three-way post is total over the header list.
  routine "chain_validate_consecutive_numbers" .proven
      (some "chain_validate_consecutive_numbers_spec_within")
      (notes := "93-instruction cross-header accessor: validates RLP field 8 (`number`) is "
        ++ "CONSECUTIVE across adjacent headers (`num[i] = num[i-1] + 1` in `BitVec 64`; the "
        ++ "guest's `ADDI x29 x29 1` then `BNE x29 x28`). Three-way post over the TRUE count: "
        ++ "all-consecutive (`a0 = 0`, `*validPtr = 1`), first-violation (`a0 = 0`, "
        ++ "`*validPtr = 0`, `*firstBad = k`), first parse-failure (`a0 = status ≠ 0`, "
        ++ "`*firstBad = k`) -- each header's number genuinely decoded via K34's `Result`, "
        ++ "`prev` threaded through `cvcn_iter_prev`. ⚠️ ONE stated `BitVec`-vs-`Nat` "
        ++ "divergence from the execution spec's `header.number = parent.number + 1`: the "
        ++ "wraparound at `num[i-1] = 2^64-1`, which has no u64-decodable successor and so is "
        ++ "unreachable. Step bound inherits the K34 callee's `7 * (2^64 - 1)` tail factor "
        ++ "(#11461). No `Correspondence` row yet -- that needs a `_of_decode` bridge to "
        ++ "`SpecRef`, which does not exist for this family (see #11575)"),
  routine "chain_validate_increasing_timestamps" .proven
      (some "chain_validate_increasing_timestamps_spec_within")
      (notes := "cross-header accessor with the SAME frame, hypothesis set and three-way "
        ++ "post shape as `chain_validate_consecutive_numbers` above, over the timestamp "
        ++ "field instead of `number` (`Ts` scratch cell in place of `Num`) and a strict "
        ++ "increase instead of a `+1` step. Step bound inherits the same K34 "
        ++ "`7 * (2^64 - 1)` factor (#11461). No `Correspondence` row yet, same reason"),
  -- Graded `.proven`, not `.conditional`: identical shape to the two twins above
  -- (same frame, hypothesis set and three-way total post), just a `< limit` upper
  -- bound on the `gas_used` field instead of a `+1`/strict-increase step. Both
  -- twins were graded `.proven`; this triple is a DIRECT `cpsTripleWithin`,
  -- structurally identical to `chain_validate_consecutive_numbers` (no
  -- `Fn`/`Fn.retSpecFlat`), so grading it tier B on the allowlist would put two
  -- structurally identical triples at different grades. Every hypothesis is
  -- resource/ABI (`hspC` frame base, `hret` ret alignment, `hnWord` definitional,
  -- `hN : lengths.length < 2 ^ 64`, and the six `hAll*` per-header facts); there
  -- is NO input-domain gate, the post is total over the header list. Former allowlist
  -- entry drained (#11575). No `Correspondence` row yet -- same missing
  -- `_of_decode` bridge as the twins.
  routine "chain_validate_gas_used_under_limit" .proven
      (some "chain_validate_gas_used_under_limit_spec_within")
      (notes := "cross-header accessor with the SAME frame, hypothesis set and three-way "
        ++ "post shape as its `chain_validate_consecutive_numbers` / "
        ++ "`chain_validate_increasing_timestamps` twins, over the `gas_used` field "
        ++ "against a `< limit` upper bound (guest's `SLTU`-style comparison) instead of "
        ++ "a `+1`/strict-increase step. Direct `cpsTripleWithin` form identical to the "
        ++ "twins (drained the tier-B allowlist entry, which miscategorised it). Step "
        ++ "bound inherits the same K34 `7 * (2^64 - 1)` factor (#11461). No "
        ++ "`Correspondence` row yet, same reason"),

  -- Graded `.proven`, not `.conditional`, for the same reason as
  -- `chain_validate_gas_used_under_limit` above: direct `cpsTripleWithin` forms
  -- structurally identical to the registered twins. Each of the three reads like
  -- an input-domain gate (`value is a multiple of GAS_PER_BLOB`, `value under
  -- MAX_BLOB_GAS_PER_BLOCK`, `extra_data length <= 32`) but in every case that
  -- property is the OUTPUT the routine verifies, declared in the postcondition
  -- (three-way: all-valid / first-violation / first parse-failure) — NOT a
  -- hypothesis restricting the inputs. The hypothesis set is exactly the ABI-only
  -- one (`hspC`, `hret`, `hnWord`, `hN`, six `hAll*`), same as the twins. All
  -- three were grade tier-B on the allowlist as "needs Fn.retSpecFlat"; that is
  -- false, there is no `Fn`/`Fn.retSpecFlat` in any of the three files, so the
  -- allowlist entries are drained below (#11575).
  routine "chain_validate_blob_gas_used_multiple" .proven
      (some "chain_validate_blob_gas_used_multiple_spec_within")
      (notes := "cross-header accessor identical in frame, hypothesis set and three-way "
        ++ "post shape to the `chain_validate_*` twins, over field 17 (`blob_gas_used`), "
        ++ "checking `value &&& (GAS_PER_BLOB - 1) = 0` (multiple of `GAS_PER_BLOB "
        ++ "= 131072 = 2^17`). THAT multiple-of check is the post output, not an input "
        ++ "gate. Step bound inherits the K34 `7 * (2^64 - 1)` factor (#11461). No "
        ++ "`Correspondence` row yet, same missing `_of_decode` bridge"),
  routine "chain_validate_blob_gas_used_under_max" .proven
      (some "chain_validate_blob_gas_used_under_max_spec_within")
      (notes := "cross-header accessor identical in frame, hypothesis set and three-way "
        ++ "post shape to the `chain_validate_*` twins, over field 17 (`blob_gas_used`), "
        ++ "checking `value <= MAX_BLOB_GAS_PER_BLOCK = 2752512`. THAT under-max check "
        ++ "is the post output, not an input gate. Step bound inherits the K34 "
        ++ "`7 * (2^64 - 1)` factor (#11461). No `Correspondence` row yet, same missing "
        ++ "`_of_decode` bridge"),
  routine "chain_validate_extra_data_length" .proven
      (some "chain_validate_extra_data_length_spec_within")
      (notes := "cross-header accessor identical in frame, hypothesis set and three-way "
        ++ "post shape to the `chain_validate_*` twins, over field 12 (`extra_data`), "
        ++ "checking the RLP content length <= 32. THAT length bound is the post "
        ++ "output, not an input gate. Step bound inherits the K34 `7 * (2^64 - 1)` "
        ++ "factor (#11461). No `Correspondence` row yet, same missing `_of_decode` "
        ++ "bridge"),

  -- #11925 continuation: the first registrations out of scripts/proof-frontier.py's
  -- present-but-unrowed bucket (the #11637 row-existence debt). All four are direct
  -- whole-routine `cpsTripleWithin` triples found live by the frontier census; the
  -- `hbound`-style hypotheses each carries are STATIC input well-formedness / slack
  -- facts tied to the decode predicates, not runtime-outcome gates — the posts stay
  -- total disjunctions that still state the failure branches. Graded `.proven`.
  routine "account_decode" .proven (some "account_decode_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.account_decode`: decodes the "
        ++ "RLP account record (balance/root/codeHash) to `a0 = 0` with a total "
        ++ "whole-routine post `adWholePost`. Every hypothesis is ABI/resource "
        ++ "(`hspW` frame base, `hret` ret alignment, `hlenW` definitional, and "
        ++ "align/slack/over/valid for the input region plus the three output cells). "
        ++ "No input-domain gate"),
  routine "account_extract_balance" .proven (some "account_extract_balance_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.account_extract_balance`: writes "
        ++ "`word256Bytes32 a.balance` and returns `a0 = 0`. Its callee "
        ++ "`rlp_content_to_u256_be` is itself `.proven` (Routines.lean:207), and its "
        ++ "only value-shaped hypothesis is `hnonce : a.nonce < 2 ^ 256` — the "
        ++ "NATURAL `Word256` bound, not a restriction (identical to the u256 callee's "
        ++ "own hypothesis). All other hyps are ABI/resource. No input-domain gate"),
  routine "account_is_eip161_empty" .proven (some "account_is_eip161_empty_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.account_is_eip161_empty`: the post "
        ++ "`aieOutcome` is a TOTAL 4-way disjunction on `(a0, outVal)` — "
        ++ "`accountEip161Empty` verdict, non-empty verdict, and two error statuses. "
        ++ "EIP-161 empty-ness is the OUTPUT the routine verifies, not a precondition. "
        ++ "Hyps are ABI/resource plus a static slack hypothesis over the RLP decode "
        ++ "predicate. No input-domain gate; axiom-clean confirmed via lean_verify"),
  routine "receipt_extract_logs_bloom" .proven (some "receiptExtractLogsBloom_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.receipt_extract_logs_bloom`: the "
        ++ "post `relbRetPost` is a TOTAL 3-way disjunction — success with the 256-byte "
        ++ "bloom copied, success with a short/long payload left intact, and the RLP "
        ++ "decode-failure arm. `hbound` is a static slack fact keyed on the input's "
        ++ "`Success` decode predicate (so the COPY target is in range), not a runtime "
        ++ "outcome gate — the failure branch is still stated. ABI/resource hyps only; "
        ++ "calls RlpFieldToU64SAsm.code"),

  routine "rlp_list_encoded_size" .proven (some "rlpListEncodedSize_spec")
      (notes := "total: the result covers BOTH the `ult v 56` short branch and "
        ++ "the long branch, so it is not form-gated — the only hyp is `halignRet`"),
  -- #11341: the same triple restated over the SHARED MODEL
  -- (`(EL.RLP.encode (.list items)).length`) via `rlesSize_eq_encode_list_length`.
  -- The machine row above states its formula INLINE and unnamed; `rlesSize` in the
  -- bridge module names it (definitionally the same), which is what made the
  -- comparison statable at all.
  routine "rlp_list_encoded_size" .proven (some "rlpListEncodedSize_encode_spec")
      (notes := "model-facing restatement: `a0 = (EL.RLP.encode (.list items)).length` "
        ++ "for any item list whose encoded payload is `a0` bytes long. One rewrite "
        ++ "over `rlpListEncodedSize_spec`; `hbound` is 64-bit non-overflow, an ABI hyp"),
  routine "rlp_list_nth_item" .proven (some "rlpListNthItem_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.rlp_list_nth_item`; the "
        ++ "consumer of the account decode / apply paths"),
  routine "rlp_list_count_items" .proven (some "rlp_list_count_items_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.rlp_list_count_items`"),
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_short_pinned_spec_within")
      (gate := "`len.toNat < 56` — the RLP short-form list-prefix bound. The "
        ++ "`lenlen ≥ 2` long forms are the documented cut (#10780 item 3), the "
        ++ "same boundary as `rlp_item_size`")
      (notes := "per-form (\"short\") pinned triple; writes header byte "
        ++ "`0xC0 + len` and sets the cell flag to 1"),
  -- #10780: the 1-length-byte long form was proven in `RlpSpliceHelperSpec.lean`
  -- but never registered, so it was outside the axiom gate and the registry
  -- undercounted the routine's coverage — the short row's own gate text already
  -- describes the cut as `lenlen ≥ 2`, which only makes sense if lenlen = 1 is
  -- done. Same situation as the #11291 note below: the triple existed, the row
  -- did not. Registering existing work; no new proof.
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long1_pinned_spec_within")
      (gate := "`56 ≤ len.toNat < 256` — the 1-length-byte long form. Together "
        ++ "with the short row this covers `len < 256`; `lenlen ≥ 2` (the "
        ++ "`SLLI`-widened arms) remains the cut, #10780 item 3")
      (notes := "per-form (\"long1\") pinned triple; writes header bytes "
        ++ "`[0xF8, len]` and sets the cell flag to 2. Length-of-length is one "
        ++ "byte and minimal by construction here, so no leading-zero side "
        ++ "condition is needed at this width"),
  -- #10780 item 3: the first arm where the length-byte loop runs MORE THAN ONCE, and
  -- the first where canonical form is a real obligation rather than vacuous.
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long2_pinned_spec_within")
      (gate := "`256 ≤ len.toNat < 65536` — the 2-length-byte long form. With the "
        ++ "short and long1 rows this covers `len < 65536`; `lenlen ≥ 3` remains "
        ++ "the cut")
      (notes := "per-form (\"long2\") pinned triple; writes `[0xF9, len >>> 8, len]` "
        ++ "and sets the cell flag to 3. The length-byte loop runs TWICE here, so "
        ++ "the step bound is 32 rather than long1's 22. ⭐ Canonical form is "
        ++ "discharged separately by `long2_first_length_byte_ne_zero`: the high "
        ++ "byte is nonzero, so the length-of-length carries no leading zero — "
        ++ "vacuous at long1, real from here on"),
  -- #10780 item 3: the first arm that CITES the length-byte loop instead of
  -- unrolling it. `lpLolLoop` (RlpEncodeListPrefixLoopSpec) proves idx35-idx41 at
  -- a symbolic trip count, so this arm is its ladder path plus the fixed
  -- header/epilogue -- which is why it costs 580 lines rather than the ~200/byte
  -- the long2 header priced unrolling at.
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long3_pinned_spec_within")
      (gate := "`65536 ≤ len.toNat < 16777216` — the 3-length-byte long form. With "
        ++ "the short, long1 and long2 rows this covers `len < 16777216`; the cut "
        ++ "moves to `lenlen ≥ 4`")
      (notes := "per-form (\"long3\") pinned triple; writes "
        ++ "`[0xFA, len >>> 16, len >>> 8, len]` and sets the cell flag to 4. Step "
        ++ "bound 42 = 11 ladder + 5 header + 22 loop (`7*3+1`) + 3 epilogue + 1 "
        ++ "`JALR`. ⭐ The loop is CITED, not unrolled: `lpLolLoop` covers "
        ++ "idx35-idx41 at any trip count `≤ 8`, so each further width is its "
        ++ "ladder path plus this same epilogue. Canonical form comes from the "
        ++ "all-widths `first_length_byte_ne_zero`, specialised here as "
        ++ "`long3_first_length_byte_ne_zero`"),
  -- #10780 item 3, next width: long3's ladder with ONE more fall-through. The only
  -- two differences from long3 are the extra dispatch triple (idx17-idx19) and the
  -- loop citation at `m := 4`; header writer, epilogue, frame and clobber set are
  -- identical, which is what long3's closing note predicted.
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long4_pinned_spec_within")
      (gate := "`16777216 ≤ len.toNat < 4294967296` — the 4-length-byte long form. "
        ++ "With the short, long1, long2 and long3 rows this covers "
        ++ "`len < 4294967296`; the cut moved to `lenlen ≥ 5`, which the long5, "
        ++ "long6 and long7 rows below then push to `lenlen ≥ 8`. ⚠️ INPUT-DOMAIN gate "
        ++ "ONLY: `h_out_align`, `h_out_len` and `h_out_valid` are ABI obligations "
        ++ "on the caller-supplied output region, not domain restrictions. coverRef "
        ++ "is the smallest qualifying input, `len = 16777216` — exactly the "
        ++ "long3/long4 boundary, so the gate is REACHABLE and adjacent to already "
        ++ "covered ground rather than merely consistent (#12014)")
      (notes := "per-form (\"long4\") pinned triple; writes "
        ++ "`[0xFB, len >>> 24, len >>> 16, len >>> 8, len]` and sets the cell flag "
        ++ "to 5. Step bound 52 = 14 ladder + 5 header + 29 loop (`7*4+1`) + 3 "
        ++ "epilogue + 1 `JALR` — long3's 42 with three more dispatch steps and "
        ++ "seven more loop steps. ⭐ The loop is CITED at `m := 4`, not unrolled. "
        ++ "Canonical form comes from the all-widths `first_length_byte_ne_zero`, "
        ++ "specialised here as `long4_first_length_byte_ne_zero`. The loop's "
        ++ "overflow side condition is `outPtr.toNat + 5 ≤ 2^64`, which still "
        ++ "closes from `outPtr.toNat % 8 = 0` alone"),
  -- #10780 item 3, widths 5/6/7. Each row is long4's arm with ONE more ladder
  -- fall-through and the loop cited one trip longer; header writer (idx30-34),
  -- epilogue (idx42-44), frame and clobber set are byte-identical across all three,
  -- so the per-width cost really is the three dispatch steps long4 measured.
  -- ⛔ `lenlen = 8` is deliberately absent: see the long7 note.
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long5_pinned_spec_within")
      (gate := "`4294967296 ≤ len.toNat < 1099511627776` — the 5-length-byte long "
        ++ "form. With the short, long1, long2, long3 and long4 rows this covers "
        ++ "`len < 1099511627776`; the cut moves to `lenlen ≥ 6`. ⚠️ INPUT-DOMAIN "
        ++ "gate ONLY: `h_out_align`, `h_out_len` and `h_out_valid` are ABI "
        ++ "obligations on the caller-supplied output region, not domain "
        ++ "restrictions. coverRef is the smallest qualifying input, "
        ++ "`len = 4294967296` — exactly the long4/long5 boundary, so the gate is "
        ++ "REACHABLE and adjacent to already covered ground rather than merely "
        ++ "consistent (#12014)")
      (notes := "per-form (\"long5\") pinned triple; writes "
        ++ "`[0xFC, len >>> 32, len >>> 24, len >>> 16, len >>> 8, len]` and sets "
        ++ "the cell flag to 6. Step bound 62 = 17 ladder (idx 0, 1, 8-22) + 5 "
        ++ "header + 36 loop (`7*5+1`) + 3 epilogue + 1 `JALR` — long4's 52 with "
        ++ "three more dispatch steps and seven more loop steps. ⭐ The loop is "
        ++ "CITED at `m := 5`, not unrolled. Canonical form comes from the "
        ++ "all-widths `first_length_byte_ne_zero`, specialised here as "
        ++ "`long5_first_length_byte_ne_zero`. The loop's overflow side condition "
        ++ "is `outPtr.toNat + 6 ≤ 2^64`, which still closes from "
        ++ "`outPtr.toNat % 8 = 0` alone"),
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long6_pinned_spec_within")
      (gate := "`1099511627776 ≤ len.toNat < 281474976710656` — the 6-length-byte "
        ++ "long form. With the short and long1-long5 rows this covers "
        ++ "`len < 281474976710656`; the cut moves to `lenlen ≥ 7`. ⚠️ INPUT-DOMAIN "
        ++ "gate ONLY: `h_out_align`, `h_out_len` and `h_out_valid` are ABI "
        ++ "obligations on the caller-supplied output region, not domain "
        ++ "restrictions. coverRef is the smallest qualifying input, "
        ++ "`len = 1099511627776` — exactly the long5/long6 boundary, so the gate "
        ++ "is REACHABLE and adjacent to already covered ground rather than merely "
        ++ "consistent (#12014)")
      (notes := "per-form (\"long6\") pinned triple; writes "
        ++ "`[0xFD, len >>> 40, len >>> 32, len >>> 24, len >>> 16, len >>> 8, "
        ++ "len]` and sets the cell flag to 7. Step bound 72 = 20 ladder "
        ++ "(idx 0, 1, 8-25) + 5 header + 43 loop (`7*6+1`) + 3 epilogue + 1 "
        ++ "`JALR`. ⭐ The loop is CITED at `m := 6`, not unrolled. Canonical form "
        ++ "comes from the all-widths `first_length_byte_ne_zero`, specialised "
        ++ "here as `long6_first_length_byte_ne_zero`. The loop's overflow side "
        ++ "condition is `outPtr.toNat + 7 ≤ 2^64`, which still closes from "
        ++ "`outPtr.toNat % 8 = 0` alone"),
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long7_pinned_spec_within")
      (gate := "`281474976710656 ≤ len.toNat < 72057594037927936` — the "
        ++ "7-length-byte long form. With the short and long1-long6 rows this "
        ++ "covers `len < 72057594037927936`; the cut moves to `lenlen ≥ 8`, the "
        ++ "last width. ⚠️ INPUT-DOMAIN gate ONLY: `h_out_align`, `h_out_len` and "
        ++ "`h_out_valid` are ABI obligations on the caller-supplied output "
        ++ "region, not domain restrictions. coverRef is the smallest qualifying "
        ++ "input, `len = 281474976710656` — exactly the long6/long7 boundary, so "
        ++ "the gate is REACHABLE and adjacent to already covered ground rather "
        ++ "than merely consistent (#12014)")
      (notes := "per-form (\"long7\") pinned triple; writes "
        ++ "`[0xFE, len >>> 48, …, len >>> 8, len]` and sets the cell flag to 8. "
        ++ "Step bound 82 = 23 ladder (idx 0, 1, 8-28) + 5 header + 50 loop "
        ++ "(`7*7+1`) + 3 epilogue + 1 `JALR`. ⭐ The loop is CITED at `m := 7`, "
        ++ "not unrolled. Canonical form comes from the all-widths "
        ++ "`first_length_byte_ne_zero`, specialised here as "
        ++ "`long7_first_length_byte_ne_zero`. ⚠️ This is the LAST width alignment "
        ++ "can pay for: the loop's overflow side condition is "
        ++ "`outPtr.toNat + 8 ≤ 2^64`, and `outPtr.toNat % 8 = 0` closes it exactly "
        ++ "(checked: the same `omega` step with `+ 9` does NOT close). So "
        ++ "`lenlen = 8` is out of scope here and needs an explicit bound rather "
        ++ "than alignment"),

  -- #11291: the whole-routine triple already existed (landed 2026-07-17,
  -- closed #10782) but was never registered. It is `wdPrologue ;; wdBBField0`
  -- — the full program — not a per-path certificate, so a single row is the
  -- strongest claim and subsumes the Close2..5 composition chain.
  routine "withdrawal_decode" .proven (some "withdrawal_decode_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.withdrawal_decode`: decodes "
        ++ "all four RLP fields and returns `a0 = 0` with a `Decoded` verdict or "
        ++ "`a0 = 1` with a witnessed `DecodeFailure` — both paths in one triple, "
        ++ "so `.proven` and total (no input-domain gate). The intermediate WP "
        ++ "certificates in `WithdrawalDecode*WP.lean` are the steps this composes"),
  -- #11352 + #11578: `bgv_u32le`. Witness is offset form (covers unaligned a0).
  -- h_align listBase%8=0 is a CALLER assumption (ABI region base), NOT a static
  -- GuestAddrs pin discharged by decide — so `.conditional`, not `.proven`.
  -- coverRef `bgv_u32le_offset_precondition_reachable`. Flat form had the same
  -- gate as Region.wf on a0; moving it to listBase fixed production offs 4/12
  -- but did not erase the alignment hyp.
  routine "bgv_u32le" .conditional (some "bgv_u32le_offset_spec_within")
      (notes := "offset-form triple at GuestAddrs.bgv_u32le: a0=listBase+off "
        ++ "(may be unaligned), bytesRegion listBase bs, post a0=leU32 (bs.drop off) 0. "
        ++ "Gate: h_align listBase.toNat%8=0 remains a caller hyp at erh sites "
        ++ "(listBase is ABI a0, not a static GuestAddrs base). coverRef "
        ++ "`bgv_u32le_offset_precondition_reachable`. Prior flat_spec Region.wf "
        ++ "a0%8=0 does not cover offs 4/12. leU32_eq_bytesLEtoNat still ties value"),

  -- #11349: `check_gas_limit`, row 7 of docs/leaf-routine-targets.md. The machine
  -- triple already existed byte-transparently at the guest address; what this row
  -- registers is the model-facing restatement.
  routine "check_gas_limit" .proven (some "checkGasLimit_ref_spec")
      (notes := "whole-routine triple at `GuestAddrs.check_gas_limit`, post additionally "
        ++ "records `a0 = 0` iff `SpecRef.check_gas_limit` accepts. Full domain, NO "
        ++ "envelope hypothesis: the guest never forms the reference's two sums, it "
        ++ "compares |new - parent| against parent/1024"),

  -- #11344: `bytes_to_nibbles`, row 1 of docs/leaf-routine-targets.md. 10 fixture
  -- in-edges. Flat triple DERIVED from the SAsm `bytesToNibblesFn_spec` by
  -- `Fn.retSpecFlat`, so the counted loop's invariant stays in the SAsm proof.
  routine "bytes_to_nibbles" .proven (some "bytesToNibblesFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bytes_to_nibbles`: the destination "
        ++ "region holds `SpecRef.keyToNibbles (srcBytes.take len)` — the REFERENCE "
        ++ "function, not the routine's own accumulator. ABI hyps only (region wf, "
        ++ "non-overlap, non-overflow, aligned ra)"),

  -- #11799 dep / leaf-routine-targets row 4: whole-routine machine triple for
  -- `mpt_node_kind`. Full guest domain (arity-17 branch / arity-2 HP path /
  -- fail joins) with operational `MptNodeKindResult` post — no input-domain
  -- gate, so `.proven`. Pure `mptNodeKindSpec` (MptAssertions) is looser/stale
  -- vs the arity-exact guest; do not rest the post on it.
  -- #12027: Result→kindTag wiring under WF (success arms kind < 3) lands in
  -- MptNodeKindWire; existence + uniqueness witnessed below.
  routine "mpt_node_kind" .proven (some "mpt_node_kind_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.mpt_node_kind` / `kindB`: "
        ++ "count via `rlp_list_count_items`, nth via `rlp_list_nth_item` index 0, "
        ++ "HP nibble classify for leaf/ext. Post is operational "
        ++ "`MptNodeKindResult` (countFail/branch/badArity/nthFail/emptyPath/path). "
        ++ "POST STRENGTHEN (path preserve, free): x18..x21 stay concrete at "
        ++ "entry values — guest restores them via count/nth saves; old regOwn "
        ++ "export discarded that and blocked hop consumers. PRE unchanged "
        ++ "(already concrete v18..v21 in kindCallerPre/countAmbient). "
        ++ "#12027 wire: `mptNodeKindResult_eq_kindTag` (kind < 3) + "
        ++ "`mptNodeKindResult_exists_kindTag` under WF; encode-domain count "
        ++ "Success + path head HP; no #11341 (WF top-level .bytes only); "
        ++ "supersedes (does not consume) deleted pure guest_eq_kindTag bridge. "
        ++ "coverRef `mpt_node_kind_precondition_reachable`. Callees already "
        ++ "`.proven`; first walker-dispatch machine triple"),

  -- #11799: `hp_decode_nibbles` machine was already proved (HpDecodeNibblesSAsmPaths)
  -- but never registered — residual audit found it RETIRED as a walk dependency.
  -- callWithin adapter: HpDecodeNibblesCallSAsm.
  routine "hp_decode_nibbles" .proven (some "hp_decode_nibbles_spec_ported")
      (notes := "whole-routine triple at `GuestAddrs.hp_decode_nibbles` / symbolic "
        ++ "base: abiFrame over hdnBody; post is guest-exact `hdnRes` (= `hpDecode`) "
        ++ "into nibble buf + count/is-leaf cells. FULL DOMAIN (ABI hyps only). "
        ++ "Registered under #11799 residual audit — machine predated registration. "
        ++ "callWithin adapter `hp_decode_nibbles_call_spec_within` for walk ext/leaf"),

  -- #11574: the two field-bound scans. ⚠️ BOTH machine triples predate this
  -- registration by months and were simply never registered — a name search for
  -- the routines found nothing because the specs are in sibling `*SAsm` modules,
  -- which is the #10779 lesson recurring. What #11574 asked for that genuinely
  -- did not exist is the SpecRef vocabulary, not the triples.
  routine "blsg_lt_p" .proven (some "blsgLtP_spec")
      (notes := "whole-routine triple at `GuestAddrs.blsg_lt_p`: `a0 = 1` iff the "
        ++ "48-byte big-endian input is `< beBytesToNat bls12PBytes`, input and the "
        ++ "read-only prime region intact. ABI hyps only (alignment, non-overflow, "
        ++ "byte-access validity, aligned ra). The `la` materialization of "
        ++ "`blsg_p_be` is PROVEN, not assumed"),
  routine "blsg_lt_p" .conditional (some "blsgLtP_spec_specref")
      (gate := "the input is the 48-byte compact SUFFIX of a well-formed EIP-2537 "
        ++ "wire felt — `w.length = 64` and the first 16 bytes zero. Load-bearing, "
        ++ "not decorative: the reference decodes all 64 bytes, so a nonzero pad "
        ++ "byte makes the value ≥ 2^384 > p and the reference rejects, while the "
        ++ "guest scan never reads those bytes and would not. The two sides agree "
        ++ "exactly ON the well-formed felts")
      (notes := "model-facing restatement: `a0` IS the accept/reject indicator of "
        ++ "`SpecRef.Bls12.bytes_to_fq` on the wire felt. ⚠️ PREDICATE agreement "
        ++ "only — `lt_p` returns a boolean, never the field element, so value "
        ++ "agreement is not available from this routine and is not claimed"),
  routine "bnf_lt_p" .proven (some "bnfLtP_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnf_lt_p`: the BN254 twin of "
        ++ "`blsgLtP_spec` over 32 bytes and `bn254PBytes`. Same ABI-only hyps"),
  routine "bnf_lt_p" .proven (some "bnfLtP_spec_specref")
      (notes := "model-facing restatement: `a0 = 1` iff `bytesBEtoNat xs < "
        ++ "SpecRef.Bn128.fieldModulus`. ⭐ NO wire-pad gate, unlike the BLS twin — "
        ++ "`Bn128.bytes_to_g1` slices `data.take 32` directly, so the guest and the "
        ++ "reference read the same 32 bytes and the restatement is total. ⚠️ It is "
        ++ "the `x`-BOUND CLAUSE of `bytes_to_g1`, not its verdict: that function "
        ++ "also bounds `y` and tests the curve equation, neither of which this "
        ++ "routine looks at"),

  -- #11925 last-of-six: `tx_type_dispatch` re-derived as `.proven` FROM THE
  -- MERGED text of #11929 (not the pre-merge read). #11929 appended the
  -- legacy upper-bound guard (0xff guard; routine 45 -> 48 instructions):
  -- `0xff` moved OUT of the legacy arm into its own FAILURE disjunct. The
  -- post remains TOTAL over the byte: empty, byte at or above 0xc0 and not
  -- 0xff -> legacy; byte equals 0xff -> ff-fail; byte under 0xc0 in 1..4 ->
  -- typed; otherwise -> unknown-fail. A failure disjunct inside a total post
  -- is still a total post. No input-domain precondition on `txBytes` (only
  -- ABI: ra-alignment, 8-aligned base, size bound, byte-access validity).
  routine "tx_type_dispatch" .proven (some "txTypeDispatch_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.tx_type_dispatch` over "
        ++ "the emitted `txTypeDispatch_prog` (48 instrs after #11929's appended "
        ++ "0xff guard). Classifies via `teerTxTypeDispatch`: empty -> fail "
        ++ "(1,0,0); 0xc0..0xfe -> legacy (0,0,0); 0xff -> fail (1,0,0); 1..4 -> "
        ++ "typed (0,N,1); otherwise -> fail (1,0,0). Step budget "
        ++ "`nTxTypeDispatchSteps` = 256; five BGEU witnesses (shared, four "
        ++ "non-taken Typed, unknown) all carry immediate 168 = "
        ++ "`brOff (GuestAddrs.tx_type_dispatch+180) (GuestAddrs.tx_type_dispatch+12)`, "
        ++ "matching the emitted guard target at D+180"),
  -- #11800 follow-on: whole-routine wrapper over #11960 loop framing.
  -- Outer absorb uses signedCountdownLoop_reload_spec (hdr=LI at 0x8000368c);
  -- BLT-header signedCountdownLoop_spec does NOT apply (JAL→LI ≠ BLT 0x80003690).
  -- N/rem is length partition (len=136*N+rem, rem≤135), not an input-domain gate.
  -- Post operational keccakBodyDigest; pure SpecRef bridge absorbed by #12037
  -- (`keccakBodyDigest_eq_specref` / `_div_eq_specref`). Load-bearing consumer #12038.
  routine "zkvm_keccak256" .proven (some "zkvm_keccak256_spec_within")
      (notes := "whole-routine no-ra frame triple at GuestAddrs.zkvm_keccak256 "
        ++ "over zkvmKeccak256_prog (69 insn). Frame saves x8/x9/x18/x20 only "
        ++ "(not ra); JALR x0,x1 ret. Outer absorb loop: LI-header reload "
        ++ "(signedCountdownLoop_reload_spec) because body CSRS clobbers lim x29; "
        ++ "BLT-hdr lemma unapplied (JAL target LI 0x8000368c ≠ BLT 0x80003690). "
        ++ "Post: a0=0, output=keccakBodyDigest; pure SpecRef.keccak256 via "
        ++ "keccakBodyDigest_eq_specref (#12037). Resource/ABI only → .proven"),

  -- #11578 rescope: derive_withdrawal/consolidation_requests are NOT leaves
  -- (7-insn JAL x0 stage_system_call). Validation prefix of
  -- execution_requests_hash instead → hash-entry B+300. Hash half residual.
  -- FULL named gates (binder list, not intent): h_align listBase%8=0 (ABI a0,
  -- not static GuestAddrs pin); h_fit 20≤bs.length; h_ge ¬ult endW 20;
  -- erhOffsetsMonoW; erhGatesOkW. h_valid/h_over = ordinary memory framing.
  routine "execution_requests_hash" .conditional
      (some "execution_requests_hash_validation_accept")
      (notes := "validation-accept prefix at GuestAddrs.execution_requests_hash "
        ++ "(B → B+300, fuel 135): prologue sp-96 + five bgv_u32le offset reads "
        ++ "+ mono + five REMU/DIVU/cap gates. GATES (all caller hyps on the top "
        ++ "triple): h_align listBase.toNat%8=0; h_fit 20≤bs.length; h_ge "
        ++ "¬ult endW 20; erhOffsetsMonoW; erhGatesOkW. h_valid/h_over framing "
        ++ "only. coverRef erh_validation_precondition_reachable (non-empty "
        ++ "deposit 192). Hash half residual. Parked: block_state_root + "
        ++ "requests_hash_verify still String asm"),

  -- #12038 FIRST row on the signing-hash lane (there was none for any
  -- signing hash before this). K147 is the 9-instruction typed wrapper; it
  -- owns exactly the three facts proved here (n=3, MAGIC=0x05, a2→a4 output
  -- forward) and delegates the rest to K145 `tx_signing_hash` by one
  -- cross-`jal`.
  --
  -- ⚠️ There is NO input-domain gate on this row. `auth` ranges over every
  -- `Authorization`; `sp0`/`inPtr`/`outPtr`/`lenW` over every word. The
  -- condition is an UNPROVEN-CALLEE DEPENDENCY (`txSigningHashContract`),
  -- which per the 2026-08-11 coord rule is a dependency and not a gate — but
  -- since that residual carries essentially all of the routine's semantics, a
  -- `.proven` row would overclaim badly, so the tier is `.conditional` and the
  -- gate field names the callee rather than a domain restriction.
  --
  -- ⚠️ NOT tied to `SpecRef.Transactions.signing_hash_*`: the EIP-7702
  -- *authorization* digest is not one of those six (they are the TRANSACTION
  -- signing hashes). It lives inline in `SpecRef.Interpreter.recover_authority`
  -- keyed on `SET_CODE_TX_MAGIC`, and `recover_authority_unfold` (by `rfl`) is
  -- the tie.
  routine "eip7702_authorization_signing_hash" .conditional
      (some "eip7702_authorization_signing_hash_spec_within")
      (gate := "NOT an input-domain gate — an UNPROVEN-CALLEE DEPENDENCY. The "
        ++ "one condition is `h_tsh : txSigningHashContract`, the whole-routine "
        ++ "calling contract of K145 `tx_signing_hash` at the site "
        ++ "eip7702_authorization_signing_hash+20, which has no machine triple "
        ++ "today. It is stated GENERIC in (n_fields, type_prefix) — a "
        ++ "`∀ nW prefixW, nW.toNat ≤ fields.length` family — so the wrapper's "
        ++ "3 and 0x05 are DERIVED from the machine's two LIs, not assumed; the "
        ++ "`≤ fields.length` bound is load-bearing (beyond it the callee "
        ++ "returns status 1 and writes no hash, so an unbounded ∀ would be a "
        ++ "FALSE hypothesis). Every non-triple conjunct of the residual is "
        ++ "discharged at the real call site: coverRef "
        ++ "`authCallSite_ok_sample`, a closed term on the concrete "
        ++ "`sampleAuth` (chain id 1, delegate 0xDD*20, nonce 0) with its "
        ++ "27-byte tuple and a zeroed 32-byte output buffer. What is NOT "
        ++ "exhibited is exactly one `cpsTripleWithin` for tx_signing_hash. "
        ++ "The remaining hypotheses are ABI/framing obligations, not domain "
        ++ "restrictions: `halign` (even return address, witnessed by "
        ++ "`sample_ret_align`) and `hF` (caller-frame pcFree)")
      (notes := "whole-routine triple at GuestAddrs.eip7702_authorization_signing_hash "
        ++ "over eip7702AuthorizationSigningHash_prog (9 insn) via abiFrame_spec; "
        ++ "frame = [(x1,0)] at sp-16, step budget `authSteps fuel` = "
        ++ "1+1+(3+(1+fuel))+1+1+1. Structural drift guard "
        ++ "`eip7702AuthorizationSigningHash_prog_eq_frame` (rfl) pins the "
        ++ "emitted routine to abiFrameProg(-16,16,[(x1,0)],authBody); "
        ++ "`authJal_target` (decide) pins the cross-jal reloc to "
        ++ "GuestAddrs.tx_signing_hash. Post: a0=0, tuple region intact, output "
        ++ "region = `authSigningHash auth`, which `recover_authority_unfold` "
        ++ "(rfl) shows IS the digest SpecRef.recover_authority feeds to "
        ++ "Secp256k1.recover — a reduction, not a transcription. Field-position "
        ++ "pinning: `authSigningPreimage_segments` (general, short-list form) "
        ++ "and `sampleAuth_preimage` (concrete 25 bytes: MAGIC[0], list "
        ++ "header[1], chain_id[2], 0x94+address[3..23], nonce[24]) — not "
        ++ "symmetric in any two fields. Six-field wire layout confirmed against "
        ++ "SpecRef's PUBLIC decoder by `sampleAuth_decodes`. ⚠️ #12104's "
        ++ "keccakBodyDigest_eq_specref is NOT usable at this level: "
        ++ "tx_signing_hash hashes via zkvm_keccak256_segments (3-segment gather "
        ++ "entry point, no triple, no row), not zkvm_keccak256 — so the "
        ++ "residual's post is stated in pure SpecRef.keccak256 terms instead, "
        ++ "which is the form #12104 will close against once "
        ++ "tx_signing_hash_spec_within exists. Retirement: "
        ++ "`txSigningHashResidualNote`"),
  -- #11800, the node-DB half. Whole-routine triple over the emitted
  -- `nodeDbLookup_prog` (33 insn) at `GuestAddrs.node_db_lookup`; the machine
  -- appears in the statement (`ndlCr = CodeReq.ofProg ndlB nodeDbLookup_prog`),
  -- not just a model of it. Graded `.proven`, not `.conditional`: there is NO
  -- input-domain gate and NO unproven-callee dependency. `node_db_lookup` is a
  -- leaf -- it calls nothing, and in particular it does NOT hash: it compares
  -- the digest ALREADY STORED in each record against the caller's target, so
  -- the keccak obligation that `node_db_append` carries simply does not arise
  -- here. Every hypothesis is resource/ABI: `hsh.length = 32` (the a0 buffer
  -- the four-dword cascade reads), `(keccak256 m).length = 32` for the stored
  -- digests -- which is `Stateless.SpecRef.keccak256_length`, unconditionally
  -- true, so it excludes nothing -- u64-representability of node lengths and
  -- of the record count, and two-byte return-address alignment. The post is
  -- TOTAL: both the hit and the miss arm are inside the claim.
  routine "node_db_lookup" .proven (some "node_db_lookup_spec_within")
      (notes := "whole-routine `cpsTripleWithin` at `GuestAddrs.node_db_lookup`, "
        ++ "step bound `5 + 20 * |nodes| + 3` (prologue ;; per-record round ;; "
        ++ "exhaustion tail). Post is a `match` on `nodeDbFind`, the "
        ++ "address-carrying refinement of `MptAssertions.nodeDbLookupSpec`: a "
        ++ "hit pins `a0 = 0`, `*a1 = cursor + 40` (the record's NODE-BYTES "
        ++ "address) and `*a2 = |node|` -- two different cells holding two "
        ++ "different quantities, so the claim would not survive swapping them; "
        ++ "a miss pins `a0 = 1` and both cells UNCHANGED, not merely owned. "
        ++ "First-match-ness is real: the loop invariant carries "
        ++ "`nodeDbLookupSpec (take j) = none`. The four-`BNE` cascade is shown "
        ++ "to decide a 32-byte comparison exactly (`eq_of_dwords_eq`), and the "
        ++ "`andi -8` cursor bump to be exactly `nodeDbStride` "
        ++ "(`roundUp8_eq_alignToDword`). Composition to the spec reference is "
        ++ "`node_db_lookup_result_eq_build_node_db`, chaining the pre-existing "
        ++ "`nodeDbLookupSpec_eq_build_node_db` -- so the published length is "
        ++ "the length of the node `witness_state.py`'s `node_db` maps the hash "
        ++ "to. Non-vacuity is a COMPILED instantiation, "
        ++ "`node_db_lookup_sample_witness`: a closed one-record DB whose post "
        ++ "is reduced to the HIT arm. ⚠️ NOT established here: that "
        ++ "`node_db_append` establishes the `nodeDbIs` shape this triple "
        ++ "consumes (that is the append half, still open), and `bytesRegion`'s "
        ++ "dword-aligned-base convention is assumed of `mset_db_data`, not "
        ++ "derived from the link map"),
  -- #12036. `witness_lookup_by_hash` (155 insn) at
  -- `GuestAddrs.witness_lookup_by_hash`, over the emitted program itself
  -- (`wlhCr = CodeReq.ofProg wlhB witnessLookupByHash_prog`). Graded
  -- `.conditional` on an INPUT-DOMAIN gate, not on a callee: the routine's two
  -- cross-`jal`s (`witness_lookup_by_hash_indexed`, `zkvm_keccak256`) are both
  -- UNREACHED on the domain claimed, so this row carries no unproven-callee
  -- dependency -- but the general routine does, and the extension past either
  -- branch must carry those contracts as hypotheses.
  routine "witness_lookup_by_hash" .conditional
      (some "witness_lookup_by_hash_spec_within_empty_section")
      (gate := "`a1 = 0` (section_len) together with `widx_enabled = 0`. Both "
        ++ "arms of the dispatch this excludes are the WORK: the witness-index "
        ++ "binary search and the whole linear scan loop (`+308 … +552`) with "
        ++ "its `zkvm_keccak256` call are outside the claim. NOT a size cap -- "
        ++ "nothing in the module bounds `section_len` from above, which is the "
        ++ "hazard `MptWitnessLookup.lean`'s docstring records (a cap here once "
        ++ "turned valid `witness.codes` lookups into misses). Non-vacuity is a "
        ++ "COMPILED instantiation, `wlh_empty_section_sample_witness`; no "
        ++ "reachable-witness coverRef is claimed from the MPT-walk call sites")
      (notes := "whole-routine `cpsTripleWithin 52` from the linked entry to "
        ++ "the caller's return address. `wlh_abiFrame_byte_tie` pins the "
        ++ "routine to `abiFrameProg (-64) 64 wlhFrame wlhBody` by `decide`, so "
        ++ "the 8-slot save/restore, callee-saved preservation and the `sp` "
        ++ "round-trip are DERIVED via `abiFrame_spec_own`, not assumed. Post "
        ++ "pins `a0 = 1` (the documented `section_len = 0` miss), leaves the "
        ++ "caller's two out cells UNMENTIONED hence untouched, and fixes all "
        ++ "six `.data` cells the path touches: `wlh_lookup_calls` and "
        ++ "`wlh_linear_calls` bumped, `wlh_linear_last_section_len` "
        ++ "OVERWRITTEN with this call's length, `wlh_linear_max_section_len` "
        ++ "LEFT ALONE (the `bgeu` never lowers the high-water mark), "
        ++ "`wlh_linear_misses` bumped -- asymmetric, so swapping any two would "
        ++ "not typecheck. `wlhCounterBump_spec` proves the 5-instruction "
        ++ "telemetry idiom once at a free `(A, C)`; it recurs at eight sites. "
        ++ "⚠️ The named residual `MptWalkSpec.wlCallWithinShape` is NOT "
        ++ "retired, and this module shows kernel-checked WHY: "
        ++ "`wlh_entry_not_in_walk_fullCode` (`MptWalkSpec.fullCode wlhB = "
        ++ "none` -- the walk's `CodeReq` constrains no instruction at the "
        ++ "callee entry, so a triple that steps through the `jal` cannot hold) "
        ++ "and `wlh_cells_outside_residual_footprint` (the six telemetry cells "
        ++ "are absent from `wlCallEntry`/`wlCallReturn`, so a `pcFree` frame "
        ++ "may own them and the routine's `sd` falsifies the post). "
        ++ "`wlhCallWithin_empty_section` is the `callWithin_spec` discharge "
        ++ "with both repaired -- `cr ⊇ wlhCr` and the cells in the ambient -- "
        ++ "and `stackFree8_eq_frameSlotsOwn` identifies the eight dwords "
        ++ "`wlCallEntry` hands over with the routine's frame")
]

/-! ## Counts (kernel-checked) -/

/-- Rows in the guest-routine registry. -/
def routineCount : Nat := routineRegistry.length

/-- Rows at a given tier. -/
def routineCountTier (t : ProofTier) : Nat :=
  (routineRegistry.filter (fun e => e.tier == t)).length

theorem routineCount_eq : routineCount = 63 := by decide

theorem routineProvenCount_eq      : routineCountTier .proven      = 38 := by decide
theorem routineConditionalCount_eq : routineCountTier .conditional = 25 := by decide
theorem routinePartlyCount_eq      : routineCountTier .partly      = 0 := by decide

/-- Every row names a witness theorem. The `none` case is what
    `scripts/gen-axiom-witnesses.py`'s cross-check would report as an
    unwitnessed row; asserting it here makes the registry itself refuse one. -/
theorem routineRegistry_all_witnessed :
    routineRegistry.all (fun e => e.proofRef.isSome) = true := by decide

/-- Distinct guest symbols covered. Lower than `routineCount` because a
    per-form routine contributes several rows. -/
def routineSymbols : List String :=
  routineRegistry.map (·.symbol) |>.eraseDups

theorem routineSymbols_eq : routineSymbols.length = 44 := by decide

/-! ## Cross-registry consistency (#11294)

    This registry and `Correspondence.lean` describe overlapping facts in
    different vocabularies: a row here is a *witnessed theorem* about a symbol;
    a row there is a *verdict* about the same symbol. Nothing else compares
    them — `gen-axiom-witnesses.py`'s cross-check keys on theorem names, and an
    `.unproven` Correspondence row has `spec := none`, so it contributes no
    name at all and is invisible to that check by construction.

    The theorem below closes the gap in the direction that already bit once
    (#11281: `rlp_encode_uint_be` sat `.unproven` while `reub_spec_within`
    existed): a symbol witnessed here must not read `.unproven` there. Both
    registries would now have to be wrong in the same way for a stale verdict
    to survive. `scripts/check-registry-crosscheck.sh` enforces the same
    invariant source-level so it fails in `source-checks` in seconds rather
    than an hour into the build. -/

/-- `false` iff some entry of `reg` carries verdict `.unproven` for a routine
    in `witnessed`. Factored out of the theorem so the negative control below
    can run the same decision procedure on a synthetic violation. -/
def crossVerdictOk (witnessed : List String)
    (reg : List Correspondence.Entry) : Bool :=
  reg.all fun e =>
    e.verdict != .unproven || !(witnessed.contains e.routine)

/-- A routine with a witnessed row here must not be `.unproven` in
    `Correspondence.registry`. -/
theorem witnessed_not_unproven :
    crossVerdictOk routineSymbols Correspondence.registry = true := by decide

/-- Negative control, kernel-checked on every build: `rlp_encode_u64` is a real
    `.unproven` Correspondence row today, so witnessing it here would make the
    check fire. A gate nobody has seen fail is indistinguishable from one that
    cannot. (Was `rlp_item_span` until #11577 lifted that row.) -/
example :
    crossVerdictOk ("rlp_encode_u64" :: routineSymbols) Correspondence.registry
      = false := by decide

/-! ## Witness `abbrev`s

    Each row above names a theorem; the abbrev below forces its definition to
    exist, so a rename or deletion fails this file's elaboration. These are
    also what `scripts/gen-axiom-witnesses.py` greps to emit `#print axioms`
    lines, which is how these theorems reach `scripts/check-axioms.sh`.

    ⚠️ The generator's name pattern must admit these namespaces. Before #11042
    it was `@EvmAsm\.(?:Evm64|Stateless)…`, which silently matched **nothing**
    for `@EvmAsm.Codegen.…` — so an abbrev added here without widening the
    pattern would have left the gate green while covering nothing. The
    generator now also cross-checks every `proofRef` against the extracted
    names and fails loudly on a row it cannot witness.

    Convention: name the abbrev `_<lower>_routine_witness`; mark it
    `private noncomputable` to avoid polluting the namespace. -/

private noncomputable abbrev _reub_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeUintBeSAsm.reub_spec_within
private noncomputable abbrev _reub_encode_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeUintBeSAsm.reub_spec_encode_within
private noncomputable abbrev _reub_length_le_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeUintBeSAsm.reub_spec_within_of_length_le
private noncomputable abbrev _reb_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeBytesSAsm.reb_spec_within
private noncomputable abbrev _reb_rlpItem_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeBytesSAsm.reb_spec_rlpItem_within
-- #10780 item 3: the two long-form arms, their reference-tied corollaries, and the two
-- reachability witnesses their `.conditional` rows name as coverRefs (#12014's ruling).
-- The corollaries are witnessed separately from the triples on purpose: they are where
-- the `decode`/`readLength` hypotheses enter, and a reader should be able to see which
-- claim is the machine result and which is the model identification.
-- #10780: the TOTAL dispatch — one triple over all five RLP prefix forms, no `SpanForm`
-- gate. Witnessed but deliberately NOT re-graded: `rlp_item_size` keeps its
-- `.conditional` row on `rlp_item_size_spec_within`, because the total statement carries a
-- prefix-dependent step bound and a seven-register footprint where the existing one is
-- constant-time over two, and which of those a consumer wants is a per-caller decision.
-- Additive by construction: nothing consuming `SpanForm` changes.
private noncomputable abbrev _rlp_item_size_total_witness :=
  @EvmAsm.Codegen.RlpItemSizeTotalSpec.rlp_item_size_total_spec_within
private noncomputable abbrev _rlp_item_size_total_covers_witness :=
  @EvmAsm.Codegen.RlpItemSizeTotalSpec.risStepsTotal_covers
private noncomputable abbrev _rlp_item_size_total_bound_witness :=
  @EvmAsm.Codegen.RlpItemSizeTotalSpec.risStepsTotal_le
private noncomputable abbrev _rlp_item_size_long_string_witness :=
  @EvmAsm.Codegen.RlpItemSizeLongSpec.rlp_item_size_long_string_pinned_spec_within
private noncomputable abbrev _rlp_item_size_long_list_witness :=
  @EvmAsm.Codegen.RlpItemSizeLongSpec.rlp_item_size_long_list_pinned_spec_within
private noncomputable abbrev _rlp_item_size_long_string_encode_witness :=
  @EvmAsm.Codegen.RlpItemSizeLongSpec.rlp_item_size_long_string_encode_length_spec_within
private noncomputable abbrev _rlp_item_size_long_list_encode_witness :=
  @EvmAsm.Codegen.RlpItemSizeLongSpec.rlp_item_size_long_list_encode_length_spec_within
private noncomputable abbrev _rlp_item_size_long_string_cover_witness :=
  @EvmAsm.Codegen.RlpItemSizeLongSpec.longStringSample_reachable
private noncomputable abbrev _rlp_item_size_long_list_cover_witness :=
  @EvmAsm.Codegen.RlpItemSizeLongSpec.longListSample_reachable
private noncomputable abbrev _rlp_item_size_routine_witness :=
  @EvmAsm.Codegen.RlpSpliceHelperSpec.rlp_item_size_spec_within
private noncomputable abbrev _rlp_item_span_routine_witness :=
  @EvmAsm.Codegen.RlpItemSpanSpec.rlp_item_span_spec_within
-- #12033: the strict-wrapper machine tie and its compiled satisfying instance.
private noncomputable abbrev _rlp_walk_next_shared_strict_routine_witness :=
  @EvmAsm.Codegen.RlpWalkNextStrictTie.rlp_walk_next_shared_nonlist_strict_spec_within
private noncomputable abbrev _rlp_walk_next_shared_strict_instance_witness :=
  @EvmAsm.Codegen.RlpWalkNextStrictTie.rlp_walk_next_shared_nonlist_strict_instance
private noncomputable abbrev _rlp_walk_next_shared_strict_bridge_witness :=
  @EvmAsm.Codegen.RlpWalkNextStrictTie.strictW_of_rlpItemDecode_nonlist
-- #10780 item 1, at every width. `long2_first_length_byte_ne_zero` is the `lenlen = 2`
-- instance and is stated over the literal shift `len >>> 8`, so it says nothing at any
-- other width; this is the property itself, over `u64ByteLen`. Witnessed because the
-- `lenlen >= 3` arm will consume it as a specification, and a specification outside the
-- axiom gate is the #11637 failure mode -- the same reason the `LongSpan` lemmas are
-- gated. No registry row changes: this is a side condition, not a routine triple.
-- #11517 (template pair): the account-leaf sentinels. Both `EMPTY_CODE_HASH` and
-- `EMPTY_TRIE_ROOT` now have kernel-checked SpecRef ties through split Keccak proofs.
-- The literal pins remain gated so CI also rechecks their byte values.
-- #10780: the length-byte loop of `rlp_encode_list_prefix` at a SYMBOLIC trip count,
-- which is what the `lenlen >= 3` arms were missing. Ported from `rebLolLoop` (same five
-- instructions, registers renamed), so the ~200-lines-per-byte unrolling cost the long2
-- header warns about does not have to be paid. Witnessed rather than left for the arm
-- that consumes it: this is a machine result about the emitted program, and it is the
-- piece a later composition will trust without re-checking. No registry row changes --
-- a block lemma, not a routine triple.
-- #10780: `rlp_item_size`'s long-form length-byte ACCUMULATION loop (idx25-31) at a
-- symbolic trip count -- the read/accumulate counterpart of `lpLolLoop`'s write/extract.
-- Ported from `wi_len_loop` (`rlp_walk_init` idx17-23): the same seven instructions with
-- counter x30/x30, accumulator x31/x28, scratch x28/x31, cursor x6/x29. This is the
-- machine half the `SpanForm` long arms need; the model half is already gated as the
-- `LongSpan` lemmas. ⚠️ The drift guard is witnessed WITH it on purpose: the loop is
-- proved core-side over a second copy of `rlpItemSize_prog` (core may not import Codegen),
-- so the guard is the only thing keeping the copy and the emitted program in step.
private noncomputable abbrev _rlp_item_size_len_loop_witness :=
  @EvmAsm.Rv64.RLP.risLenLoop
private noncomputable abbrev _rlp_item_size_len_loop_body_witness :=
  @EvmAsm.Rv64.RLP.risLenLoopBody
private noncomputable abbrev _rlp_item_size_prog_drift_guard_witness :=
  @EvmAsm.Codegen.rlpItemSize_prog_eq_verified_prog
private noncomputable abbrev _rlp_prefix_lol_loop_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLoopSpec.lpLolLoop
private noncomputable abbrev _rlp_prefix_lol_body_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLoopSpec.lpLolBody
private noncomputable abbrev _rlp_prefix_loop_writes_toBytesBE_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLoopSpec.lpLoop_writes_toBytesBE
-- #10817: `bal_canonical_sort`'s canonical nibble extractor (flat indices 67-94,
-- `base+268 -> base+380`), proved to agree with a key decoded from the FIELD
-- SEMANTICS rather than from the sorter's own segment descriptor. That direction is
-- the whole point: a descriptor-derived key would let a limb swap satisfy both
-- sortedness and permutation-preservation, which is exactly why
-- `BalCanonicalSort.lean:41-44` refuses to substitute either property. Witnessed
-- rather than left to the sortedness theorem that will consume it -- the same
-- discipline as `lpLolLoop`, and for the same reason: a specification outside the
-- axiom gate is the #11637 failure mode. The model side is witnessed WITH the
-- machine side, because a key definition that drifted from the reversal it encodes
-- would silently re-open the vacuity. No registry row changes: a block lemma over
-- a pc range, not a routine triple, and no `JALR`.
private noncomputable abbrev _bal_digit_agree_1seg_witness :=
  @EvmAsm.Codegen.BalCanonicalSortDigitSpec.balDigitAgree_1seg
private noncomputable abbrev _bal_digit_agree_2seg_witness :=
  @EvmAsm.Codegen.BalCanonicalSortDigitSpec.balDigitAgree_2seg
private noncomputable abbrev _bal_digit_agree_2seg_live_witness :=
  @EvmAsm.Codegen.BalCanonicalSortDigitSpec.balDigitAgree_2seg_live
private noncomputable abbrev _bal_digit_at_67_witness :=
  @EvmAsm.Codegen.BalCanonicalSortDigitSpec.balDigit_at_67
private noncomputable abbrev _bal_key_getD_head_witness :=
  @EvmAsm.Codegen.BalCanonicalSortDigitSpec.balCanonicalKey_getD_head
private noncomputable abbrev _bal_key_getD_tail_witness :=
  @EvmAsm.Codegen.BalCanonicalSortDigitSpec.balCanonicalKey_getD_tail
-- #11517 (template pair): the account-leaf sentinels, pinned. `EMPTY_TRIE_ROOT` /
-- `EMPTY_CODE_HASH` existed in three unconnected copies -- SpecRef's computed pair and two
-- baked asm literals -- so a typo in one typechecked everywhere and produced a wrong state
-- root. These are the ties. Gated deliberately: the value of a drift pin is that CI
-- rechecks it, and a pin outside the gate is a comment.
-- #11517 (template pair): the account-leaf sentinels. `EMPTY_CODE_HASH` now has a
-- kernel-checked SpecRef tie through the split Keccak proof; the trie-root copy remains a
-- numeral drift pin because its distinct `keccak256 [0x80]` KAT would need a separately
-- justified intrinsic-depth theorem. The pins stay gated so CI rechecks the remaining
-- literal correspondence.
-- #11517: the `Stateless/Constants.lean` hex-`String` copies, pinned to the byte-list
-- copies #12032 pinned. The `eq_adBytes`/`eq_aieBytes` ties are the strongest of the set:
-- two independent asm-side definitions in two different representations, equal outright,
-- with no keccak and no written numeral in between.
private noncomputable abbrev _keccak256EmptyHashHex_eq_adBytes_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.keccak256EmptyHashHex_eq_adBytes
private noncomputable abbrev _keccak256EmptyHashHex_eq_aieBytes_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.keccak256EmptyHashHex_eq_aieBytes
private noncomputable abbrev _emptyTrieRootHex_eq_adBytes_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.emptyTrieRootHex_eq_adBytes
private noncomputable abbrev _trieRoot_ne_codeHash_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.trieRoot_ne_codeHash
-- ✅ #12081 REPAIRED: `emptyOmmerHashHex` now holds the empty ommer hash (keccak of
-- rlp([]) = keccak(0xc0)); it previously aliased the empty trie root. The divergence
-- was pinned as `divergence_emptyOmmerHashHex` by #12082 and retired by #12081; the
-- registry keeps a row pointing at the fix pin so the record does not vanish.
private noncomputable abbrev _fix_emptyOmmerHashHex_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.fix_emptyOmmerHashHex
-- #11517: SpecRef-derived vs asm-flattened numbers -- the sharpest drift shape, since a
-- repricing moves the SpecRef side silently while the asm literal stays put.
private noncomputable abbrev _bvEip7702AuthRegularGas_eq_spec_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.bvEip7702AuthRegularGas_eq_spec
private noncomputable abbrev _maxInitcodeSize_eq_spec_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.maxInitcodeSize_eq_spec
private noncomputable abbrev _maxDeployedCodeSize_eq_spec_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.maxDeployedCodeSize_eq_spec
private noncomputable abbrev _ad_empty_trie_root_value_witness :=
  @EvmAsm.Codegen.AccountDecodeCorrespondence.adEmptyTrieRootBytes_value
private noncomputable abbrev _ad_empty_code_hash_value_witness :=
  @EvmAsm.Codegen.AccountDecodeCorrespondence.adEmptyCodeHashBytes_value
private noncomputable abbrev _ad_empty_code_hash_spec_witness :=
  @EvmAsm.Codegen.AccountDecodeCorrespondence.adEmptyCodeHashBytes_eq_spec
private noncomputable abbrev _ad_empty_trie_root_spec_witness :=
  @EvmAsm.Codegen.AccountDecodeCorrespondence.adEmptyTrieRootBytes_eq_spec
private noncomputable abbrev _aie_empty_code_hash_value_witness :=
  @EvmAsm.Codegen.AccountDecodeCorrespondence.aieEmptyCodeHashBytes_value
private noncomputable abbrev _ad_empty_code_hash_eq_aie_witness :=
  @EvmAsm.Codegen.AccountDecodeCorrespondence.adEmptyCodeHashBytes_eq_aie
private noncomputable abbrev _rlp_prefix_first_length_byte_ne_zero_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixCanonical.first_length_byte_ne_zero
private noncomputable abbrev _rlp_prefix_pow_le_u64ByteLen_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixCanonical.pow_le_u64ByteLen
-- #11795: the REFUTATION of `RlpWalkNextStrict`, plus the accept-indexed bridge that
-- replaces it. Neither changes a registry row -- witnessed because a negative control is
-- only worth what its axioms are, and this one is load-bearing for the issue's
-- sequencing: it is what says the residual is FALSE rather than open, so nobody schedules
-- a proof against it. The replacement is witnessed alongside so the correction and its
-- repair cannot drift apart.
private noncomputable abbrev _not_rlpWalkNextStrict_witness :=
  @EvmAsm.Codegen.RlpListCountItemsBridge.not_rlpWalkNextStrict_nestedNonCanonical
private noncomputable abbrev _rlpItemDecodeBridgesOn_of_accepts_witness :=
  @EvmAsm.Codegen.RlpListCountItemsBridge.rlpItemDecodeBridgesOn_of_accepts
private noncomputable abbrev _rlpItemDecodeStrictW_of_decodeAux_witness :=
  @EvmAsm.Rv64.RLP.rlpItemDecodeStrictW_of_decodeAux
private noncomputable abbrev _account_rlp_walk_init_routine_witness :=
  @EvmAsm.Evm64.account_rlp_walk_init_spec_within
private noncomputable abbrev _rlp_walk_init_long1_routine_witness :=
  @EvmAsm.Evm64.rlp_walk_init_long1_spec_within
private noncomputable abbrev _account_rlp_walk_next_field0_routine_witness :=
  @EvmAsm.Evm64.account_rlp_walk_next_field0_spec_within
private noncomputable abbrev _account_rlp_walk_next_field1_routine_witness :=
  @EvmAsm.Evm64.account_rlp_walk_next_field1_spec_within
private noncomputable abbrev _rlp_walk_next_scalar_routine_witness :=
  @EvmAsm.Evm64.rlp_walk_next_scalar_spec_within
private noncomputable abbrev _account_rlp_content_to_u64_nonce_routine_witness :=
  @EvmAsm.Evm64.account_rlp_content_to_u64_nonce_spec_within
private noncomputable abbrev _account_extract_nonce_routine_witness :=
  @EvmAsm.Codegen.account_extract_nonce_spec_within
private noncomputable abbrev _account_rlp_content_to_u256_be_balance_routine_witness :=
  @EvmAsm.Evm64.account_rlp_content_to_u256_be_balance_spec_within
-- #11289: the 7 specs `Correspondence.lean` named but nothing witnessed.
private noncomputable abbrev _rlp_bytes_encoded_size_routine_witness :=
  @EvmAsm.Codegen.RlpBytesEncodedSizeSAsm.rlpBytesEncodedSize_spec
-- #11341: the model-facing counterpart, named by the `.bridged` Correspondence row.
private noncomputable abbrev _rlp_bytes_encoded_size_encode_routine_witness :=
  @EvmAsm.Codegen.RlpBytesEncodedSizeSAsm.rlpBytesEncodedSize_encode_spec
private noncomputable abbrev _rlp_field_to_u256_be_routine_witness :=
  @EvmAsm.Codegen.RlpFieldToU256BeSAsm.rlpFieldToU256Be_spec_within
private noncomputable abbrev _rlp_field_to_u64_routine_witness :=
  @EvmAsm.Codegen.RlpFieldToU64SAsm.rlpFieldToU64_spec_within
private noncomputable abbrev _header_validate_extra_data_length_routine_witness :=
  @EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.header_validate_extra_data_length_spec_within
-- #11575 row 2's Correspondence row names this; Codegen-side, so it lives here.
private noncomputable abbrev _header_extra_data_length_of_decode_witness :=
  @EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.header_extra_data_length_of_decode
private noncomputable abbrev _header_extract_logs_bloom_routine_witness :=
  @EvmAsm.Codegen.HeaderExtractLogsBloomSpec.headerExtractLogsBloom_spec_within
-- Correspondence row (#11575) names this; Codegen-side, so the witness lives here
-- for the same reason as #11351's below.
private noncomputable abbrev _header_logs_bloom_of_decode_witness :=
  @EvmAsm.Codegen.HeaderExtractLogsBloomSpec.header_logs_bloom_of_decode
private noncomputable abbrev _header_extract_number_routine_witness :=
  @EvmAsm.Codegen.HeaderExtractNumberSpec.header_extract_number_spec_within
-- #11575 tier A. Namespace note: both theorems live in the `…Spec` NAMESPACE
-- (`ChainValidateConsecutiveNumbersSpec`) but in the `…LoopClose` MODULE — the
-- loop-close files reopen the spec namespace rather than declaring their own.
-- #11576: the seventh header-family routine — the one `docs/leaf-routine-targets.md`
-- singles out as NOT a mechanical fork, because it had only the string↔Program
-- byte-identity theorem and no triple at all. Domain-restricted to the empty header list
-- (`hN : encoded = []`), with the restriction IN the statement; the `N ≥ 1` loop is the
-- named remaining half. No registry row yet: a row would advertise coverage of a routine
-- whose loop is unproven, and the six exit-path lemmas are the honest unit until then.
-- `nonce_rule_agrees` is witnessed because it settles the canonical-scalar leniency
-- question — on an 8-byte field the guest's `u64 = 0` test IS the port's all-zero test.
private noncomputable abbrev _cvpmf_empty_routine_witness :=
  @EvmAsm.Codegen.ChainValidatePostMergeFullSpec.chain_validate_post_merge_full_spec_within_empty
private noncomputable abbrev _cvpmf_nonce_rule_agrees_witness :=
  @EvmAsm.Codegen.ChainValidatePostMergeFullSpec.nonce_rule_agrees
private noncomputable abbrev _cvpmf_empty_ommer_hash_value_witness :=
  @EvmAsm.Codegen.ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_value
private noncomputable abbrev _chain_validate_consecutive_numbers_routine_witness :=
  @EvmAsm.Codegen.ChainValidateConsecutiveNumbersSpec.chain_validate_consecutive_numbers_spec_within
private noncomputable abbrev _chain_validate_increasing_timestamps_routine_witness :=
  @EvmAsm.Codegen.ChainValidateIncreasingTimestampsSpec.chain_validate_increasing_timestamps_spec_within
private noncomputable abbrev _chain_validate_gas_used_under_limit_routine_witness :=
  @EvmAsm.Codegen.ChainValidateGasUsedUnderLimitSpec.chain_validate_gas_used_under_limit_spec_within
private noncomputable abbrev _chain_validate_blob_gas_used_multiple_routine_witness :=
  @EvmAsm.Codegen.ChainValidateBlobGasMultipleSpec.chain_validate_blob_gas_used_multiple_spec_within
private noncomputable abbrev _chain_validate_blob_gas_used_under_max_routine_witness :=
  @EvmAsm.Codegen.ChainValidateBlobGasUnderMaxSpec.chain_validate_blob_gas_used_under_max_spec_within
private noncomputable abbrev _chain_validate_extra_data_length_routine_witness :=
  @EvmAsm.Codegen.ChainValidateExtraDataLengthSpec.chain_validate_extra_data_length_spec_within
-- #11925 continuation: whole-routine triples surfaced by scripts/proof-frontier.py.
-- Namespace/molecule note (mirrors the twins): account_extract_balance_spec_within
-- lives in the bare `EvmAsm.Codegen` NAMESPACE inside AccountAccessorTopSpec.lean;
-- account_decode_spec_within is in `EvmAsm.Codegen.AccountDecodeSpec` inside
-- AccountDecodeClose6.lean; the other two follow the `…Spec` namespace convention.
private noncomputable abbrev _account_decode_routine_witness :=
  @EvmAsm.Codegen.AccountDecodeSpec.account_decode_spec_within
private noncomputable abbrev _account_extract_balance_routine_witness :=
  @EvmAsm.Codegen.account_extract_balance_spec_within
private noncomputable abbrev _account_is_eip161_empty_routine_witness :=
  @EvmAsm.Codegen.AccountIsEip161EmptySpec.account_is_eip161_empty_spec_within
private noncomputable abbrev _receipt_extract_logs_bloom_routine_witness :=
  @EvmAsm.Codegen.ReceiptExtractLogsBloomSpec.receiptExtractLogsBloom_spec_within
-- Correspondence row #11351 names this; it is Codegen-side, and Correspondence
-- deliberately does not import Codegen, so the witness abbrev lives here.
private noncomputable abbrev _header_number_of_decode_witness :=
  @EvmAsm.Codegen.HeaderExtractNumberSpec.header_number_of_decode
-- #11345: the model-facing consumer joining `account_decode`'s output struct to
-- `AccountRecord` and thence to `SpecRef.decode_account_from_leaf`. Codegen-side,
-- so like the #11351 witness above it lives here rather than in Correspondence.
-- #11516: named by the `account_decode` Correspondence row. Codegen-side, so the
-- witness lives here (same reason as the #11351/#11345/#11348 witnesses above).
-- Row without witness = theorem invisible to the axiom gate; that is a separate
-- obligation from claiming a tier, and #11348 is where I learned it the hard way.
private noncomputable abbrev _account_decode_spec_within_witness :=
  @EvmAsm.Codegen.AccountDecodeSpec.account_decode_spec_within
private noncomputable abbrev _account_decode_matches_specRef_witness :=
  @EvmAsm.Codegen.AccountDecodeCompose.decoded_matches_specRef
private noncomputable abbrev _account_decode_output_witness :=
  @EvmAsm.Codegen.AccountDecodeCompose.outputSuccess_eq_accountDecodedIs
-- #11346 item 2: the leniency agreement now consumes the shared `beAccum`
-- model directly; no duplicate-definition identity witness is needed.
private noncomputable abbrev _account_eip161_leniency_witness :=
  @EvmAsm.Codegen.AccountIsEip161EmptySpec.leniency_agrees
-- #11348: Correspondence's `bloom_or_into` row names this, and it is Codegen-side,
-- so like the #11351/#11345 witnesses above the abbrev lives here.
--
-- ⚠️ NO `RoutineEntry` row accompanies it, deliberately. Every row in the registry
-- above claims a FLAT whole-routine triple at `GuestAddrs.<symbol>`, derived by
-- `Fn.retSpecFlat`; `bloomOrIntoFn_spec` is the structured SAsm `.Spec`, so a
-- `.proven` row would overclaim. The WITNESS is what puts a theorem in the axiom
-- gate; the ROW is what claims a tier. Those are separate obligations and only the
-- first is warranted here. (This distinction is the subject of #11637.)
private noncomputable abbrev _bloom_or_into_witness :=
  @EvmAsm.Codegen.BloomOrIntoSAsm.bloomOrIntoFn_spec
-- The reference-facing half: why per-receipt accumulation matches a `logs_bloom`
-- computed from the flat log list.
private noncomputable abbrev _bloom_or_into_fold_witness :=
  @EvmAsm.Codegen.BloomOrIntoSAsm.bloomOrInto_fold_eq_logs_bloom
private noncomputable abbrev _rlp_list_encoded_size_routine_witness :=
  @EvmAsm.Codegen.RlpListEncodedSizeSAsm.rlpListEncodedSize_spec
-- #11341: the model-facing counterpart, named by the `.bridged` Correspondence row.
private noncomputable abbrev _rlp_list_encoded_size_encode_routine_witness :=
  @EvmAsm.Codegen.RlpListEncodedSizeSAsm.rlpListEncodedSize_encode_spec
private noncomputable abbrev _rlp_list_nth_item_routine_witness :=
  @EvmAsm.Codegen.RlpListNthItemSAsm.rlpListNthItem_spec_within
private noncomputable abbrev _rlp_list_count_items_routine_witness :=
  @EvmAsm.Codegen.RlpListCountItemsSAsm.rlp_list_count_items_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_short_routine_witness :=
  @EvmAsm.Codegen.RlpSpliceHelperSpec.rlp_encode_list_prefix_short_pinned_spec_within
-- #10780: the long1 arm, proven since the short arm landed but never registered.
private noncomputable abbrev _rlp_encode_list_prefix_long1_routine_witness :=
  @EvmAsm.Codegen.RlpSpliceHelperSpec.rlp_encode_list_prefix_long1_pinned_spec_within
-- #10780 item 3: the long2 arm, plus its canonical-form lemma (the no-leading-zero
-- property in the length-of-length, which is what makes the header valid RLP).
private noncomputable abbrev _rlp_encode_list_prefix_long2_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong2Spec.rlp_encode_list_prefix_long2_pinned_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_long2_canonical_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong2Spec.long2_first_length_byte_ne_zero
private noncomputable abbrev _rlp_encode_list_prefix_long3_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong3Spec.rlp_encode_list_prefix_long3_pinned_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_long3_canonical_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong3Spec.long3_first_length_byte_ne_zero
private noncomputable abbrev _rlp_encode_list_prefix_long4_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong4Spec.rlp_encode_list_prefix_long4_pinned_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_long4_canonical_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong4Spec.long4_first_length_byte_ne_zero
-- #10780 item 3, widths 5/6/7. Each triple is witnessed alongside its canonicality
-- instance for the same reason long3/long4 are: the instance is what makes the emitted
-- header canonical RLP rather than merely parseable, and a specification outside the
-- axiom gate is the #11637 failure mode.
private noncomputable abbrev _rlp_encode_list_prefix_long5_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong5Spec.rlp_encode_list_prefix_long5_pinned_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_long5_canonical_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong5Spec.long5_first_length_byte_ne_zero
private noncomputable abbrev _rlp_encode_list_prefix_long6_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong6Spec.rlp_encode_list_prefix_long6_pinned_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_long6_canonical_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong6Spec.long6_first_length_byte_ne_zero
private noncomputable abbrev _rlp_encode_list_prefix_long7_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong7Spec.rlp_encode_list_prefix_long7_pinned_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_long7_canonical_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong7Spec.long7_first_length_byte_ne_zero
-- #11291: the whole-routine withdrawal decoder (existed since #10782).
private noncomputable abbrev _bgv_u32le_routine_witness :=
  @EvmAsm.Codegen.ExecutionRequestsHashBgvOffset.bgv_u32le_offset_spec_within
private noncomputable abbrev _check_gas_limit_routine_witness :=
  @EvmAsm.Codegen.CheckGasLimitSAsm.checkGasLimit_ref_spec
private noncomputable abbrev _bytes_to_nibbles_routine_witness :=
  @EvmAsm.Codegen.BytesToNibblesSAsm.bytesToNibblesFlat_spec
-- #11799 dep: whole-routine mpt_node_kind machine triple.
private noncomputable abbrev _mpt_node_kind_routine_witness :=
  @EvmAsm.Codegen.MptNodeKindSpec.mpt_node_kind_spec_within
-- #12027: Result → kindTag wiring under WF (success arms + constructive existence).
private noncomputable abbrev _mpt_node_kind_result_eq_kindTag_witness :=
  @EvmAsm.Codegen.MptNodeKindWire.mptNodeKindResult_eq_kindTag
private noncomputable abbrev _mpt_node_kind_result_exists_kindTag_witness :=
  @EvmAsm.Codegen.MptNodeKindWire.mptNodeKindResult_exists_kindTag

-- #11799 residual audit: hp_decode_nibbles machine already existed; register it.
private noncomputable abbrev _hp_decode_nibbles_routine_witness :=
  @EvmAsm.Codegen.HpDecodeNibblesSAsm.hp_decode_nibbles_spec_ported
private noncomputable abbrev _withdrawal_decode_routine_witness :=
  @EvmAsm.Codegen.WithdrawalDecodeSpec.withdrawal_decode_spec_within
-- #11574: the two field-bound scans. The MACHINE triples were unwitnessed by
-- `check-axioms.sh` until now despite predating this registration by months —
-- exactly the "witnessed symbol with no row" / "row with no witness" pair of
-- omissions #11342 and #11348 each caught once.
private noncomputable abbrev _blsg_lt_p_routine_witness :=
  @EvmAsm.Codegen.Bls12G1LtPSAsm.blsgLtP_spec
private noncomputable abbrev _blsg_lt_p_specref_routine_witness :=
  @EvmAsm.Codegen.blsgLtP_spec_specref
private noncomputable abbrev _bnf_lt_p_routine_witness :=
  @EvmAsm.Codegen.Bn254FieldLtPSAsm.bnfLtP_spec
private noncomputable abbrev _bnf_lt_p_specref_routine_witness :=
  @EvmAsm.Codegen.bnfLtP_spec_specref
-- #11925 last-of-six: the whole-routine triple lives in the `TxTypeDispatchTop`
-- module, in the `…TxTypeDispatchSpec` namespace.
private noncomputable abbrev _tx_type_dispatch_routine_witness :=
  @EvmAsm.Codegen.TxTypeDispatchSpec.txTypeDispatch_spec_within
-- #11800 follow-on: zkvm_keccak256 whole-routine wrapper over #11960 framing.
private noncomputable abbrev _zkvm_keccak256_routine_witness :=
  @EvmAsm.Codegen.Proofs.zkvm_keccak256_spec_within
-- #12037: pure operational digest → SpecRef.keccak256 (load-bearing for #12038).
private noncomputable abbrev _keccakBodyDigest_eq_specref_witness :=
  @EvmAsm.Codegen.Proofs.keccakBodyDigest_eq_specref
private noncomputable abbrev _keccakBodyDigest_div_eq_specref_witness :=
  @EvmAsm.Codegen.Proofs.keccakBodyDigest_div_eq_specref
-- #12018 phase 1: SHA-256 frame and setup boundaries are independently
-- witnessed while the full-block loop and top-level wrapper remain open.
private noncomputable abbrev _zkvm_sha256_frame_witness :=
  @EvmAsm.Codegen.Proofs.sha256Frame_spec
private noncomputable abbrev _zkvm_sha256_setup_witness :=
  @EvmAsm.Codegen.Proofs.sha256SetupMoves_spec
-- #12018 phase 2: full-block copy, parameter materialization, and the
-- external SHA compression seam are composed; the outer loop and wrapper stay
-- open.
private noncomputable abbrev _zkvm_sha256_full_block_prefix_witness :=
  @EvmAsm.Codegen.Proofs.sha256FullBlockPrefix_spec
-- #12018 phase 3: the emitted LI/BLT/JAL countdown shell is proved with an
-- explicit 22-step body contract; padding and the top-level wrapper remain
-- open.
private noncomputable abbrev _zkvm_sha256_full_block_loop_witness :=
  @EvmAsm.Codegen.Proofs.sha256FullBlockLoop_reload_spec
-- #11578 rescope: execution_requests_hash validation-accept prefix.
private noncomputable abbrev _execution_requests_hash_routine_witness :=
  @EvmAsm.Codegen.ExecutionRequestsHashWrap.execution_requests_hash_validation_accept
-- #12011 hash-half: erh_hash_one empty+nonempty tops under residual h_sha.
-- No Routines ROW yet (whole erh/rhv still open); witnesses still required so
-- check-axioms covers these modules (same pattern as #12018 phase witnesses).
private noncomputable abbrev _erh_hash_one_empty_witness :=
  @EvmAsm.Codegen.ExecutionRequestsHashHashOneTop.erh_hash_one_spec_within_empty
private noncomputable abbrev _erh_hash_one_nonempty_witness :=
  @EvmAsm.Codegen.ExecutionRequestsHashHashOneNonemptyTop.erh_hash_one_spec_within_nonempty
-- #12038: K147 EIP-7702 authorization signing hash, whole routine, under the
-- named unproven-callee residual for K145 `tx_signing_hash`.
private noncomputable abbrev _eip7702_authorization_signing_hash_routine_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.eip7702_authorization_signing_hash_spec_within
-- The SpecRef tie (by `rfl`): the digest IS `recover_authority`'s `signing_hash`.
private noncomputable abbrev _eip7702_auth_signing_hash_specref_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.recover_authority_unfold
-- Structural drift guard on the emitted routine + its cross-`jal` reloc.
private noncomputable abbrev _eip7702_auth_signing_hash_frame_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.eip7702AuthorizationSigningHash_prog_eq_frame
private noncomputable abbrev _eip7702_auth_signing_hash_jal_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.authJal_target
-- coverRef: the residual's computable half, discharged at the real call site.
private noncomputable abbrev _eip7702_auth_signing_hash_cover_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.authCallSite_ok_sample
-- Field-position pinning (general short-list form + the concrete 25 bytes).
private noncomputable abbrev _eip7702_auth_signing_hash_segments_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.authSigningPreimage_segments
private noncomputable abbrev _eip7702_auth_signing_hash_preimage_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.sampleAuth_preimage
private noncomputable abbrev _eip7702_auth_signing_hash_decodes_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.sampleAuth_decodes
-- #11800 node-DB half: whole-routine `node_db_lookup` triple, its compiled
-- non-vacuity instance, and the composition to `SpecRef.build_node_db`.
private noncomputable abbrev _node_db_lookup_routine_witness :=
  @EvmAsm.Codegen.NodeDbLookupSpec.node_db_lookup_spec_within
private noncomputable abbrev _node_db_lookup_sample_witness :=
  @EvmAsm.Codegen.NodeDbLookupSpec.node_db_lookup_sample_witness
private noncomputable abbrev _node_db_lookup_specref_witness :=
  @EvmAsm.Codegen.NodeDbLookupSpec.node_db_lookup_result_eq_build_node_db
-- #12036: the `witness_lookup_by_hash` whole-routine triple on the
-- `section_len = 0` domain, its compiled instance, the callWithin discharge,
-- and the two kernel-checked reasons `wlCallWithinShape` is still open.
private noncomputable abbrev _witness_lookup_by_hash_routine_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.witness_lookup_by_hash_spec_within_empty_section
private noncomputable abbrev _witness_lookup_by_hash_sample_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.wlh_empty_section_sample_witness
private noncomputable abbrev _witness_lookup_by_hash_frame_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.wlh_abiFrame_byte_tie
private noncomputable abbrev _witness_lookup_by_hash_callwithin_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.wlhCallWithin_empty_section
private noncomputable abbrev _witness_lookup_by_hash_gap_code_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.wlh_entry_not_in_walk_fullCode
private noncomputable abbrev _witness_lookup_by_hash_gap_cells_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.wlh_cells_outside_residual_footprint

end EvmAsm.Progress
