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
import EvmAsm.Codegen.Programs.BloomOrIntoBridge
import EvmAsm.Evm64.AccountAccessorSpec
import EvmAsm.Codegen.Programs.RlpEncodeUintBeComposeSAsm
import EvmAsm.Codegen.Programs.RlpEncodeBytesComposeSAsm
import EvmAsm.Codegen.Programs.RlpSpliceHelperSpec
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
import EvmAsm.Codegen.Programs.BgvU32leSpec
import EvmAsm.Codegen.Programs.CheckGasLimitBridge
import EvmAsm.Codegen.Programs.BytesToNibblesBridge
import EvmAsm.Codegen.Programs.WithdrawalDecodeClose5
import EvmAsm.Codegen.Programs.CryptoFieldLtPBridge
-- #11575 tier A: the whole-routine triples live in the `LoopClose` modules (the
-- `Spec` modules hold only the prologue/epilogue/return-path blocks), so it is
-- those that have to be imported for the witness abbrevs to force.
import EvmAsm.Codegen.Programs.ChainValidateConsecutiveNumbersLoopClose
import EvmAsm.Codegen.Programs.ChainValidateIncreasingTimestampsLoopClose
import EvmAsm.Codegen.Programs.ChainValidateGasUsedUnderLimitLoopClose
import EvmAsm.Codegen.Programs.ChainValidateBlobGasMultipleLoopClose
import EvmAsm.Codegen.Programs.ChainValidateBlobGasUnderMaxLoopClose
import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthLoopClose

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
  routine "rlp_content_to_u64" .conditional
      (some "account_rlp_content_to_u64_nonce_spec_within")
      (gate := "`a.nonce < 2 ^ 64` — the accessor's u64 output width, narrower "
        ++ "than `Account.nonce`'s own `< 2 ^ 256` invariant")
      (notes := "step bound `7 * (Nat.toBytesBE a.nonce).length + 11`"),
  routine "rlp_content_to_u256_be" .proven
      (some "account_rlp_content_to_u256_be_balance_spec_within")
      (notes := "writes the 32-byte balance; step bound "
        ++ "`7 * (Nat.toBytesBE a.balance.toNat).length + 16`"),

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
  -- #11352: `bgv_u32le`, row 10 of docs/leaf-routine-targets.md. Guest-input u32
  -- accessor with 8 fixture in-edges. The flat triple is DERIVED from the SAsm
  -- `bgvU32leFn_spec` by `Fn.retSpecFlat`, so the machine reasoning is the SAsm proof.
  routine "bgv_u32le" .proven (some "bgvU32leFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bgv_u32le`: `a0 = leU32 bs 0` for "
        ++ "a read-only region of >= 4 bytes, region intact. Only ABI hyps (pointer in "
        ++ "a0, region wf, aligned ra). Tied to the reference by "
        ++ "`leU32_eq_bytesLEtoNat`"),

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
        ++ "routine looks at")
]

/-! ## Counts (kernel-checked) -/

/-- Rows in the guest-routine registry. -/
def routineCount : Nat := routineRegistry.length

/-- Rows at a given tier. -/
def routineCountTier (t : ProofTier) : Nat :=
  (routineRegistry.filter (fun e => e.tier == t)).length

theorem routineCount_eq : routineCount = 43 := by decide

theorem routineProvenCount_eq      : routineCountTier .proven      = 34 := by decide
theorem routineConditionalCount_eq : routineCountTier .conditional = 9 := by decide
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

theorem routineSymbols_eq : routineSymbols.length = 33 := by decide

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

/-- Negative control, kernel-checked on every build: `rlp_item_span` is a real
    `.unproven` Correspondence row today, so witnessing it here would make the
    check fire. A gate nobody has seen fail is indistinguishable from one that
    cannot. -/
example :
    crossVerdictOk ("rlp_item_span" :: routineSymbols) Correspondence.registry
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
private noncomputable abbrev _rlp_item_size_routine_witness :=
  @EvmAsm.Codegen.RlpSpliceHelperSpec.rlp_item_size_spec_within
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
-- #11291: the whole-routine withdrawal decoder (existed since #10782).
private noncomputable abbrev _bgv_u32le_routine_witness :=
  @EvmAsm.Codegen.BgvU32leSpec.bgvU32leFlat_spec
private noncomputable abbrev _check_gas_limit_routine_witness :=
  @EvmAsm.Codegen.CheckGasLimitSAsm.checkGasLimit_ref_spec
private noncomputable abbrev _bytes_to_nibbles_routine_witness :=
  @EvmAsm.Codegen.BytesToNibblesSAsm.bytesToNibblesFlat_spec
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

end EvmAsm.Progress
