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
import EvmAsm.Evm64.AccountAccessorSpec
import EvmAsm.Codegen.Programs.RlpEncodeUintBeComposeSAsm
import EvmAsm.Codegen.Programs.RlpEncodeBytesComposeSAsm
import EvmAsm.Codegen.Programs.RlpSpliceHelperSpec
import EvmAsm.Codegen.Programs.RlpBytesEncodedSizeSAsm
import EvmAsm.Codegen.Programs.RlpBytesEncodedSizeBridge
import EvmAsm.Codegen.Programs.HeaderExtractNumberSpec
import EvmAsm.Codegen.Programs.HeaderExtractNumberBridge
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
  routine "header_extract_number" .proven (some "header_extract_number_spec_within")
      (notes := "8-instruction wrapper: prologue ;; `rlp_field_to_u64` at field index 8 "
        ++ ";; epilogue. The whole-routine triple predates the correspondence row "
        ++ "(#11351) -- a missing row was never evidence of a missing proof. Its step "
        ++ "bound inherits the callee's loose `7 * (2^64 - 1)` tail factor; tracked at "
        ++ "the origin as #11461"),
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
        ++ "non-overlap, non-overflow, aligned ra)")
]

/-! ## Counts (kernel-checked) -/

/-- Rows in the guest-routine registry. -/
def routineCount : Nat := routineRegistry.length

/-- Rows at a given tier. -/
def routineCountTier (t : ProofTier) : Nat :=
  (routineRegistry.filter (fun e => e.tier == t)).length

theorem routineCount_eq : routineCount = 27 := by decide

theorem routineProvenCount_eq      : routineCountTier .proven      = 19 := by decide
theorem routineConditionalCount_eq : routineCountTier .conditional = 8 := by decide
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

theorem routineSymbols_eq : routineSymbols.length = 19 := by decide

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
private noncomputable abbrev _header_extract_number_routine_witness :=
  @EvmAsm.Codegen.HeaderExtractNumberSpec.header_extract_number_spec_within
-- Correspondence row #11351 names this; it is Codegen-side, and Correspondence
-- deliberately does not import Codegen, so the witness abbrev lives here.
private noncomputable abbrev _header_number_of_decode_witness :=
  @EvmAsm.Codegen.HeaderExtractNumberSpec.header_number_of_decode
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

end EvmAsm.Progress
