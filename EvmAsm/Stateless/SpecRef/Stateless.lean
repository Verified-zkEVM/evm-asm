/-
  EvmAsm.Stateless.SpecRef.Stateless

  Port of `execution-specs/src/ethereum/forks/amsterdam/stateless.py`
  (`@tests-zkevm@v0.6.0`, `40f956fab`): the six functions of the stateless
  validation shell.

  * `compute_new_payload_request_root` (`stateless.py:229`)
  * `_decode_header`                   (`stateless.py:244`)
  * `validate_headers`                 (`stateless.py:255`)
  * `_is_activation_active`            (`stateless.py:278`)
  * `validate_chain_config`            (`stateless.py:303`)
  * `verify_stateless_new_payload`     (`stateless.py:321`)

  ## The execution seam

  `verify_stateless_new_payload` calls `execute_new_payload_request`
  (`stateless.py:355`) — full statefull block re-execution
  (`execution_engine.new_payload`). That is NOT ported here (it is the
  whole EVM). We cut at exactly that call: everything on the
  validation/deserialization/hashing side is real; the execution engine is
  an explicit parameter `execute : ExecutionSeam` taking the precise inputs
  the Python call passes (`NewPayloadRequest`, the witness-backed pre-state,
  the `ChainContext`, and the transaction public keys) and returning
  `Except SpecError Unit` (`ok` ≙ Python returning normally, `error` ≙ any
  raised exception). Bead `evm-asm-4ch8f.8` decides how this seam is
  instantiated against the RV64 guest. `executeAlwaysOk` is a placeholder
  so the shell is `#eval`-runnable end-to-end.
-/

import EvmAsm.Stateless.SpecRef.Ssz
import EvmAsm.Stateless.SpecRef.PrecompilesTable

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP (RLPItem decodeFully)

/-! ## `compute_new_payload_request_root` (`stateless.py:229`) -/

/-- Compute the request root for a stateless input via SSZ hash tree root. -/
def compute_new_payload_request_root (si : StatelessInput) : Hash32 :=
  (newPayloadRequestToSsz si.newPayloadRequest).hashTreeRoot

/-! ## `_decode_header` (`stateless.py:244`)

`rlp.decode_to(Header, …)` is type-directed; we decode to a generic RLP
list and discriminate the current fork (amsterdam, 23 fields) from the
previous fork (bpo5, 21 fields) by RLP list length. The field count remains
the fork discriminant.

The per-field typed checks `rlp.decode_to` performs on numeric fields **are**
re-imposed (#11513 — they were previously dropped, making the port looser than
the Python on all nine). They come from two different places in the reference,
and are NOT the same predicate:

* **canonicality** — `_deserialize_to_uint` rejects a leading zero byte on
  every uint field (`ethereum_rlp` 0.1.6, `rlp.py:270-271`);
* **width** — delegated to the target type's `from_be_bytes`, so it binds
  `U64`/`U256` only: `FixedUnsigned.from_be_bytes` raises when the buffer is
  wider than the type (`ethereum_types` 0.4.1, `numeric.py:566-577`), while
  arbitrary-precision `Uint.from_be_bytes` is a plain `int.from_bytes` with no
  length check at all (`numeric.py:523-528`).

So five of the nine fields are width-**unbounded** in the reference; see
`numericFieldWidths`. ⚠️ Those are the versions `execution-specs/uv.lock`
resolves. A stale environment supplies `ethereum_rlp` 0.1.5 /
`ethereum_types` 0.3.0, and reading those inverts a strictness verdict — see
docs/agents/spec-correspondence.md §6a. -/

private def rlpBytes? : RLPItem → Option Bytes
  | .bytes b => some b
  | _ => none

/-- The nine numeric header fields, each paired with the byte width its Python
    annotation implies: `none` for arbitrary-precision `Uint`, `some 32` for
    `U256`, `some 8` for `U64`.

    One table serves both fork arms: `bpo5`'s `Header` carries identical
    annotations at indices 0–20, and index 22 is absent there, where
    `bs.getD 22 []` is the canonical empty field and passes every check. -/
def numericFieldWidths : List (Nat × Option Nat) :=
  [(7,  none),      -- difficulty       : Uint  (amsterdam/blocks.py:152)
   (8,  none),      -- number           : Uint  (:157)
   (9,  none),      -- gas_limit        : Uint  (:162)
   (10, none),      -- gas_used         : Uint  (:178)
   (11, some 32),   -- timestamp        : U256  (:183)
   (15, none),      -- base_fee_per_gas : Uint  (:203)
   (17, some 8),    -- blob_gas_used    : U64   (:218)
   (18, some 8),    -- excess_blob_gas  : U64   (:226)
   (22, some 8)]    -- slot_number      : U64   (:263)

/-- The fixed-width **byte** fields present in BOTH fork arms (indices 0–20),
    with the width their annotation's `FixedBytes.LENGTH` enforces.

    `_deserialize_to_bytes` does not merely check "is it bytes" — it constructs
    the annotated type, and `FixedBytes.__new__` raises when the length is wrong
    (`ethereum_types` 0.4.1, `bytes.py:29-37`). So these are as much a decode
    check as the uint ones (#11615); the port's `getB` had dropped them.

    ⚠️ `extra_data` (12) is absent on purpose: it is plain `Bytes`, genuinely
    unbounded at decode time. Its ≤32 rule is a `validate_header` clause, not a
    decode one. -/
def fixedBytesFieldWidths : List (Nat × Nat) :=
  [(0,  32),   -- parent_hash              : Hash32  = Bytes32
   (1,  32),   -- ommers_hash              : Hash32
   (2,  20),   -- coinbase                 : Address = Bytes20
   (3,  32),   -- state_root               : Root    = Hash32
   (4,  32),   -- transactions_root        : Root
   (5,  32),   -- receipt_root             : Root
   (6,  256),  -- bloom                    : Bloom   = Bytes256
   (13, 32),   -- prev_randao              : Bytes32
   (14, 8),    -- nonce                    : Bytes8
   (16, 32),   -- withdrawals_root         : Root
   (19, 32),   -- parent_beacon_block_root : Root
   (20, 32)]   -- requests_hash            : Hash32

/-- Fixed-width byte fields that exist ONLY in the current-fork (23-field) arm.

    ⚠️ This split is why #11615 could not copy #11513's shape. A missing numeric
    field reads as `bs.getD i [] = []`, and `[]` passes every uint check
    (canonical, length 0 ≤ any bound), so the numeric sweep was safe to run
    unconditionally. `[]` does **not** pass `length = 32`, so sweeping index 21
    over a 21-field header would reject every previous-fork block. -/
def currentForkBytesFieldWidths : List (Nat × Nat) :=
  [(21, 32)]   -- block_access_list_hash : Hash32

/-- One numeric field through `rlp.decode_to`'s uint path, with the error
    remapped to this decoder's own.

    Delegates to `decodeItemScalar`, the existing port of
    `_deserialize_to_uint` + `from_be_bytes`, whose `Option Nat` width argument
    already models the `Uint`-vs-`FixedUnsigned` split — so the two checks live
    in exactly one place in the tree. -/
private def getNChecked (maxBytes : Option Nat) (b : Bytes) : Except SpecError Nat :=
  match decodeItemScalar maxBytes (.bytes b) with
  | .ok n => .ok n
  | .error _ => .error .headerDecodeError

/-- Every numeric field passes its typed check. -/
private def numericFieldsOk (bs : List Bytes) : Bool :=
  numericFieldWidths.all fun p =>
    match getNChecked p.2 (bs.getD p.1 []) with
    | .ok _ => true
    | .error _ => false

/-- One fixed-width byte field through `rlp.decode_to`'s bytes path. -/
private def getBChecked (width : Nat) (b : Bytes) : Except SpecError Bytes :=
  match decodeItemFixedBytes width (.bytes b) with
  | .ok out => .ok out
  | .error _ => .error .headerDecodeError

/-- Every fixed-width byte field in the given arm has its annotated length. -/
private def bytesFieldsOk (isCurrent : Bool) (bs : List Bytes) : Bool :=
  let tbl := if isCurrent then fixedBytesFieldWidths ++ currentForkBytesFieldWidths
             else fixedBytesFieldWidths
  tbl.all fun p =>
    match getBChecked p.2 (bs.getD p.1 []) with
    | .ok _ => true
    | .error _ => false

/-- Every field passes its typed check, in the decoder's error monad. -/
private def checkNumericFields (isCurrent : Bool) (bs : List Bytes) :
    Except SpecError Unit :=
  if numericFieldsOk bs && bytesFieldsOk isCurrent bs then .ok ()
  else .error .headerDecodeError

/-- Build a `Header` from its decoded RLP field bytes. Fields 21–22
    (`block_access_list_hash`, `slot_number`) are amsterdam-only and default
    to `[]`/`0` for the previous fork.

    This is the field **assignment** only; the typed checks are
    `checkNumericFields`, and `_decode_header` runs both. Assigning
    `bytesBEtoNat` here rather than the checked decoder's result is not a
    weakening: `getNChecked_value` proves the two agree whenever the check
    passes.

    Public so a caller can read off ANY field of a successfully decoded header
    via `decode_header_inv`. `rlpBytes?` stays private, so that lemma is still
    the only door into `_decode_header` itself. -/
def mkHeaderFields (isCurrent : Bool) (bs : List Bytes) : Header :=
  let getB := fun i => bs.getD i []
  let getN := fun i => bytesBEtoNat (bs.getD i [])
  { isCurrentFork := isCurrent
    parentHash := getB 0, ommersHash := getB 1, coinbase := getB 2,
    stateRoot := getB 3, transactionsRoot := getB 4, receiptRoot := getB 5,
    bloom := getB 6, difficulty := getN 7, number := getN 8, gasLimit := getN 9,
    gasUsed := getN 10, timestamp := getN 11, extraData := getB 12,
    prevRandao := getB 13, nonce := getB 14, baseFeePerGas := getN 15,
    withdrawalsRoot := getB 16, blobGasUsed := getN 17, excessBlobGas := getN 18,
    parentBeaconBlockRoot := getB 19, requestsHash := getB 20,
    blockAccessListHash := getB 21, slotNumber := getN 22 }

/-- One fork arm: the typed checks, then the field assignment. Ordering matches
    the reference, which discriminates on schema (arity) and validates the
    fields of whichever arm it is in. -/
private def decodeHeaderArm (isCurrent : Bool) (bs : List Bytes) :
    Except SpecError Header :=
  match checkNumericFields isCurrent bs with
  | .error e => .error e
  | .ok _ => .ok (mkHeaderFields isCurrent bs)

/-- Decode an RLP-encoded header, current fork (23 fields) first, else the
    previous fork (21 fields).

    The reference's `except rlp.DecodingError: return rlp.decode_to(
    PreviousForkHeader, …)` fallback is why a content failure in one arm is not
    observably different from an arity failure: a 23-field list whose field
    content is invalid falls through to the 21-field schema and fails there on
    arity. Either way, error. -/
def _decode_header (header_bytes : Bytes) : Except SpecError Header :=
  match decodeFully header_bytes with
  | some (.list items) =>
      match items.mapM rlpBytes? with
      | none => .error .headerDecodeError
      | some bs =>
          if bs.length = 23 then decodeHeaderArm true bs
          else if bs.length = 21 then decodeHeaderArm false bs
          else .error .headerDecodeError
  | _ => .error .headerDecodeError

/-- Indexing view of `items.mapM rlpBytes?`: it succeeds exactly when every
    item is a byte string, and then the `i`th decoded field is the `i`th item's
    payload.  Stated here because `rlpBytes?` is private to this module. -/
private theorem mapM_rlpBytes_spec :
    ∀ (items : List RLPItem) (bs : List Bytes),
      items.mapM rlpBytes? = some bs →
      bs.length = items.length ∧
        ∀ i, i < items.length → items[i]? = some (.bytes (bs.getD i [])) := by
  intro items
  induction items with
  | nil =>
      intro bs h
      rw [List.mapM_nil] at h
      have hb : bs = [] := (Option.some.inj h).symm
      subst hb
      exact ⟨rfl, by intro i hi; exact absurd hi (by simp)⟩
  | cons it rest ih =>
      intro bs h
      cases hit : rlpBytes? it with
      | none => rw [List.mapM_cons, hit] at h; simp at h
      | some b =>
          cases hrest : rest.mapM rlpBytes? with
          | none => rw [List.mapM_cons, hit, hrest] at h; simp at h
          | some bs' =>
              rw [List.mapM_cons, hit, hrest] at h
              simp at h
              subst h
              have hb : it = .bytes b := by
                cases it with
                | bytes q => simp [rlpBytes?] at hit; rw [hit]
                | list _ => simp [rlpBytes?] at hit
              obtain ⟨hlen, hidx⟩ := ih bs' hrest
              refine ⟨by simp [hlen], ?_⟩
              intro i hi
              cases i with
              | zero => simp [hb]
              | succ k =>
                  simp only [List.getElem?_cons_succ, List.length_cons] at *
                  have := hidx k (by omega)
                  simpa using this

/-- The checked decoder agrees with the plain big-endian reading on every input
    it accepts. This is what makes `mkHeaderFields`' `bytesBEtoNat` assignment a
    faithful rendering of `decode_to`'s per-field result rather than a weakening
    of it. -/
theorem getNChecked_value {w : Option Nat} {b : Bytes} {n : Nat}
    (h : getNChecked w b = .ok n) : n = bytesBEtoNat b := by
  unfold getNChecked at h
  split at h
  · rename_i n' hscalar
    exact (Except.ok.inj h) ▸ decodeItemScalar_value hscalar
  · exact absurd h (by simp)

/-- Both of `rlp.decode_to`'s uint checks, read back off a successful field
    decode: no leading zero byte, and — only when the annotated type is
    fixed-width — no more bytes than the type admits. -/
theorem getNChecked_checks {w : Option Nat} {b : Bytes} {n : Nat}
    (h : getNChecked w b = .ok n) :
    (∀ c, b.head? = some c → c ≠ 0) ∧ (∀ W, w = some W → b.length ≤ W) := by
  unfold getNChecked at h
  split at h
  · rename_i n' hscalar
    exact decodeItemScalar_checks hscalar
  · exact absurd h (by simp)

/-- Membership inversion: a passing sweep means each listed field decoded. -/
private theorem numericFieldsOk_mem {bs : List Bytes} (h : numericFieldsOk bs = true)
    {i : Nat} {w : Option Nat} (hmem : (i, w) ∈ numericFieldWidths) :
    ∃ n, getNChecked w (bs.getD i []) = .ok n := by
  unfold numericFieldsOk at h
  rw [List.all_eq_true] at h
  have hp := h _ hmem
  dsimp only at hp
  cases hg : getNChecked w (bs.getD i []) with
  | ok n => exact ⟨n, rfl⟩
  | error e => rw [hg] at hp; simp at hp

/-- The same, for the fixed-width byte fields of the arm that was taken. -/
private theorem bytesFieldsOk_mem {isCurrent : Bool} {bs : List Bytes}
    (h : bytesFieldsOk isCurrent bs = true) {i w : Nat}
    (hmem : (i, w) ∈ fixedBytesFieldWidths ∨
      (isCurrent = true ∧ (i, w) ∈ currentForkBytesFieldWidths)) :
    (bs.getD i []).length = w := by
  unfold bytesFieldsOk at h
  rw [List.all_eq_true] at h
  have hmem' : (i, w) ∈ (if isCurrent then
      fixedBytesFieldWidths ++ currentForkBytesFieldWidths
    else fixedBytesFieldWidths) := by
    cases isCurrent with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        rcases hmem with hm | ⟨hc, -⟩
        · exact hm
        · exact absurd hc (by simp)
    | true =>
        simp only [if_true]
        rcases hmem with hm | ⟨-, hm⟩
        · exact List.mem_append_left _ hm
        · exact List.mem_append_right _ hm
  have hp := h _ hmem'
  dsimp only at hp
  cases hg : getBChecked w (bs.getD i []) with
  | error e => rw [hg] at hp; simp at hp
  | ok out =>
      unfold getBChecked at hg
      split at hg
      · rename_i out' hfx
        exact (decodeItemFixedBytes_inv hfx).2
      · exact absurd hg (by simp)

/-- Inversion of a successful header decode, in vocabulary a caller can use:
    the input decodes fully to a list of byte strings, of one of the two
    permitted arities, the header is the port's field assignment on those bytes,
    and every numeric field passed `rlp.decode_to`'s typed checks.

    Needed because `rlpBytes?` is private, so `_decode_header` cannot be
    inverted from outside this module.

    The last two conjuncts are what a guest-correspondence bridge consumes
    (#11513, #11575): the equation for ANY field follows from the
    `mkHeaderFields` conjunct by `rfl`, and the canonicality/width facts arrive
    indexed, so a bridge instantiates them at its own field instead of carrying
    them as caller obligations.

    ⚠️ The width fact is vacuous for the five arbitrary-precision `Uint` fields
    (7, 8, 9, 10, 15) — the reference imposes no bound there, so neither does
    this. A guest that reads such a field into a 64-bit register is stricter
    than the reference, and that is a guest-side restriction which cannot be
    discharged from here. -/
theorem decode_header_inv {hb : Bytes} {hdr : Header}
    (h : _decode_header hb = .ok hdr) :
    ∃ (items : List RLPItem) (bs : List Bytes),
      decodeFully hb = some (.list items) ∧
        bs.length = items.length ∧
        (bs.length = 23 ∨ bs.length = 21) ∧
        (∀ i, i < items.length → items[i]? = some (.bytes (bs.getD i []))) ∧
        hdr = mkHeaderFields (bs.length == 23) bs ∧
        (∀ i w, (i, w) ∈ numericFieldWidths →
          (∀ c, (bs.getD i []).head? = some c → c ≠ 0) ∧
          (∀ W, w = some W → (bs.getD i []).length ≤ W)) ∧
        (∀ i w, (i, w) ∈ fixedBytesFieldWidths ∨
            (bs.length = 23 ∧ (i, w) ∈ currentForkBytesFieldWidths) →
          (bs.getD i []).length = w) := by
  unfold _decode_header at h
  split at h
  · rename_i items hfull
    split at h
    · exact absurd h (by simp)
    · rename_i bs hmap
      obtain ⟨hlen, hidx⟩ := mapM_rlpBytes_spec items bs hmap
      -- both arms run the same check first, so the field facts are shared
      have harm : ∀ (isCurrent : Bool) (hdr' : Header),
          decodeHeaderArm isCurrent bs = .ok hdr' →
          hdr' = mkHeaderFields isCurrent bs ∧ numericFieldsOk bs = true ∧
            bytesFieldsOk isCurrent bs = true := by
        intro isCurrent hdr' harm
        unfold decodeHeaderArm at harm
        cases hchk : checkNumericFields isCurrent bs with
        | error e => rw [hchk] at harm; simp at harm
        | ok u =>
            rw [hchk] at harm
            refine ⟨(Except.ok.inj harm).symm, ?_⟩
            unfold checkNumericFields at hchk
            split at hchk
            · rename_i hok
              exact ⟨(Bool.and_eq_true .. ▸ hok).1, (Bool.and_eq_true .. ▸ hok).2⟩
            · simp at hchk
      have hfields : numericFieldsOk bs = true →
          ∀ i w, (i, w) ∈ numericFieldWidths →
            (∀ c, (bs.getD i []).head? = some c → c ≠ 0) ∧
            (∀ W, w = some W → (bs.getD i []).length ≤ W) := by
        intro hok i w hmem
        obtain ⟨n, hn⟩ := numericFieldsOk_mem hok hmem
        exact getNChecked_checks hn
      split at h
      · rename_i h23
        obtain ⟨hval, hchk, hbchk⟩ := harm true hdr h
        refine ⟨items, bs, hfull, hlen, Or.inl h23, hidx,
          by rw [hval]; congr 1; simp [h23], hfields hchk, ?_⟩
        intro i w hmem
        exact bytesFieldsOk_mem hbchk
          (by rcases hmem with hm | ⟨-, hm⟩
              · exact Or.inl hm
              · exact Or.inr ⟨rfl, hm⟩)
      · split at h
        · rename_i h21
          obtain ⟨hval, hchk, hbchk⟩ := harm false hdr h
          refine ⟨items, bs, hfull, hlen, Or.inr h21, hidx,
            by rw [hval]; congr 1; simp [h21], hfields hchk, ?_⟩
          intro i w hmem
          refine bytesFieldsOk_mem hbchk ?_
          rcases hmem with hm | ⟨h23', -⟩
          · exact Or.inl hm
          · exact absurd (h21 ▸ h23') (by decide)
        · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## `validate_headers` (`stateless.py:255`) -/

/-- Validate that a sequence of encoded headers forms a contiguous chain.
    Each header's `parent_hash` must match the hash of the preceding header.
    Returns the decoded headers and their block hashes. -/
def validate_headers (encoded_headers : List Bytes) :
    Except SpecError (List Header × List Hash32) := do
  if encoded_headers.length > 256 then
    throw (.tooManyHeaders encoded_headers.length)
  let headers ← encoded_headers.mapM _decode_header
  let block_hashes : List Hash32 := encoded_headers.map keccak256
  -- headers[i].parent_hash == block_hashes[i-1] for i in 1..len
  let contiguous := (headers.drop 1).zip block_hashes
    |>.all (fun p => p.1.parentHash == p.2)
  if contiguous then pure (headers, block_hashes)
  else throw .headersNotContiguous

/-! ## `_is_activation_active` (`stateless.py:278`) -/

/-- Whether an activation point is active for the payload. -/
def _is_activation_active (activation : ForkActivation) (ep : ExecutionPayload) :
    Except SpecError Bool := do
  if activation.blockNumber.isNone ∧ activation.timestamp.isNone then
    throw .forkActivationMissing
  if let some bn := activation.blockNumber then
    if ep.blockNumber < bn then return false
  if let some ts := activation.timestamp then
    if ep.timestamp < ts then return false
  return true

/-! ## `validate_chain_config` (`stateless.py:303`)

v0.6.0 deletes the Amsterdam-fork and blob-schedule checks
(`UnsupportedForkConfigError`, `_expected_amsterdam_blob_schedule`):
fork identity is carried by the input's schema id, and the blob
schedule is compiled into the guest. Only activation checking remains. -/

/-- Validate and return the target payload's active fork config. -/
def validate_chain_config (chain_config : ChainConfig) (npr : NewPayloadRequest) :
    Except SpecError ForkConfig := do
  let active_fork := chain_config.activeFork
  let execution_payload := npr.executionPayload
  if !(← _is_activation_active active_fork.activation execution_payload) then
    throw .inactiveForkConfig
  pure active_fork

/-! ## The execution seam

The seam interface (`ChainContext`, `ExecutionSeamInput`,
`ExecutionSeam`, `executeAlwaysOk`) lives in `Seam.lean`; the default
below is `elExecute` (`PrecompilesTable.lean`): the FULL ported
`execute_new_payload_request` (pre-checks + `execute_block` +
`apply_body` + post-state root, `ElExecute.lean`) over the complete
18-entry precompile table — no fallback. -/

/-! ## `verify_stateless_new_payload` (`stateless.py:321`) -/

/-- Statelessly validate the execution payload. Every exception the Python
    `try` would catch is folded into `successful_validation = false`. -/
def verify_stateless_new_payload (si : StatelessInput)
    (execute : ExecutionSeam := elExecute) : StatelessValidationResult :=
  let new_payload_request_root := compute_new_payload_request_root si
  let witness := si.witness
  let attempt : Except SpecError Unit := do
    let _ ← validate_chain_config si.chainConfig si.newPayloadRequest
    let (decoded_headers, block_hashes) ← validate_headers witness.headers
    let parent_header ← match decoded_headers.getLast? with
      | some h => pure h
      | none => throw (.executionRejected "no witness headers")  -- decoded_headers[-1]
    let chain_context : ChainContext :=
      { chainId := si.chainConfig.chainId
        blockHashes := block_hashes
        parentHeader := parent_header }
    let pre_state : WitnessPreState :=
      { nodeDb := build_node_db witness.state
        stateRoot := parent_header.stateRoot
        codeDb := build_code_db witness.codes }
    execute { newPayloadRequest := si.newPayloadRequest
              preState := pre_state
              chainContext := chain_context
              transactionPublicKeys := si.publicKeys }
  { newPayloadRequestRoot := new_payload_request_root
    successfulValidation := (match attempt with | .ok _ => true | .error _ => false)
    chainConfig := si.chainConfig }

/-! ## Sanity checks -/

def sanityForkConfig : ForkConfig :=
  { activation := { blockNumber := none, timestamp := some 100 } }

-- Build a minimal RLP header with `n` fields, field 0 = parent_hash,
-- field 3 = state_root, all others empty.
/-- The annotated width of field `i`, or 0 for the numeric and variable-length
    fields (whose canonical zero/empty encoding is `[]`). -/
def testFieldWidth (i : Nat) : Nat :=
  match (fixedBytesFieldWidths ++ currentForkBytesFieldWidths).find?
      (fun p => p.1 == i) with
  | some p => p.2
  | none => 0

/-- ⚠️ Every fixed-width byte field is filled to its ANNOTATED width, not to `[]`.
    Before #11615 this filled them all with `.bytes []`, which the port accepted
    because `getB` had no width check — so the guards were exercising headers
    `rlp.decode_to` would have rejected outright. -/
def mkTestHeaderBytes (n : Nat) (parentHash stateRoot : Bytes) : Bytes :=
  let fields : List RLPItem := (List.range n).map (fun i =>
    if i = 0 then .bytes parentHash
    else if i = 3 then .bytes stateRoot
    else .bytes (List.replicate (testFieldWidth i) 0))
  EvmAsm.EL.RLP.encode (.list fields)

-- Amsterdam header (23 fields) decodes with isCurrentFork = true.
#guard
  match _decode_header (mkTestHeaderBytes 23 (List.replicate 32 0x01) (List.replicate 32 0x02)) with
  | .ok h => h.isCurrentFork && h.parentHash == List.replicate 32 0x01
             && h.stateRoot == List.replicate 32 0x02
  | .error _ => false

-- Previous-fork header (21 fields) decodes with isCurrentFork = false.
#guard
  match _decode_header (mkTestHeaderBytes 21 (List.replicate 32 0x03) (List.replicate 32 0x04)) with
  | .ok h => (!h.isCurrentFork) && h.parentHash == List.replicate 32 0x03
  | .error _ => false

-- A header with a bad field count is rejected.
#guard match _decode_header (mkTestHeaderBytes 20 [] []) with
  | .error .headerDecodeError => true | _ => false

/-- Test header bytes with one field overridden, for the per-field typed checks.
    Every other field is the canonical empty encoding. -/
def mkTestHeaderBytesAt (n idx : Nat) (v : Bytes) : Bytes :=
  let fields : List RLPItem := (List.range n).map (fun i =>
    if i = idx then .bytes v
    else .bytes (List.replicate (testFieldWidth i) 0))
  EvmAsm.EL.RLP.encode (.list fields)

/-! ### The per-field typed checks (#11513)

These are the only executable evidence for `_decode_header`'s field validation:
the correspondence harness registers no `header` family, so there is no CPython
differential to inherit here. -/

-- A leading zero byte is non-canonical on an arbitrary-precision field …
#guard match _decode_header (mkTestHeaderBytesAt 23 8 [0x00, 0x01]) with
  | .error .headerDecodeError => true | _ => false

-- … and on a fixed-width one.
#guard match _decode_header (mkTestHeaderBytesAt 23 17 [0x00, 0x01]) with
  | .error .headerDecodeError => true | _ => false

-- A `U64` field wider than eight bytes is out of range.
#guard match _decode_header (mkTestHeaderBytesAt 23 22 (List.replicate 9 0x01)) with
  | .error .headerDecodeError => true | _ => false

-- `timestamp` is `U256`, so its bound is 32 bytes, not 8: 32 fits, 33 does not.
#guard match _decode_header (mkTestHeaderBytesAt 23 11 (List.replicate 32 0x01)) with
  | .ok _ => true | .error _ => false
#guard match _decode_header (mkTestHeaderBytesAt 23 11 (List.replicate 33 0x01)) with
  | .error .headerDecodeError => true | _ => false

-- ⚠️ The load-bearing NEGATIVE case. `number` is arbitrary-precision `Uint`, whose
-- `from_be_bytes` has no length check, so a nine-byte field is ACCEPTED here
-- exactly as `rlp.decode_to` accepts it. A guest reading this field into a 64-bit
-- register is stricter than the reference — a GUEST-side restriction, which the
-- port must not adopt. Tightening this to 8 would make the port stricter than the
-- Python in order to hide that, which is the opposite of the fix (#11513).
#guard match _decode_header (mkTestHeaderBytesAt 23 8 (List.replicate 9 0x01)) with
  | .ok h => h.number == bytesBEtoNat (List.replicate 9 (0x01 : EvmAsm.EL.RLP.Byte))
  | .error _ => false

-- Same for `gas_limit`/`gas_used`/`difficulty`/`base_fee_per_gas`.
#guard match _decode_header (mkTestHeaderBytesAt 23 9 (List.replicate 12 0x01)) with
  | .ok _ => true | .error _ => false

/-! ### The fixed-width BYTE field checks (#11615)

`_deserialize_to_bytes` constructs the annotated type, and `FixedBytes.__new__`
raises when the length is wrong -- so these are decode checks too, and `getB` had
dropped them. -/

-- A short `Root` is rejected (`state_root` must be exactly 32).
#guard match _decode_header (mkTestHeaderBytesAt 23 3 (List.replicate 31 0)) with
  | .error .headerDecodeError => true | _ => false

-- ... and a long one.
#guard match _decode_header (mkTestHeaderBytesAt 23 3 (List.replicate 33 0)) with
  | .error .headerDecodeError => true | _ => false

-- `Address` is 20, not 32.
#guard match _decode_header (mkTestHeaderBytesAt 23 2 (List.replicate 32 0)) with
  | .error .headerDecodeError => true | _ => false
#guard match _decode_header (mkTestHeaderBytesAt 23 2 (List.replicate 20 0)) with
  | .ok _ => true | .error _ => false

-- `Bloom` is 256 -- the width `header_extract_logs_bloom`'s success arm needs.
#guard match _decode_header (mkTestHeaderBytesAt 23 6 (List.replicate 255 0)) with
  | .error .headerDecodeError => true | _ => false
#guard match _decode_header (mkTestHeaderBytesAt 23 6 (List.replicate 256 0)) with
  | .ok h => h.bloom.length == 256 | .error _ => false

-- `nonce` is `Bytes8`.
#guard match _decode_header (mkTestHeaderBytesAt 23 14 (List.replicate 32 0)) with
  | .error .headerDecodeError => true | _ => false

-- `extra_data` (12) is plain `Bytes`: unbounded AT DECODE TIME. The <=32 rule is a
-- `validate_header` clause, not a decode one, so a 40-byte field decodes fine here.
#guard match _decode_header (mkTestHeaderBytesAt 23 12 (List.replicate 40 0)) with
  | .ok h => h.extraData.length == 40 | .error _ => false

-- ⚠️ THE REGRESSION THIS COULD HAVE CAUSED. Index 21 exists only in the 23-field
-- arm, so sweeping it unconditionally would reject every previous-fork header --
-- `bs.getD 21 []` is `[]`, which fails `length = 32` where it passes every uint
-- check. The arity split is what stops that; this guard pins it.
#guard match _decode_header (mkTestHeaderBytes 21 (List.replicate 32 0x03)
    (List.replicate 32 0x04)) with
  | .ok h => !h.isCurrentFork | .error _ => false

-- Two contiguous headers validate; a non-contiguous pair does not.
#guard
  let h0 := mkTestHeaderBytes 23 (List.replicate 32 0x00) (List.replicate 32 0x00)
  let h0hash := keccak256 h0
  let h1 := mkTestHeaderBytes 23 h0hash (List.replicate 32 0x05)
  match validate_headers [h0, h1] with
  | .ok (hs, hashes) => hs.length == 2 && hashes.length == 2
  | .error _ => false

#guard
  let h0 := mkTestHeaderBytes 23 (List.replicate 32 0x00) (List.replicate 32 0x00)
  let h1 := mkTestHeaderBytes 23 (List.replicate 32 0xEE) (List.replicate 32 0x05)  -- wrong parent
  match validate_headers [h0, h1] with
  | .error .headersNotContiguous => true | _ => false

-- Activation: active when payload meets the timestamp; missing both fails.
#guard
  let ep : ExecutionPayload := (Inhabited.default : ExecutionPayload)
  match _is_activation_active { blockNumber := none, timestamp := some 0 } ep with
  | .ok b => b | _ => false

#guard
  match _is_activation_active { blockNumber := none, timestamp := none }
      (Inhabited.default : ExecutionPayload) with
  | .error .forkActivationMissing => true | _ => false

end EvmAsm.Stateless.SpecRef
