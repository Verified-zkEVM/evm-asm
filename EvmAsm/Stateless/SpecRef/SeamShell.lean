/-
  EvmAsm.Stateless.SpecRef.SeamShell

  The seam shell (bead `evm-asm-s1d19.3`): the
  `execute_new_payload_request` pre-checks and `execute_block`'s
  pre-execution frame, wired as the first *partial* execution seam
  under the monotone sound-for-accepts discipline
  (docs/agents/specref-execution-seam-scope.md §3).  Ports, at
  `@tests-zkevm@v0.5.0` (`bd8c673`):

  * `execution_engine/requests.py`: `_encode_deposit`,
    `_encode_withdrawal`, `_encode_consolidation`,
    `encode_execution_requests` (functions of the same names)
  * `requests.py`: `compute_requests_hash` (function
    `compute_requests_hash`)
  * `execution_engine/validation_helpers.py`: `_payload_header`,
    `_payload_block` (functions of the same names)
  * `execution_engine/new_payload.py`: `is_valid_block_hash`,
    `is_valid_versioned_hashes`, and the pre-check prefix of
    `execute_new_payload_request` (functions of the same names)
  * `fork.py`: `MAX_RLP_BLOCK_SIZE`, `EMPTY_OMMER_HASH`,
    `check_gas_limit`, `calculate_base_fee_per_gas`, `validate_header`
    (functions/constants of the same names)

  ## The partial seam (`executeSeamShell`)

  A partial seam may reject ONLY on checks the real spec's *accepting*
  path unconditionally performs (scope doc §3).  `executeSeamShell`
  rejects exactly on: the `execute_new_payload_request` pre-checks
  (empty-tx, block-hash, versioned-hashes), `execute_block`'s
  pre-execution frame (public-key count, `MAX_RLP_BLOCK_SIZE`,
  `validate_header`, ommers-empty — ommers are empty by construction
  from `_payload_block`), and root-anchored witness authentication
  (`decode_witness_to_mpt` on `pre_state.stateRoot` — the accepting
  path always decodes the state trie for the post-root computation).
  `apply_body` and the eight post-execution root checks remain the
  accepted stub until Stack C (`s1d19.5`) supplies them.

  The tx/withdrawals tries in `_payload_header` are Python
  `Trie(secured=False, default=None)` + `root(trie)`; here
  `build_mpt`/`mpt_root` (`IncrementalMptWrite.lean`), whose
  equivalence with `patricialize` is `#guard`-pinned there.
-/

import EvmAsm.Stateless.SpecRef.Seam
import EvmAsm.Stateless.SpecRef.Gas
import EvmAsm.Stateless.SpecRef.BlocksRlp
import EvmAsm.Stateless.SpecRef.Transactions
import EvmAsm.Stateless.SpecRef.IncrementalMptWrite

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP (RLPItem)

private def encS (i : RLPItem) : Bytes := EvmAsm.EL.RLP.encode i

/-! ## Request encoding (`execution_engine/requests.py`) -/

/-- 8-byte little-endian (`U64.to_le_bytes8`). -/
private def leBytes8 (n : Nat) : Bytes :=
  (List.range 8).map (fun i => BitVec.ofNat 8 (n >>> (8 * i)))

/-- `_encode_deposit(d)`. -/
def _encode_deposit (d : DepositRequest) : Bytes :=
  d.pubkey ++ d.withdrawalCredentials ++ leBytes8 d.amount
    ++ d.signature ++ leBytes8 d.index

/-- `_encode_withdrawal(w)`. -/
def _encode_withdrawal (w : WithdrawalRequest) : Bytes :=
  w.sourceAddress ++ w.validatorPubkey ++ leBytes8 w.amount

/-- `_encode_consolidation(c)`. -/
def _encode_consolidation (c : ConsolidationRequest) : Bytes :=
  c.sourceAddress ++ c.sourcePubkey ++ c.targetPubkey

/-- `_encode_builder_deposit` (EIP-8282). -/
def _encode_builder_deposit (b : BuilderDepositRequest) : Bytes :=
  b.pubkey ++ b.withdrawalCredentials ++ leBytes8 b.amount ++ b.signature

/-- `_encode_builder_exit` (EIP-8282). -/
def _encode_builder_exit (b : BuilderExitRequest) : Bytes :=
  b.sourceAddress ++ b.pubkey

/-- `encode_execution_requests(requests)`: each non-empty list becomes
    one `TYPE_BYTE ++ concat(items)` blob, ascending type order
    (deposit `0x00`, withdrawal `0x01`, consolidation `0x02`, builder
    deposit `0x03`, builder exit `0x04`); empty lists are omitted. -/
def encode_execution_requests (requests : ExecutionRequests) : List Bytes :=
  (if requests.deposits.isEmpty then [] else
    [0x00 :: (requests.deposits.flatMap _encode_deposit)])
  ++ (if requests.withdrawals.isEmpty then [] else
    [0x01 :: (requests.withdrawals.flatMap _encode_withdrawal)])
  ++ (if requests.consolidations.isEmpty then [] else
    [0x02 :: (requests.consolidations.flatMap _encode_consolidation)])
  ++ (if requests.builderDeposits.isEmpty then [] else
    [0x03 :: (requests.builderDeposits.flatMap _encode_builder_deposit)])
  ++ (if requests.builderExits.isEmpty then [] else
    [0x04 :: (requests.builderExits.flatMap _encode_builder_exit)])

/-! ## `compute_requests_hash` (`requests.py`, function `compute_requests_hash`) -/

/-- `sha256(concat(sha256(request) for request))` (EIP-7685). -/
def compute_requests_hash (requests : List Bytes) : Hash32 :=
  sha256 (requests.flatMap sha256)

/-! ## `_payload_header` / `_payload_block`
(`execution_engine/validation_helpers.py`, functions `_payload_header`
and `_payload_block`) -/

/-- `EMPTY_OMMER_HASH = keccak256(rlp.encode([]))` (`fork.py`). -/
def EMPTY_OMMER_HASH : Hash32 := keccak256 (encS (.list []))

/-- The unsecured rlp-indexed trie root over a list of encoded values
    (the `Trie(secured=False, default=None)` + `trie_set` + `root`
    pattern of `_payload_header`). -/
def indexedTrieRoot (values : List Bytes) : Except SpecError Root := do
  let data := values.zipIdx.map (fun (v, i) =>
    (encS (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE i)), MptValue.bytes v))
  mpt_root (← build_mpt data false none)

/-- `_payload_header(execution_payload, parent_beacon_block_root,
    execution_requests)`. -/
def _payload_header (payload : ExecutionPayload)
    (parent_beacon_block_root : Root)
    (execution_requests : ExecutionRequests) : Except SpecError Header := do
  let transactions_root ← indexedTrieRoot payload.transactions
  let withdrawals_root ← indexedTrieRoot
    (payload.withdrawals.map (fun w => encS (withdrawalToRlpItem w)))
  let requests_hash :=
    compute_requests_hash (encode_execution_requests execution_requests)
  pure { isCurrentFork := true
         parentHash := payload.parentHash
         ommersHash := EMPTY_OMMER_HASH
         coinbase := payload.feeRecipient
         stateRoot := payload.stateRoot
         transactionsRoot := transactions_root
         receiptRoot := payload.receiptsRoot
         bloom := payload.logsBloom
         difficulty := 0
         number := payload.blockNumber
         gasLimit := payload.gasLimit
         gasUsed := payload.gasUsed
         timestamp := payload.timestamp
         extraData := payload.extraData
         prevRandao := payload.prevRandao
         nonce := List.replicate 8 0x00
         baseFeePerGas := payload.baseFeePerGas
         withdrawalsRoot := withdrawals_root
         blobGasUsed := payload.blobGasUsed
         excessBlobGas := payload.excessBlobGas
         parentBeaconBlockRoot := parent_beacon_block_root
         requestsHash := requests_hash
         blockAccessListHash := keccak256 payload.blockAccessList
         slotNumber := payload.slotNumber }

/-- `_payload_block(...)`: the header plus the payload's raw
    transactions/withdrawals, no ommers. -/
def _payload_block (payload : ExecutionPayload)
    (parent_beacon_block_root : Root)
    (execution_requests : ExecutionRequests) : Except SpecError Block := do
  pure { header := ← _payload_header payload parent_beacon_block_root execution_requests
         transactions := payload.transactions
         ommers := []
         withdrawals := payload.withdrawals }

/-! ## `is_valid_block_hash` / `is_valid_versioned_hashes`
(`execution_engine/new_payload.py`, functions of the same names) -/

/-- `is_valid_block_hash`: the payload's `block_hash` is
    `keccak256(rlp.encode(header))` of the implied header; any failure
    building the header is `False`. -/
def is_valid_block_hash (payload : ExecutionPayload)
    (parent_beacon_block_root : Root)
    (execution_requests : ExecutionRequests) : Bool :=
  match _payload_header payload parent_beacon_block_root execution_requests with
  | .error _ => false
  | .ok header => headerHash header == payload.blockHash

/-- `is_valid_versioned_hashes`: blob-transaction versioned hashes, in
    payload order, equal the request's list; any decode failure is
    `False`. -/
def is_valid_versioned_hashes (npr : NewPayloadRequest) : Bool :=
  let computed : Except SpecError (List VersionedHash) :=
    npr.executionPayload.transactions.foldlM (init := []) (fun acc encoded_tx => do
      match ← decode_transaction encoded_tx with
      | .blob tx => pure (acc ++ tx.blobVersionedHashes)
      | _ => pure acc)
  match computed with
  | .error _ => false
  | .ok hashes => hashes == npr.versionedHashes

/-! ## `fork.py` pre-execution frame -/

/-- `MAX_RLP_BLOCK_SIZE = MAX_BLOCK_SIZE - SAFETY_MARGIN` (`fork.py`,
    constant `MAX_RLP_BLOCK_SIZE`). -/
def MAX_RLP_BLOCK_SIZE : Nat := 10485760 - 2097152

/-- `check_gas_limit(gas_limit, parent_gas_limit)` (`fork.py`, function
    `check_gas_limit`). -/
def check_gas_limit (gas_limit parent_gas_limit : Uint) : Bool :=
  let max_adjustment_delta := parent_gas_limit / GasCosts.LIMIT_ADJUSTMENT_FACTOR
  if gas_limit ≥ parent_gas_limit + max_adjustment_delta then false
  else if gas_limit + max_adjustment_delta ≤ parent_gas_limit then false
  else if gas_limit < GasCosts.LIMIT_MINIMUM then false
  else true

/-- `calculate_base_fee_per_gas(...)` (`fork.py`, function
    `calculate_base_fee_per_gas`).  The gas-limit check failure is the
    Python `InvalidBlock` raise. -/
def calculate_base_fee_per_gas (block_gas_limit parent_gas_limit
    parent_gas_used parent_base_fee_per_gas : Uint) : Except SpecError Uint := do
  let parent_gas_target := parent_gas_limit / 2  -- ELASTICITY_MULTIPLIER
  if !check_gas_limit block_gas_limit parent_gas_limit then
    throw (.invalidBlock "gas limit out of bounds")
  if parent_gas_used == parent_gas_target then
    pure parent_base_fee_per_gas
  else if parent_gas_used > parent_gas_target then
    let gas_used_delta := parent_gas_used - parent_gas_target
    let parent_fee_gas_delta := parent_base_fee_per_gas * gas_used_delta
    let target_fee_gas_delta := parent_fee_gas_delta / parent_gas_target
    let base_fee_per_gas_delta := max (target_fee_gas_delta / 8) 1
    pure (parent_base_fee_per_gas + base_fee_per_gas_delta)
  else
    let gas_used_delta := parent_gas_target - parent_gas_used
    let parent_fee_gas_delta := parent_base_fee_per_gas * gas_used_delta
    let target_fee_gas_delta := parent_fee_gas_delta / parent_gas_target
    let base_fee_per_gas_delta := target_fee_gas_delta / 8
    pure (parent_base_fee_per_gas - base_fee_per_gas_delta)

/-- `validate_header(parent_header, header)` (`fork.py`, function
    `validate_header`): every failed check is an `InvalidBlock`. -/
def validate_header (parent_header header : Header) :
    Except SpecError Unit := do
  if header.number < 1 then throw (.invalidBlock "block number < 1")
  let excess_blob_gas ← calculate_excess_blob_gas parent_header
  if header.excessBlobGas ≠ excess_blob_gas then
    throw (.invalidBlock "excess blob gas mismatch")
  if header.gasUsed > header.gasLimit then
    throw (.invalidBlock "gas used exceeds limit")
  let expected_base_fee ← calculate_base_fee_per_gas header.gasLimit
    parent_header.gasLimit parent_header.gasUsed parent_header.baseFeePerGas
  if expected_base_fee ≠ header.baseFeePerGas then
    throw (.invalidBlock "base fee mismatch")
  if header.timestamp ≤ parent_header.timestamp then
    throw (.invalidBlock "timestamp not after parent")
  if header.number ≠ parent_header.number + 1 then
    throw (.invalidBlock "block number not parent + 1")
  if header.extraData.length > 32 then
    throw (.invalidBlock "extra data too long")
  if header.difficulty ≠ 0 then throw (.invalidBlock "difficulty nonzero")
  if header.nonce ≠ List.replicate 8 0x00 then
    throw (.invalidBlock "nonce nonzero")
  if header.ommersHash ≠ EMPTY_OMMER_HASH then
    throw (.invalidBlock "ommers hash not empty")
  if header.parentHash ≠ headerHash parent_header then
    throw (.invalidBlock "parent hash mismatch")

/-! ## Static per-transaction checks (sound-for-accepts extension)

The accepting path runs `process_transaction` on every transaction,
whose unconditional prefix (`fork.py`, functions `process_transaction`
and `check_transaction`) performs checks that do NOT depend on
execution state:

* sender recovery from the supplied public key
  (`recover_sender_from_public_key` — pure signature verification);
* `validate_transaction` (intrinsic gas / EIP-7623 floor / EIP-2681
  nonce cap / init-code size — pure);
* the gas-dimension caps against the *initial* availability
  (`regular/state_gas_available ≤ block_gas_limit` always, so
  `min(TX_MAX_GAS_LIMIT, tx.gas) > block_gas_limit` or
  `tx.gas > block_gas_limit` can never pass later);
* cumulative blob gas vs `MAX_BLOB_GAS_PER_BLOCK` (fully determined by
  the payload);
* fee sanity vs the header base fee, blob static checks (count,
  version byte, `max_fee_per_blob_gas` vs the header-derived blob gas
  price), and the EIP-7702 non-empty-authorization check;
* for the FIRST transaction only, against the (witness-backed,
  pre-execution) state: the nonce-too-LOW check — nonces never
  decrease, so `pre_state.nonce > tx.nonce` implies the at-check nonce
  is also too high — and the EOA/delegation sender check — an existing
  account's code cannot change during the pre-tx system calls
  (`set_code` happens only on CREATE at a fresh address or in-tx
  EIP-7702, and hitting an existing account's address with CREATE2
  needs a keccak preimage, the model's standing assumption).  The
  balance and nonce-too-HIGH checks are NOT sound against pre-state
  (adversarial system-contract code could credit/debit the sender or
  drive a delegated sender's CREATE before the first transaction) and
  wait for `apply_body`, as do all later transactions' state checks.

`MAX_BLOB_GAS_PER_BLOCK` / `BLOB_COUNT_LIMIT` /
`VERSIONED_HASH_VERSION_KZG` are `fork.py` constants;
`is_valid_delegation` is `vm/eoa_delegation.py` (function
`is_valid_delegation`). -/

/-- `MAX_BLOB_GAS_PER_BLOCK = BLOB_SCHEDULE_MAX * PER_BLOB` (`fork.py`). -/
def MAX_BLOB_GAS_PER_BLOCK : U64 := GasCosts.BLOB_SCHEDULE_MAX * GasCosts.PER_BLOB
/-- `BLOB_COUNT_LIMIT` (`fork.py`). -/
def BLOB_COUNT_LIMIT : Nat := 6
/-- `VERSIONED_HASH_VERSION_KZG` (`fork.py`). -/
def VERSIONED_HASH_VERSION_KZG : BitVec 8 := 0x01

/-- `is_valid_delegation(code)` (`vm/eoa_delegation.py`, function
    `is_valid_delegation`): 23 bytes prefixed `0xEF0100`. -/
def is_valid_delegation (code : Bytes) : Bool :=
  code.length == 23 && code.take 3 == [0xEF, 0x01, 0x00]

/-- `calculate_total_blob_gas(tx)` (`vm/gas.py`, function
    `calculate_total_blob_gas`). -/
def calculate_total_blob_gas (tx : Transaction) : U64 :=
  match tx with
  | .blob t => GasCosts.PER_BLOB * t.blobVersionedHashes.length
  | _ => 0

/-- The execution-independent prefix of `check_transaction` (`fork.py`,
    function `check_transaction`) for one transaction; returns
    `max_gas_fee` (for the first-tx balance check). -/
def staticCheckTransaction (base_fee_per_gas : Uint)
    (block_gas_limit : Uint) (excess_blob_gas : U64) (tx : Transaction) :
    Except SpecError Uint := do
  if min TX_MAX_GAS_LIMIT tx.gas > block_gas_limit then
    throw (.invalidBlock "regular gas used exceeds limit")
  if tx.gas > block_gas_limit then
    throw (.invalidBlock "state gas used exceeds limit")
  let max_gas_fee ←
    match tx with
    | .feeMarket t => feeCap t.maxFeePerGas t.maxPriorityFeePerGas t.gas
    | .blob t => feeCap t.maxFeePerGas t.maxPriorityFeePerGas t.gas
    | .setCode t => feeCap t.maxFeePerGas t.maxPriorityFeePerGas t.gas
    | .legacy t => legacyCap t.gasPrice t.gas
    | .accessList t => legacyCap t.gasPrice t.gas
  let max_gas_fee ←
    match tx with
    | .blob t => do
        if t.blobVersionedHashes.isEmpty then
          throw (.invalidBlock "no blob data in transaction")
        if t.blobVersionedHashes.length > BLOB_COUNT_LIMIT then
          throw (.invalidBlock "blob count exceeded")
        if t.blobVersionedHashes.any (fun h => h.take 1 != [VERSIONED_HASH_VERSION_KZG]) then
          throw (.invalidBlock "invalid blob versioned hash")
        let blob_gas_price ← calculate_blob_gas_price excess_blob_gas
        if t.maxFeePerBlobGas < blob_gas_price then
          throw (.invalidBlock "insufficient max fee per blob gas")
        pure (max_gas_fee + calculate_total_blob_gas tx * t.maxFeePerBlobGas)
    | _ => pure max_gas_fee
  if let .setCode t := tx then
    if t.authorizations.isEmpty then
      throw (.invalidBlock "empty authorization list")
  pure max_gas_fee
where
  feeCap (maxFee maxPriority gas : Uint) : Except SpecError Uint := do
    if maxFee < maxPriority then
      throw (.invalidBlock "priority fee greater than max fee")
    if maxFee < base_fee_per_gas then
      throw (.invalidBlock "insufficient max fee per gas")
    pure (gas * maxFee)
  legacyCap (gasPrice gas : Uint) : Except SpecError Uint := do
    if gasPrice < base_fee_per_gas then
      throw (.invalidBlock "gas price below base fee")
    pure (gas * gasPrice)

/-- Static per-transaction checks over the whole payload (see the
    section header): sender/pubkey verification + `validate_transaction`
    + the execution-independent `check_transaction` prefix for every
    transaction, cumulative blob gas, and the pre-state nonce / balance
    / EOA checks for the first transaction. -/
def staticTransactionChecks (chain_id : U64) (header : Header)
    (ws : WitnessPreState) (transactions : List Bytes)
    (public_keys : List Bytes) : Except SpecError Unit := do
  let mut total_blob_gas : U64 := 0
  let mut is_first := true
  for (encoded_tx, public_key) in transactions.zip public_keys do
    let tx ← decode_transaction encoded_tx
    let sender ← recover_sender_from_public_key chain_id tx public_key
    let _ ← validate_transaction tx sender
    let _ ← staticCheckTransaction header.baseFeePerGas
      header.gasLimit header.excessBlobGas tx
    total_blob_gas := total_blob_gas + calculate_total_blob_gas tx
    if is_first then
      is_first := false
      -- check_transaction's pre-state reads for the first transaction
      -- (only the checks sound against pre-state; see the header):
      -- get_account(tx_state, sender) on the untouched tracker reads
      -- the witness directly.
      let sender_account := ((← get_account_optional ws sender).getD
        { nonce := 0, balance := 0, codeHash := EMPTY_CODE_HASH })
      if sender_account.nonce > tx.nonce then
        throw (.invalidBlock "nonce too low")
      if sender_account.codeHash != EMPTY_CODE_HASH then
        let sender_code ← get_code ws sender_account.codeHash
        if !is_valid_delegation sender_code then
          throw (.invalidBlock "not EOA")
  if total_blob_gas > MAX_BLOB_GAS_PER_BLOCK then
    throw (.invalidBlock "blob gas limit exceeded")

/-! ## The partial seam -/

/-- The pre-check prefix of `execute_new_payload_request`
    (`new_payload.py`) + `execute_block`'s pre-execution frame
    (`fork.py`) + root-anchored witness authentication, with
    `apply_body` and the post-execution checks still stubbed to accept
    (sound-for-accepts; see the header). -/
def executeSeamShell : ExecutionSeam := fun input => do
  let npr := input.newPayloadRequest
  let payload := npr.executionPayload
  -- execute_new_payload_request pre-checks
  if payload.transactions.any (·.isEmpty) then
    throw (.invalidBlock "Empty transaction in payload")
  if !is_valid_block_hash payload npr.parentBeaconBlockRoot npr.executionRequests then
    throw (.invalidBlock "Invalid block hash")
  if !is_valid_versioned_hashes npr then
    throw (.invalidBlock "Invalid versioned hashes")
  let block ← _payload_block payload npr.parentBeaconBlockRoot npr.executionRequests
  -- execute_block pre-execution frame
  if (encS (blockToRlpItem block)).length > MAX_RLP_BLOCK_SIZE then
    throw (.invalidBlock "Block rlp size exceeds MAX_RLP_BLOCK_SIZE")
  if input.transactionPublicKeys.length ≠ block.transactions.length then
    throw (.invalidBlock "Transaction public key count mismatch")
  validate_header input.chainContext.parentHeader block.header
  if !block.ommers.isEmpty then throw (.invalidBlock "ommers not empty")
  -- Root-anchored witness authentication (obligation #7): the accepting
  -- path always decodes the state trie from the witness.
  let _ ← decode_witness_to_mpt input.preState.nodeDb input.preState.stateRoot
  -- Static per-transaction checks (the execution-independent prefix of
  -- process_transaction/check_transaction; see the section above).
  staticTransactionChecks input.chainContext.chainId block.header
    input.preState block.transactions input.transactionPublicKeys
  -- apply_body + post-execution root checks: Stack C (s1d19.5).
  pure ()

/-! ## Sanity checks -/

-- compute_requests_hash: empty list = sha256("") vector; a two-blob
-- sample matches the Python spec.
#guard bytesBEtoNat (compute_requests_hash [])
  == 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
#guard bytesBEtoNat (compute_requests_hash
    [0x00 :: List.replicate 192 0x11, 0x01 :: List.replicate 76 0x22])
  == 0xb4930207a285f011d2c070d9e18d2691eac3054b5c2bed5cbe2690b175e1d694

-- encode_execution_requests: empty container → no blobs; a single
-- withdrawal request gets the 0x01 type byte and 76-byte body.
#guard encode_execution_requests {
  deposits := [], withdrawals := [], consolidations := [], builderDeposits := [], builderExits := []
} == []
#guard
  let w : WithdrawalRequest :=
    { sourceAddress := List.replicate 20 0xAA,
      validatorPubkey := List.replicate 48 0xBB, amount := 5 }
  encode_execution_requests {
    deposits := [], withdrawals := [w], consolidations := [], builderDeposits := [], builderExits := [] }
    == [0x01 :: (List.replicate 20 0xAA ++ List.replicate 48 0xBB
          ++ [0x05, 0, 0, 0, 0, 0, 0, 0])]

#guard
  let b : BuilderDepositRequest :=
    { pubkey := List.replicate 48 0x11,
      withdrawalCredentials := List.replicate 32 0x22,
      amount := 0x0102030405060708,
      signature := List.replicate 96 0x33 }
  encode_execution_requests {
    deposits := [], withdrawals := [], consolidations := [], builderDeposits := [b], builderExits := [] }
    == [0x03 :: (List.replicate 48 0x11 ++ List.replicate 32 0x22
      ++ [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]
      ++ List.replicate 96 0x33)]

#guard
  let b : BuilderExitRequest :=
    { sourceAddress := List.replicate 20 0x44, pubkey := List.replicate 48 0x55 }
  encode_execution_requests {
    deposits := [], withdrawals := [], consolidations := [], builderDeposits := [], builderExits := [b] }
    == [0x04 :: (List.replicate 20 0x44 ++ List.replicate 48 0x55)]

-- check_gas_limit boundaries.
-- max_adjustment_delta = 30000000/1024 = 29296: strict bounds both sides.
#guard check_gas_limit 30000000 30000000 == true
#guard check_gas_limit (30000000 + 29295) 30000000 == true
#guard check_gas_limit (30000000 + 29296) 30000000 == false
#guard check_gas_limit (30000000 - 29296) 30000000 == false
#guard check_gas_limit (30000000 - 29295) 30000000 == true
#guard check_gas_limit 4999 30000000 == false

-- calculate_base_fee_per_gas: at target → unchanged; full blocks → +12.5%.
#guard (calculate_base_fee_per_gas 30000000 30000000 15000000 1000000000).toOption
  == some 1000000000
#guard (calculate_base_fee_per_gas 30000000 30000000 30000000 1000000000).toOption
  == some 1125000000
#guard (calculate_base_fee_per_gas 30000000 30000000 0 1000000000).toOption
  == some 875000000

end EvmAsm.Stateless.SpecRef
