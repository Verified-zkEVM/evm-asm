/-
  EvmAsm.Stateless.SpecRef.Fork

  Port of the block-body execution of
  `execution-specs/src/ethereum/forks/amsterdam/fork.py`
  (`@tests-zkevm@v0.5.0`, `bd8c673`) — bead `evm-asm-s1d19.5`:

  * `fork.py`: `make_receipt`, `process_checked_system_transaction`,
    `process_unchecked_system_transaction`, `apply_body`,
    `process_general_purpose_requests`, `process_transaction`,
    `process_withdrawals` (functions of the same names) and the system
    addresses/constants
  * `bloom.py`: `add_to_bloom`, `logs_bloom` (functions of the same
    names)
  * `blocks.py`: `Receipt` (class `Receipt`), `encode_receipt`
    (function `encode_receipt`)
  * `utils/message.py`: `prepare_message` (function `prepare_message`)
  * `requests.py`: `parse_deposit_requests`, `extract_deposit_data`
    (functions of the same names) and the deposit-event constants
  * `fork.py`: `check_transaction` (function `check_transaction`) — the
    full version (the execution-independent prefix already lives in
    `SeamShell.lean`)

  The Python mutates `block_env.state` (the block tracker) and
  `block_output` in place; here `apply_body` threads them through
  `EvmM` (the machine's tracker parent is the block state) and returns
  the `BlockOutput`.  Receipts in the trie are stored ENCODED (the
  Python stores `Bytes | Receipt`; a legacy receipt object RLP-encodes
  to the same bytes at `root(trie)` time, so storing the encoding is
  observationally equal — `decode_receipt` in `parse_deposit_requests`
  is bypassed by keeping decoded receipts alongside).
-/

import EvmAsm.Stateless.SpecRef.Interpreter

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP (RLPItem)

private def encF (i : RLPItem) : Bytes := EvmAsm.EL.RLP.encode i
private def scalarF (n : Nat) : RLPItem := .bytes (EvmAsm.EL.RLP.Nat.toBytesBE n)

/-! ## `fork.py` constants -/

def BEACON_ROOTS_ADDRESS : Address :=
  natToBytesBE 20 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
def HISTORY_STORAGE_ADDRESS : Address :=
  natToBytesBE 20 0x0000F90827F1C53a10cb7A02335B175320002935
def WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS : Address :=
  natToBytesBE 20 0x00000961Ef480Eb55e80D19ad83579A64c007002
def CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS : Address :=
  natToBytesBE 20 0x0000BBdDc7CE488642fb579F8B00f3a590007251
def BUILDER_DEPOSIT_CONTRACT_ADDRESS : Address :=
  natToBytesBE 20 0x0000884d2AA32eAa155F59A2f24eFa73D9008282
def BUILDER_EXIT_CONTRACT_ADDRESS : Address :=
  natToBytesBE 20 0x000014574A74c805590AFF9499fc7A690f008282
def SYSTEM_TRANSACTION_GAS : Uint := 30000000
def SYSTEM_MAX_SSTORES_PER_CALL : Uint := 16
def GWEI_TO_WEI : U256 := 10^9

/-! ## `requests.py` deposit parsing -/

def DEPOSIT_CONTRACT_ADDRESS : Address :=
  natToBytesBE 20 0x00000000219ab540356cbb839cbe05303d7705fa
def DEPOSIT_EVENT_SIGNATURE_HASH : Bytes :=
  natToBytesBE 32 0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5

/-- `extract_deposit_data(data)`: strip the ABI framing; any deviation
    is `InvalidBlock`. -/
def extract_deposit_data (data : Bytes) : Except SpecError Bytes := do
  let word := fun (off : Nat) => bytesBEtoNat ((data.drop off).take 32)
  let field := fun (off size : Nat) => (data.drop (off + 32)).take size
  if data.length ≠ 576 then throw (.invalidBlock "Invalid deposit event data length")
  if word 0 ≠ 160 then throw (.invalidBlock "Invalid pubkey offset in deposit log")
  if word 32 ≠ 256 then throw (.invalidBlock "Invalid withdrawal credentials offset in deposit log")
  if word 64 ≠ 320 then throw (.invalidBlock "Invalid amount offset in deposit log")
  if word 96 ≠ 384 then throw (.invalidBlock "Invalid signature offset in deposit log")
  if word 128 ≠ 512 then throw (.invalidBlock "Invalid index offset in deposit log")
  if word 160 ≠ 48 then throw (.invalidBlock "Invalid pubkey size in deposit log")
  if word 256 ≠ 32 then throw (.invalidBlock "Invalid withdrawal credentials size in deposit log")
  if word 320 ≠ 8 then throw (.invalidBlock "Invalid amount size in deposit log")
  if word 384 ≠ 96 then throw (.invalidBlock "Invalid signature size in deposit log")
  if word 512 ≠ 8 then throw (.invalidBlock "Invalid index size in deposit log")
  pure (field 160 48 ++ field 256 32 ++ field 320 8 ++ field 384 96 ++ field 512 8)

/-! ## `bloom.py` -/

/-- `add_to_bloom(bloom, bloom_entry)`: set 3 bits from the first three
    16-bit words of `keccak256(entry)` (11 LSBs each). -/
def add_to_bloom (bloom : Bytes) (bloom_entry : Bytes) : Bytes :=
  let hashed := keccak256 bloom_entry
  [0, 2, 4].foldl (fun bloom idx =>
    let bit_to_set := bytesBEtoNat ((hashed.drop idx).take 2) &&& 0x07FF
    let bit_index := 0x07FF - bit_to_set
    let byte_index := bit_index / 8
    let bit_value := 1 <<< (7 - bit_index % 8)
    bloom.set byte_index
      (BitVec.ofNat 8 ((bloom.getD byte_index 0).toNat ||| bit_value))) bloom

/-- `logs_bloom(logs)`. -/
def logs_bloom (logs : List Log) : Bloom :=
  logs.foldl (fun bloom log =>
    log.topics.foldl add_to_bloom (add_to_bloom bloom log.address))
    (List.replicate 256 0x00)

/-! ## `Receipt` / `encode_receipt` (`blocks.py`) -/

/-- `Receipt` (class `Receipt`). -/
structure Receipt where
  succeeded : Bool
  cumulativeGasUsed : Uint
  bloom : Bloom
  logs : List Log
  deriving Repr

private def logToRlpItem (l : Log) : RLPItem :=
  .list [.bytes l.address, .list (l.topics.map .bytes), .bytes l.data]

/-- `rlp.encode(receipt)`'s item. -/
def receiptToRlpItem (r : Receipt) : RLPItem :=
  .list [.bytes (if r.succeeded then [0x01] else []),
         scalarF r.cumulativeGasUsed, .bytes r.bloom,
         .list (r.logs.map logToRlpItem)]

/-- `encode_receipt(tx, receipt)`: legacy = the RLP itself (the Python
    stores the object; it encodes identically at trie-root time), typed
    forms get the type byte. -/
def encode_receipt (tx : Transaction) (r : Receipt) : Bytes :=
  match tx with
  | .legacy _ => encF (receiptToRlpItem r)
  | .accessList _ => 0x01 :: encF (receiptToRlpItem r)
  | .feeMarket _ => 0x02 :: encF (receiptToRlpItem r)
  | .blob _ => 0x03 :: encF (receiptToRlpItem r)
  | .setCode _ => 0x04 :: encF (receiptToRlpItem r)

/-- `make_receipt(tx, error, cumulative_gas_used, logs)`. -/
def make_receipt (tx : Transaction) (error : Option EvmError)
    (cumulative_gas_used : Uint) (logs : List Log) : Receipt × Bytes :=
  let receipt : Receipt :=
    { succeeded := error.isNone
      cumulativeGasUsed := cumulative_gas_used
      bloom := logs_bloom logs
      logs := logs }
  (receipt, encode_receipt tx receipt)

/-! ## `prepare_message` (`utils/message.py`) -/

/-- The 20 precompile addresses (`PRE_COMPILED_CONTRACTS.keys()`),
    warmed by every transaction. -/
def precompileAddresses (pre : PrecompileMap) : List Address := pre.map (·.1)

/-- `prepare_message(block_env, tx_env, tx)`. -/
def prepare_message (pre : PrecompileMap) (blockEnv : BlockEnvironment)
    (txEnv : TransactionEnvironment) (tx : Transaction) : TxM Message := do
  let accessed₀ := setUnion (setAdd [] txEnv.origin) (precompileAddresses pre)
  let accessed₀ := setUnion accessed₀ txEnv.accessListAddresses
  let (current_target, msg_data, code, code_address) ←
    match tx.to with
    | none => do
        let nonce := (← getAccount txEnv.origin).nonce
        let target := compute_contract_address txEnv.origin (nonce - 1)
        pure (target, ([] : Bytes), tx.data, (none : Option Address))
    | some to => do
        let code_hash := (← getAccount to).codeHash
        let code ← getCode code_hash to
        pure (to, tx.data, code, some to)
  pure { blockEnv := blockEnv
         txEnv := txEnv
         caller := txEnv.origin
         target := tx.to
         gas := txEnv.gas
         stateGasReservoir := txEnv.stateGasReservoir
         value := tx.value
         data := msg_data
         code := code
         depth := 0
         currentTarget := current_target
         codeAddress := code_address
         shouldTransferValue := true
         isStatic := false
         accessedAddresses := setAdd accessed₀ current_target
         accessedStorageKeys := txEnv.accessListStorageKeys
         disablePrecompiles := false }

/-! ## `check_transaction` (`fork.py`, function `check_transaction`) —
the full, execution-aware version.  The pure prefix mirrors
`SeamShell.staticCheckTransaction`; the state checks read through the
transaction tracker. -/

def check_transaction (blockEnv : BlockEnvironment) (blockOutput : BlockOutput)
    (tx : Transaction) (sender : Address) :
    EvmM (Uint × List VersionedHash × U64) := do
  let regular_gas_available := blockEnv.blockGasLimit - blockOutput.blockGasUsed
  let state_gas_available := blockEnv.blockGasLimit - blockOutput.blockStateGasUsed
  let blob_gas_available := MAX_BLOB_GAS_PER_BLOCK - blockOutput.blobGasUsed
  if min TX_MAX_GAS_LIMIT tx.gas > regular_gas_available then
    EvmM.liftSpec (throw (.invalidBlock "regular gas used exceeds limit"))
  if tx.gas > state_gas_available then
    EvmM.liftSpec (throw (.invalidBlock "state gas used exceeds limit"))
  let tx_blob_gas_used := calculate_total_blob_gas tx
  if tx_blob_gas_used > blob_gas_available then
    EvmM.liftSpec (throw (.invalidBlock "blob gas limit exceeded"))
  let sender_account ← EvmM.liftTx (getAccount sender)
  let (effective_gas_price, max_gas_fee) ←
    match tx with
    | .feeMarket t => feeMarketPrice t.maxFeePerGas t.maxPriorityFeePerGas t.gas
    | .blob t => feeMarketPrice t.maxFeePerGas t.maxPriorityFeePerGas t.gas
    | .setCode t => feeMarketPrice t.maxFeePerGas t.maxPriorityFeePerGas t.gas
    | .legacy t => legacyPrice t.gasPrice t.gas
    | .accessList t => legacyPrice t.gasPrice t.gas
  let (max_gas_fee, blob_versioned_hashes) ←
    match tx with
    | .blob t => do
        if t.blobVersionedHashes.isEmpty then
          EvmM.liftSpec (throw (.invalidBlock "no blob data in transaction"))
        if t.blobVersionedHashes.length > BLOB_COUNT_LIMIT then
          EvmM.liftSpec (throw (.invalidBlock "blob count exceeded"))
        if t.blobVersionedHashes.any (fun h => h.take 1 != [VERSIONED_HASH_VERSION_KZG]) then
          EvmM.liftSpec (throw (.invalidBlock "invalid blob versioned hash"))
        let blob_gas_price ← EvmM.liftSpec
          (calculate_blob_gas_price blockEnv.excessBlobGas)
        if t.maxFeePerBlobGas < blob_gas_price then
          EvmM.liftSpec (throw (.invalidBlock "insufficient max fee per blob gas"))
        pure (max_gas_fee + calculate_total_blob_gas tx * t.maxFeePerBlobGas,
              t.blobVersionedHashes)
    | _ => pure (max_gas_fee, [])
  -- to-creation for blob/set-code is unrepresentable (decode enforces
  -- a mandatory address); the empty-authorization check:
  if let .setCode t := tx then
    if t.authorizations.isEmpty then
      EvmM.liftSpec (throw (.invalidBlock "empty authorization list"))
  if sender_account.nonce > tx.nonce then
    EvmM.liftSpec (throw (.invalidBlock "nonce too low"))
  if sender_account.nonce < tx.nonce then
    EvmM.liftSpec (throw (.invalidBlock "nonce too high"))
  if sender_account.balance < max_gas_fee + tx.value then
    EvmM.liftSpec (throw (.invalidBlock "insufficient sender balance"))
  let sender_code ← EvmM.liftTx (getCode sender_account.codeHash sender)
  if sender_account.codeHash != EMPTY_CODE_HASH && !is_valid_delegation sender_code then
    EvmM.liftSpec (throw (.invalidBlock "not EOA"))
  pure (effective_gas_price, blob_versioned_hashes, tx_blob_gas_used)
where
  feeMarketPrice (maxFee maxPriority gas : Uint) : EvmM (Uint × Uint) := do
    if maxFee < maxPriority then
      EvmM.liftSpec (throw (.invalidBlock "priority fee greater than max fee"))
    if maxFee < blockEnv.baseFeePerGas then
      EvmM.liftSpec (throw (.invalidBlock "insufficient max fee per gas"))
    let priority := min maxPriority (maxFee - blockEnv.baseFeePerGas)
    pure (priority + blockEnv.baseFeePerGas, gas * maxFee)
  legacyPrice (gasPrice gas : Uint) : EvmM (Uint × Uint) := do
    if gasPrice < blockEnv.baseFeePerGas then
      EvmM.liftSpec (throw (.invalidBlock "gas price below base fee"))
    pure (gasPrice, gas * gasPrice)

/-! ## System transactions -/

/-- Run an action in a FRESH `TransactionState` over the current block
    state, returning the block-level tracker to the machine afterwards
    (the Python creates a throwaway/new `TransactionState(parent=…)`;
    the machine's tracker always holds the live one). -/
def withFreshTxState (m : EvmM α) : EvmM α := fun s => do
  let blockState := s.txState.parent
  match m { s with txState := { parent := blockState } } with
  | .error e => .error e
  | .ok (a, s') => .ok (a, s')

/-- `process_unchecked_system_transaction(block_env, target_address,
    data)`. -/
def process_unchecked_system_transaction (pre : PrecompileMap)
    (blockEnv : BlockEnvironment) (builder : BlockAccessListBuilder)
    (target_address : Address) (data : Bytes) :
    EvmM (MessageCallOutput × BlockAccessListBuilder) :=
  withFreshTxState (do
    let code ← extCodeOf target_address
    let txEnv : TransactionEnvironment :=
      { origin := VM_SYSTEM_ADDRESS
        recipient := some target_address
        value := 0
        gasPrice := blockEnv.baseFeePerGas
        gas := SYSTEM_TRANSACTION_GAS
        stateGasReservoir := StateGasCosts.STORAGE_SET * SYSTEM_MAX_SSTORES_PER_CALL
        accessListAddresses := []
        accessListStorageKeys := []
        blobVersionedHashes := []
        authorizations := []
        indexInBlock := none
        txHash := none
        intrinsicRegularGas := 0
        intrinsicStateGas := 0 }
    let msg : Message :=
      { blockEnv := blockEnv
        txEnv := txEnv
        caller := VM_SYSTEM_ADDRESS
        target := some target_address
        gas := SYSTEM_TRANSACTION_GAS
        stateGasReservoir := StateGasCosts.STORAGE_SET * SYSTEM_MAX_SSTORES_PER_CALL
        value := 0
        data := data
        code := code
        depth := 0
        currentTarget := target_address
        codeAddress := some target_address
        shouldTransferValue := false
        isStatic := false
        accessedAddresses := []
        accessedStorageKeys := []
        disablePrecompiles := false }
    let output ← process_message_call pre msg
    let builder ← EvmM.liftTx (incorporateTxIntoBlock builder)
    pure (output, builder))

/-- `process_checked_system_transaction(...)`: the code pre-check reads
    through a throwaway tracker (the same reads are re-performed and
    tracked by the unchecked call). -/
def process_checked_system_transaction (pre : PrecompileMap)
    (blockEnv : BlockEnvironment) (builder : BlockAccessListBuilder)
    (target_address : Address) (data : Bytes) :
    EvmM (MessageCallOutput × BlockAccessListBuilder) := do
  let code ← withFreshTxState (extCodeOf target_address)
  if code.isEmpty then
    EvmM.liftSpec (throw (.invalidBlock "System contract address does not contain code"))
  let (output, builder) ← process_unchecked_system_transaction pre blockEnv
    builder target_address data
  if output.error.isSome then
    EvmM.liftSpec (throw (.invalidBlock "System contract call failed"))
  pure (output, builder)

/-! ## `process_transaction` (`fork.py`, function `process_transaction`) -/

def process_transaction (pre : PrecompileMap) (blockEnv : BlockEnvironment)
    (blockOutput : BlockOutput) (builder : BlockAccessListBuilder)
    (tx : Transaction) (index : Nat) :
    EvmM (BlockOutput × BlockAccessListBuilder) :=
  withFreshTxState (do
    let builder := { builder with blockAccessIndex := index + 1 }
    let mut blockOutput := blockOutput
    let txTrie := dictSet blockOutput.transactionsTrie (encF (scalarF index))
      (encode_transaction tx)
    blockOutput := { blockOutput with transactionsTrie := txTrie }
    -- v0.6.0 (EIP-155): explicit chain-id rejection (`WrongChainIdError`)
    -- before sender recovery — independent of the supplied public key.
    let tx_chain_id ← EvmM.liftSpec (chain_id tx)
    if let some cid := tx_chain_id then
      if cid ≠ blockEnv.chainId then
        EvmM.liftSpec (throw (.invalidTransaction
          s!"expected chain_id `{blockEnv.chainId}` but got `{cid}`"))
    let sender ←
      match blockEnv.transactionPublicKeys with
      | none => EvmM.liftSpec (recover_sender tx)
      | some keys => EvmM.liftSpec (recover_sender_from_public_key blockEnv.chainId tx
          (keys.getD index []))
    let intrinsic ← EvmM.liftSpec (validate_transaction tx sender)
    let intrinsic_gas := intrinsic.regular + intrinsic.state
    let (effective_gas_price, blob_versioned_hashes, tx_blob_gas_used) ←
      check_transaction blockEnv blockOutput tx sender
    let sender_account ← EvmM.liftTx (getAccount sender)
    let blob_gas_fee ←
      match tx with
      | .blob _ => do
          let price ← EvmM.liftSpec (calculate_blob_gas_price blockEnv.excessBlobGas)
          pure (calculate_total_blob_gas tx * price)
      | _ => pure 0
    let effective_gas_fee := tx.gas * effective_gas_price
    let execution_gas := tx.gas - intrinsic_gas
    let regular_gas_budget := TX_MAX_GAS_LIMIT - intrinsic.regular
    let gas := min regular_gas_budget execution_gas
    let state_gas_reservoir := execution_gas - gas
    EvmM.liftTx (incrementNonce sender)
    let sender_balance_after_gas_fee :=
      sender_account.balance - effective_gas_fee - blob_gas_fee
    EvmM.liftTx (setAccountBalance sender sender_balance_after_gas_fee)
    let access_list_addresses := setAdd [] blockEnv.coinbase
    let (access_list_addresses, access_list_storage_keys) :=
      match tx.accessList? with
      | none => (access_list_addresses, [])
      | some al => al.foldl (fun (addrs, keys) (access : Access) =>
          (setAdd addrs access.account,
           access.slots.foldl (fun ks slot => setAdd ks (access.account, slot)) keys))
          (access_list_addresses, [])
    let authorizations := match tx with
      | .setCode t => t.authorizations
      | _ => []
    let txEnv : TransactionEnvironment :=
      { origin := sender
        recipient := tx.to
        value := tx.value
        gasPrice := effective_gas_price
        gas := gas
        stateGasReservoir := state_gas_reservoir
        accessListAddresses := access_list_addresses
        accessListStorageKeys := access_list_storage_keys
        blobVersionedHashes := blob_versioned_hashes
        authorizations := authorizations
        indexInBlock := some index
        txHash := some (get_transaction_hash (encode_transaction tx))
        intrinsicRegularGas := intrinsic.regular
        intrinsicStateGas := intrinsic.state }
    let message ← EvmM.liftTx (prepare_message pre blockEnv txEnv tx)
    let mut tx_output ← process_message_call pre message
    if tx.to == none && (tx_output.error.isSome || tx_output.createdTargetAlive) then
      tx_output := { tx_output with
        stateGasLeft := tx_output.stateGasLeft + StateGasCosts.NEW_ACCOUNT
        stateRefund := tx_output.stateRefund + StateGasCosts.NEW_ACCOUNT }
    let tx_gas_used_before_refund := tx.gas - tx_output.gasLeft - tx_output.stateGasLeft
    let tx_gas_refund := min (tx_gas_used_before_refund / 5) tx_output.refundCounter
    let tx_gas_used_after_refund := tx_gas_used_before_refund - tx_gas_refund
    let tx_gas_used := max tx_gas_used_after_refund intrinsic.calldataFloor
    let tx_gas_left := tx.gas - tx_gas_used
    let gas_refund_amount := tx_gas_left * effective_gas_price
    let priority_fee_per_gas := effective_gas_price - blockEnv.baseFeePerGas
    let transaction_fee := tx_gas_used * priority_fee_per_gas
    EvmM.liftTx (createEther sender gas_refund_amount)
    EvmM.liftTx (createEther blockEnv.coinbase transaction_fee)
    let tx_state_gas : Int := (txEnv.intrinsicStateGas : Int)
      + tx_output.stateGasUsed - (tx_output.stateRefund : Int)
    let tx_state_gas_nat := (max 0 tx_state_gas).toNat
    let tx_regular_gas := tx_gas_used_before_refund - tx_state_gas_nat
    blockOutput := { blockOutput with
      blockGasUsed := blockOutput.blockGasUsed + tx_regular_gas
      blockStateGasUsed := blockOutput.blockStateGasUsed + tx_state_gas_nat
      blobGasUsed := blockOutput.blobGasUsed + tx_blob_gas_used
      cumulativeGasUsed := blockOutput.cumulativeGasUsed + tx_gas_used }
    let (receipt, encoded_receipt) := make_receipt tx tx_output.error
      blockOutput.cumulativeGasUsed tx_output.logs
    let receipt_key := encF (scalarF index)
    blockOutput := { blockOutput with
      receiptKeys := blockOutput.receiptKeys ++ [receipt_key]
      receiptsTrie := dictSet blockOutput.receiptsTrie receipt_key encoded_receipt
      blockLogs := blockOutput.blockLogs ++ tx_output.logs
      decodedReceiptLogs := blockOutput.decodedReceiptLogs ++ [receipt.logs] }
    for address in tx_output.accountsToDelete do
      EvmM.liftTx (clearAccountPreservingBalance address)
    let builder ← EvmM.liftTx (incorporateTxIntoBlock builder)
    pure (blockOutput, builder))

/-! ## `process_withdrawals` / `parse_deposit_requests` -/

def process_withdrawals (blockOutput : BlockOutput)
    (builder : BlockAccessListBuilder) (withdrawals : List Withdrawal) :
    EvmM (BlockOutput × BlockAccessListBuilder) :=
  withFreshTxState (do
    let mut blockOutput := blockOutput
    let mut i := 0
    for wd in withdrawals do
      let wdTrie := dictSet blockOutput.withdrawalsTrie (encF (scalarF i))
        (encF (withdrawalToRlpItem wd))
      blockOutput := { blockOutput with withdrawalsTrie := wdTrie }
      EvmM.liftTx (createEther wd.address (wd.amount * GWEI_TO_WEI))
      i := i + 1
    let builder ← EvmM.liftTx (incorporateTxIntoBlock builder)
    pure (blockOutput, builder))

/-- `parse_deposit_requests(block_output)` over the kept decoded
    receipts (see the header note). -/
def parse_deposit_requests (blockOutput : BlockOutput) :
    Except SpecError Bytes := do
  let mut deposit_requests : Bytes := []
  for receipt_logs in blockOutput.decodedReceiptLogs do
    for log in receipt_logs do
      if log.address == DEPOSIT_CONTRACT_ADDRESS then
        if log.topics.headD [] == DEPOSIT_EVENT_SIGNATURE_HASH then
          deposit_requests := deposit_requests ++ (← extract_deposit_data log.data)
  pure deposit_requests

/-! ## `process_general_purpose_requests` / `apply_body` -/

def process_general_purpose_requests (pre : PrecompileMap)
    (blockEnv : BlockEnvironment) (blockOutput : BlockOutput)
    (builder : BlockAccessListBuilder) :
    EvmM (BlockOutput × BlockAccessListBuilder) := do
  let deposit_requests ← EvmM.liftSpec (parse_deposit_requests blockOutput)
  let mut requests := blockOutput.requests
  if deposit_requests.length > 0 then
    requests := requests ++ [0x00 :: deposit_requests]
  let (wd_out, builder) ← process_checked_system_transaction pre blockEnv builder
    WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS []
  if wd_out.returnData.length > 0 then
    requests := requests ++ [0x01 :: wd_out.returnData]
  let (cons_out, builder) ← process_checked_system_transaction pre blockEnv builder
    CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS []
  if cons_out.returnData.length > 0 then
    requests := requests ++ [0x02 :: cons_out.returnData]
  let (bdep_out, builder) ← process_checked_system_transaction pre blockEnv builder
    BUILDER_DEPOSIT_CONTRACT_ADDRESS []
  if bdep_out.returnData.length > 0 then
    requests := requests ++ [0x03 :: bdep_out.returnData]
  let (bexit_out, builder) ← process_checked_system_transaction pre blockEnv builder
    BUILDER_EXIT_CONTRACT_ADDRESS []
  if bexit_out.returnData.length > 0 then
    requests := requests ++ [0x04 :: bexit_out.returnData]
  pure ({ blockOutput with requests := requests }, builder)

/-- `apply_body(block_env, transactions, withdrawals)`. -/
def apply_body (pre : PrecompileMap) (blockEnv : BlockEnvironment)
    (transactions : List Bytes) (withdrawals : List Withdrawal) :
    EvmM (BlockOutput × BlockAccessListBuilder) := do
  let mut blockOutput : BlockOutput := {}
  let mut builder : BlockAccessListBuilder := {}
  let (_, builder') ← process_unchecked_system_transaction pre blockEnv builder
    BEACON_ROOTS_ADDRESS blockEnv.parentBeaconBlockRoot
  builder := builder'
  let (_, builder') ← process_unchecked_system_transaction pre blockEnv builder
    HISTORY_STORAGE_ADDRESS (blockEnv.blockHashes.getLast?.getD (List.replicate 32 0))
  builder := builder'
  EvmM.liftTx (trackAncestorAccess 1)
  let mut i := 0
  for encoded_tx in transactions do
    let tx ← EvmM.liftSpec (decode_transaction encoded_tx)
    let (out', builder') ← process_transaction pre blockEnv blockOutput builder tx i
    blockOutput := out'
    builder := builder'
    i := i + 1
  builder := { builder with blockAccessIndex := transactions.length + 1 }
  let (out', builder') ← process_withdrawals blockOutput builder withdrawals
  blockOutput := out'
  builder := builder'
  let (out', builder') ← process_general_purpose_requests pre blockEnv
    blockOutput builder
  blockOutput := out'
  builder := builder'
  let blockState ← EvmM.getBlockState
  let bal := build_block_access_list builder blockState
  blockOutput := { blockOutput with blockAccessList := bal }
  EvmM.liftSpec (validate_block_access_list_gas_limit bal blockEnv.blockGasLimit)
  pure (blockOutput, builder)

end EvmAsm.Stateless.SpecRef
