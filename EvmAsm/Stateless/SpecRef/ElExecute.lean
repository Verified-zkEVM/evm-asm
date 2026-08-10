/-
  EvmAsm.Stateless.SpecRef.ElExecute

  The execution-seam interior (`elExecute`, docs/4ch8f-top-spec.md §4;
  bead `evm-asm-s1d19.5`): the completion of
  `execution-specs/src/ethereum/forks/amsterdam/fork.py`
  function `execute_block` — the `apply_body` call and the eight
  post-execution checks — composed with the `execute_new_payload_request`
  pre-checks already in `SeamShell.lean` (function
  `execute_new_payload_request` of `execution_engine/new_payload.py`)
  into a full `ExecutionSeam`.

  `elExecuteWith` is parameterized by the `PrecompileMap`; the
  precompile stage supplies the 20 implementations and flips the
  default seam from `executeSeamShell` to the full `elExecute`.

  The post-state root uses `compute_state_root_and_trie_changes`
  (`WitnessStateRoot.lean`) with the `_storage_root_cache`
  reconstructed from `BlockState.preStateReads` (see
  `StateTracker.lean`); the tx/receipt/withdrawal trie roots are the
  unsecured `root(trie)` over the collected assoc data
  (`build_mpt`/`mpt_root`).
-/

import EvmAsm.Stateless.SpecRef.Fork
import EvmAsm.Stateless.SpecRef.WitnessStateRoot

namespace EvmAsm.Stateless.SpecRef

/-- The unsecured `root(trie)` over collected key→value assoc data
    (`Trie(secured=False, default=None)`). -/
private def collectedTrieRoot (data : List (Bytes × Bytes)) :
    Except SpecError Root := do
  mpt_root (← build_mpt (data.map (fun (k, v) => (k, MptValue.bytes v))) false none)

/-- A placeholder frame for machine initialization; every real frame
    is swapped in by `process_message` before any instruction runs. -/
private def dummyEvm (blockEnv : BlockEnvironment) : Evm :=
  let txEnv : TransactionEnvironment :=
    { origin := NULL_ADDRESS, recipient := none, value := 0, gasPrice := 0,
      gas := 0, stateGasReservoir := 0, accessListAddresses := [],
      accessListStorageKeys := [], blobVersionedHashes := [],
      authorizations := [], indexInBlock := none, txHash := none,
      intrinsicRegularGas := 0, intrinsicStateGas := 0 }
  let msg : Message :=
    { blockEnv := blockEnv, txEnv := txEnv, caller := NULL_ADDRESS,
      target := none, currentTarget := NULL_ADDRESS, gas := 0,
      stateGasReservoir := 0, value := 0, data := [], codeAddress := none,
      code := [], depth := 0, shouldTransferValue := false, isStatic := false,
      accessedAddresses := [], accessedStorageKeys := [],
      disablePrecompiles := false }
  { code := [], gasLeft := 0, stateGasLeft := 0, validJumpDestinations := [],
    message := msg, accessedAddresses := [], accessedStorageKeys := [] }

/-- The `execute_block` interior below the pre-execution frame
    (`fork.py`, function `execute_block`): `apply_body`, the diff
    extraction, the post-state root, and the eight header checks. -/
def execute_block_interior (pre : PrecompileMap) (ws : WitnessPreState)
    (chainContext : ChainContext) (block : Block)
    (transaction_public_keys : List Bytes) : Except SpecError Unit := do
  let blockEnv : BlockEnvironment :=
    { chainId := chainContext.chainId
      blockGasLimit := block.header.gasLimit
      blockHashes := chainContext.blockHashes
      coinbase := block.header.coinbase
      number := block.header.number
      baseFeePerGas := block.header.baseFeePerGas
      time := block.header.timestamp
      prevRandao := block.header.prevRandao
      excessBlobGas := block.header.excessBlobGas
      parentBeaconBlockRoot := block.header.parentBeaconBlockRoot
      slotNumber := block.header.slotNumber
      transactionPublicKeys := some transaction_public_keys }
  let machine₀ : Machine :=
    { evm := dummyEvm blockEnv
      txState := { parent := { preState := ws } } }
  let result := (apply_body pre blockEnv block.transactions block.withdrawals).run
    |>.run machine₀
  let (blockOutput, machine) ←
    match ← result with
    -- an EvmError escaping apply_body is a Python exception escaping
    -- execute_block → rejection
    | (.error _, _) => throw (.executionRejected "unhandled EVM error in apply_body")
    | (.ok (out, _builder), machine) => pure (out, machine)
  let block_state := machine.txState.parent
  let diff := extract_block_diff block_state
  let cache₀ ← cacheFromReads ws block_state.preStateReads
  let block_state_root ← compute_state_root_and_trie_changes ws cache₀
    diff.accountChanges diff.storageChanges
  let transactions_root ← collectedTrieRoot blockOutput.transactionsTrie
  let receipt_root ← collectedTrieRoot blockOutput.receiptsTrie
  let block_logs_bloom := logs_bloom blockOutput.blockLogs
  let withdrawals_root ← collectedTrieRoot blockOutput.withdrawalsTrie
  let requests_hash := compute_requests_hash blockOutput.requests
  let computed_bal_hash := hash_block_access_list blockOutput.blockAccessList
  let block_gas_used := max blockOutput.blockGasUsed blockOutput.blockStateGasUsed
  if block_gas_used ≠ block.header.gasUsed then
    throw (.invalidBlock "gas used mismatch")
  if transactions_root ≠ block.header.transactionsRoot then
    throw (.invalidBlock "transactions root mismatch")
  if block_state_root ≠ block.header.stateRoot then
    throw (.invalidBlock "state root mismatch")
  if receipt_root ≠ block.header.receiptRoot then
    throw (.invalidBlock "receipt root mismatch")
  if block_logs_bloom ≠ block.header.bloom then
    throw (.invalidBlock "bloom mismatch")
  if withdrawals_root ≠ block.header.withdrawalsRoot then
    throw (.invalidBlock "withdrawals root mismatch")
  if blockOutput.blobGasUsed ≠ block.header.blobGasUsed then
    throw (.invalidBlock "blob gas used mismatch")
  if requests_hash ≠ block.header.requestsHash then
    throw (.invalidBlock "requests hash mismatch")
  if computed_bal_hash ≠ block.header.blockAccessListHash then
    throw (.invalidBlock "Invalid block access list hash")

/-- Shared `execute_new_payload_request` pre-checks + `_payload_block` used by
    both the production seam and the gas-dimension diagnostic. -/
private def elPrepareBlock (input : ExecutionSeamInput) : Except SpecError Block := do
  let npr := input.newPayloadRequest
  let payload := npr.executionPayload
  if payload.transactions.any (·.isEmpty) then
    throw (.invalidBlock "Empty transaction in payload")
  if !is_valid_block_hash payload npr.parentBeaconBlockRoot npr.executionRequests then
    throw (.invalidBlock "Invalid block hash")
  if !is_valid_versioned_hashes npr then
    throw (.invalidBlock "Invalid versioned hashes")
  let block ← _payload_block payload npr.parentBeaconBlockRoot npr.executionRequests
  if (EvmAsm.EL.RLP.encode (blockToRlpItem block)).length > MAX_RLP_BLOCK_SIZE then
    throw (.invalidBlock "Block rlp size exceeds MAX_RLP_BLOCK_SIZE")
  if input.transactionPublicKeys.length ≠ block.transactions.length then
    throw (.invalidBlock "Transaction public key count mismatch")
  validate_header input.chainContext.parentHeader block.header
  if !block.ommers.isEmpty then throw (.invalidBlock "ommers not empty")
  pure block

/-- The full seam: `execute_new_payload_request` (pre-checks +
    `_payload_block`) and the complete `execute_block`.  This IS
    `elExecute` once a complete `PrecompileMap` is supplied. -/
def elExecuteWith (pre : PrecompileMap) : ExecutionSeam := fun input => do
  let block ← elPrepareBlock input
  execute_block_interior pre input.preState input.chainContext block
    input.transactionPublicKeys

/-- Diagnostic: return `BlockOutput.blockGasUsed` × `blockStateGasUsed` from the
    same `apply_body` call `execute_block_interior` uses for the EIP-8037
    `max` comparison (`ElExecute.lean` gas-used check). These are the oracle's
    accumulator fields, not a side recomputation of gas arithmetic.

    Stops after `apply_body` (skips post-body root/bloom checks) so the
    export stays cheap; the gas fields are fully accumulated before those
    checks. Tooling-only — not part of the production seam result. -/
def apply_body_block_gas_dims (pre : PrecompileMap) (ws : WitnessPreState)
    (chainContext : ChainContext) (block : Block)
    (transaction_public_keys : List Bytes) : Except SpecError (Uint × Uint) := do
  let blockEnv : BlockEnvironment :=
    { chainId := chainContext.chainId
      blockGasLimit := block.header.gasLimit
      blockHashes := chainContext.blockHashes
      coinbase := block.header.coinbase
      number := block.header.number
      baseFeePerGas := block.header.baseFeePerGas
      time := block.header.timestamp
      prevRandao := block.header.prevRandao
      excessBlobGas := block.header.excessBlobGas
      parentBeaconBlockRoot := block.header.parentBeaconBlockRoot
      slotNumber := block.header.slotNumber
      transactionPublicKeys := some transaction_public_keys }
  let machine₀ : Machine :=
    { evm := dummyEvm blockEnv
      txState := { parent := { preState := ws } } }
  let result := (apply_body pre blockEnv block.transactions block.withdrawals).run
    |>.run machine₀
  match ← result with
  | (.error _, _) => throw (.executionRejected "unhandled EVM error in apply_body")
  | (.ok (out, _), _) => pure (out.blockGasUsed, out.blockStateGasUsed)

/-- Full-seam diagnostic wrapper: same pre-checks as `elExecuteWith`, then
    `apply_body_block_gas_dims`. -/
def elDiagnoseGasDimsWith (pre : PrecompileMap) (input : ExecutionSeamInput) :
    Except SpecError (Uint × Uint) := do
  let block ← elPrepareBlock input
  apply_body_block_gas_dims pre input.preState input.chainContext block
    input.transactionPublicKeys

end EvmAsm.Stateless.SpecRef
