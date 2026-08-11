/-
  EvmAsm.Stateless.SpecRef.Types

  Domain types for the stateless-guest reference port. These mirror the
  Python `@dataclass`/`StrEnum` types in
  `execution-specs/src/ethereum/forks/amsterdam/stateless.py` (and the
  `execution_engine.types` / `blocks` / `state` types it references),
  at tag `tests-zkevm@v0.4.0`.

  Modeling choices (see docs/4ch8f-specref-port.md):
  * `Bytes = List (BitVec 8)` (see `Crypto.lean`), `#eval`/`decide`-friendly.
  * Ethereum numeric widths (`U64`, `U256`, `Uint`) are unbounded `Nat`;
    width enforcement lives in the SSZ codec (`Ssz.lean`), matching how the
    Python `remerkleable` types apply width only at (de)serialization.
  * Fixed-width byte fields (`Hash32`, `Root`, `Address`, `Bloom`,
    `VersionedHash`) are raw `Bytes`; their length is validated at the
    boundary that constructs the fixed field, rather than at the type level.
-/

import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Stateless.SpecRef

/-! ## Numeric and byte-field aliases (all mirror Ethereum types) -/

abbrev U64 := Nat
abbrev U256 := Nat
abbrev Uint := Nat
abbrev Hash32 := Bytes
abbrev Root := Bytes
abbrev Address := Bytes
abbrev Bloom := Bytes
abbrev VersionedHash := Bytes
abbrev Bytes32 := Bytes

/-! ## Distinct failure reasons

`verify_stateless_new_payload` catches every exception and folds it into
`successful_validation=False`, but the porting rules require the interior
functions to surface the *distinct* reasons rather than collapse them. -/

/-- Every distinct spec-level failure the port can raise, tagged by the
    Python exception/`raise` site it corresponds to. -/
inductive SpecError where
  /-- `deserialize_stateless_input`: input shorter than the schema id. -/
  | missingSchemaId
  /-- `deserialize_stateless_input`: schema id ≠ `STATELESS_INPUT_SCHEMA_ID`. -/
  | unsupportedSchemaId (found : Nat)
  /-- `SszStatelessInput.decode_bytes` / `encode_bytes` failure. -/
  | sszError (why : String)
  /-- `stateless_input_to_ssz`: a transaction public key ≠ 65 bytes. -/
  | publicKeyWrongLength (len : Nat)
  /-- `validate_headers`: more than 256 witness headers. -/
  | tooManyHeaders (count : Nat)
  /-- `_decode_header`: RLP decode failed for both current and previous fork. -/
  | headerDecodeError
  /-- `validate_headers`: `parent_hash` chain is not contiguous. -/
  | headersNotContiguous
  /-- `_is_activation_active`: activation sets neither block_number nor timestamp
      (`InvalidForkActivationError`). -/
  | forkActivationMissing
  /-- `validate_chain_config`: active fork not active for the payload
      (`InactiveForkConfigError`). -/
  | inactiveForkConfig
  /-- `_decode_account_from_leaf`: leaf RLP is not a 4-item list. -/
  | accountLeafMalformed
  /-- `_decode_account_from_leaf`: a non-empty fixed-width account field is
      not exactly 32 bytes (`FixedBytes` construction in the reference). -/
  | accountFieldWrongLength (field : String) (len : Nat)
  /-- `_trie_lookup`: hit an unresolved `HashedNode`. -/
  | unresolvedHashedNode
  /-- `decode_witness_to_mpt`: `node_db[root_hash]` raised `KeyError` — the
      witness does not contain the trie's root node. -/
  | witnessRootMissing
  /-- `fork.py` / `execution_engine/new_payload.py`: any `InvalidBlock`
      raised by the pre-checks or the `execute_block` frame. -/
  | invalidBlock (why : String)
  /-- Modeling-only: contact with a precompile whose implementation is
      not yet ported (`Precompiles.lean`).  The hybrid seam catches
      exactly this and falls back to the sound-for-accepts shell. -/
  | unimplementedPrecompile (name : String)
  /-- `state_tracker.py`: an `AssertionError` on the state layer
      (`set_storage` on a missing account, `move_ether` underflow). -/
  | stateError (why : String)
  /-- `transactions.py` `validate_transaction`:
      `InsufficientTransactionGasError` / `NonceOverflowError` /
      `InitCodeTooLargeError`. -/
  | invalidTransaction (why : String)
  /-- `transactions.py` signature validation / recovery:
      `InvalidSignatureError`. -/
  | invalidSignature (why : String)
  /-- `transactions.py` `decode_transaction` / `rlp.decode_to`: any
      `DecodingError`, `TransactionTypeError`, or `IndexError` while
      decoding a transaction envelope. -/
  | txDecodeError (why : String)
  /-- `incremental_mpt.py` write side (`mpt_set`/`mpt_get`/`mpt_root`/
      `build_mpt` and helpers): any `AssertionError` raised on the
      insert/delete/encode/traverse path — e.g. touching an unresolved
      `HashedNode`, `_split_extension` collision, unencodable value. -/
  | mptWriteError (why : String)
  /-- `WitnessState.get_code`: `self._code_db[code_hash]` raised `KeyError` —
      the witness does not contain the bytecode for a non-empty code hash. -/
  | codeHashMissing
  /-- `WitnessState.get_storage`: `rlp.decode(leaf)` raised `DecodingError`
      on a storage-trie leaf value. -/
  | storageLeafMalformed
  /-- `_decode_witness_node` / `_resolve_child_ref` / `compact_to_nibbles`:
      any `AssertionError` / `IndexError` / RLP `DecodingError` raised while
      decoding a witness trie node (all folded into rejection by the
      `verify_stateless_new_payload` `try`). -/
  | witnessNodeMalformed (why : String)
  /-- Execution seam (`execute_new_payload_request`) rejected the payload. -/
  | executionRejected (why : String)
  deriving Repr, BEq, DecidableEq

/-! ## Protocol forks (`stateless.py:81` `ProtocolFork`) -/

/-- Stable execution-layer fork identifiers used by stateless schemas.
    v0.6.0 turns this into an `IntEnum` (`Frontier = 0x01` …
    `Amsterdam = 0x15`); the value no longer travels in the SSZ payload —
    its only wire use is the schema-id prefix
    (`STATELESS_INPUT_SCHEMA_FORK_INDEX`, `stateless_ssz.py:89`). -/
inductive ProtocolFork where
  | Frontier | Homestead | DAOFork | TangerineWhistle | SpuriousDragon
  | Byzantium | StPetersburg | Istanbul | MuirGlacier | Berlin | London
  | ArrowGlacier | GrayGlacier | Paris | Shanghai | Cancun | Prague | Osaka
  | BPO1 | BPO2 | Amsterdam
  deriving Repr, BEq, DecidableEq

/-- The `IntEnum` value of a fork (`stateless.py:86`–`106`): declaration
    index + 1, spelled out to keep each value visibly tied to the spec. -/
def ProtocolFork.value : ProtocolFork → Nat
  | .Frontier => 0x01 | .Homestead => 0x02 | .DAOFork => 0x03
  | .TangerineWhistle => 0x04 | .SpuriousDragon => 0x05 | .Byzantium => 0x06
  | .StPetersburg => 0x07 | .Istanbul => 0x08 | .MuirGlacier => 0x09
  | .Berlin => 0x0A | .London => 0x0B | .ArrowGlacier => 0x0C
  | .GrayGlacier => 0x0D | .Paris => 0x0E | .Shanghai => 0x0F
  | .Cancun => 0x10 | .Prague => 0x11 | .Osaka => 0x12
  | .BPO1 => 0x13 | .BPO2 => 0x14 | .Amsterdam => 0x15

/-! ## Chain-config dataclasses (`stateless.py:126`–`160`) -/

/-- `ForkActivation` (`stateless.py:130`). -/
structure ForkActivation where
  blockNumber : Option U64
  timestamp : Option U64
  deriving Repr, BEq, DecidableEq

/-- `ForkConfig` (`stateless.py:142`). v0.6.0 drops the `fork` and
    `blob_schedule` fields: fork identity is carried by the schema id
    and the blob schedule is compiled into the guest. -/
structure ForkConfig where
  activation : ForkActivation
  deriving Repr, BEq, DecidableEq

/-- `ChainConfig` (`stateless.py:153`). -/
structure ChainConfig where
  chainId : U64
  activeFork : ForkConfig
  deriving Repr, BEq, DecidableEq

/-! ## Payload / request dataclasses
    (`blocks.py`, `execution_engine/types.py`, `execution_engine/requests.py`) -/

/-- `Withdrawal` (`blocks.py:36`). -/
structure Withdrawal where
  index : U64
  validatorIndex : U64
  address : Address
  amount : U256
  deriving Repr, BEq, DecidableEq

/-- `ExecutionPayload` (`execution_engine/types.py:29`). -/
structure ExecutionPayload where
  parentHash : Hash32
  feeRecipient : Address
  stateRoot : Root
  receiptsRoot : Root
  logsBloom : Bloom
  prevRandao : Bytes
  blockNumber : Uint
  gasLimit : Uint
  gasUsed : Uint
  timestamp : U256
  extraData : Bytes
  baseFeePerGas : Uint
  blockHash : Hash32
  transactions : List Bytes
  withdrawals : List Withdrawal
  blobGasUsed : U64
  excessBlobGas : U64
  blockAccessList : Bytes
  slotNumber : U64
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `DepositRequest` (`execution_engine/requests.py:35`). -/
structure DepositRequest where
  pubkey : Bytes
  withdrawalCredentials : Bytes
  amount : U64
  signature : Bytes
  index : U64
  deriving Repr, BEq, DecidableEq

/-- `WithdrawalRequest` (`execution_engine/requests.py:47`). -/
structure WithdrawalRequest where
  sourceAddress : Address
  validatorPubkey : Bytes
  amount : U64
  deriving Repr, BEq, DecidableEq

/-- `ConsolidationRequest` (`execution_engine/requests.py:57`). -/
structure ConsolidationRequest where
  sourceAddress : Address
  sourcePubkey : Bytes
  targetPubkey : Bytes
  deriving Repr, BEq, DecidableEq

/-- `BuilderDepositRequest` (`execution_engine/requests.py:67`). -/
structure BuilderDepositRequest where
  pubkey : Bytes
  withdrawalCredentials : Bytes
  amount : U64
  signature : Bytes
  deriving Repr, BEq, DecidableEq

/-- `BuilderExitRequest` (`execution_engine/requests.py:78`). -/
structure BuilderExitRequest where
  sourceAddress : Address
  pubkey : Bytes
  deriving Repr, BEq, DecidableEq

/-- `ExecutionRequests` (`execution_engine/requests.py:67`). -/
structure ExecutionRequests where
  deposits : List DepositRequest
  withdrawals : List WithdrawalRequest
  consolidations : List ConsolidationRequest
  builderDeposits : List BuilderDepositRequest
  builderExits : List BuilderExitRequest
  deriving Repr, BEq, DecidableEq

/-- `NewPayloadRequest` (`execution_engine/types.py:63`). -/
structure NewPayloadRequest where
  executionPayload : ExecutionPayload
  versionedHashes : List VersionedHash
  parentBeaconBlockRoot : Root
  executionRequests : ExecutionRequests
  deriving Repr, BEq, DecidableEq

/-- `ExecutionWitness` (`stateless.py:32`). -/
structure ExecutionWitness where
  state : List Bytes
  codes : List Bytes
  headers : List Bytes
  deriving Repr, BEq, DecidableEq

/-- `StatelessInput` (`stateless.py:185`). -/
structure StatelessInput where
  newPayloadRequest : NewPayloadRequest
  witness : ExecutionWitness
  chainConfig : ChainConfig
  publicKeys : List Bytes
  deriving Repr, BEq, DecidableEq

/-- `StatelessValidationResult` (`stateless.py:216`). -/
structure StatelessValidationResult where
  newPayloadRequestRoot : Hash32
  successfulValidation : Bool
  chainConfig : ChainConfig
  deriving Repr, BEq, DecidableEq

/-! ## State-side types (`ethereum.state`, `witness_state.py`) -/

/-- `ethereum.state.Account` — the three fields stored on the account
    object (`storage_root` is returned separately by
    `_decode_account_from_leaf`). -/
structure Account where
  nonce : Uint
  balance : U256
  codeHash : Hash32
  deriving Repr, BEq, DecidableEq

/-- A decoded block header. The Python `_decode_header` returns
    `Header | PreviousForkHeader`; both share the leading fields, and
    `validate_headers`/`verify_stateless_new_payload` only read
    `parent_hash` and `state_root`. We collapse the union into one record
    carrying every decoded field plus a `fork` tag recording which decoder
    succeeded (amsterdam = 23 RLP fields, bpo5 = 21). Scalar fields are
    kept as `Nat`, byte/hash fields as `Bytes`. -/
structure Header where
  /-- `true` if decoded as the amsterdam `Header` (23 fields), `false` for
      the previous-fork (bpo5) `Header` (21 fields). -/
  isCurrentFork : Bool
  parentHash : Hash32
  ommersHash : Hash32
  coinbase : Address
  stateRoot : Root
  transactionsRoot : Root
  receiptRoot : Root
  bloom : Bloom
  difficulty : Uint
  number : Uint
  gasLimit : Uint
  gasUsed : Uint
  timestamp : U256
  extraData : Bytes
  prevRandao : Bytes
  nonce : Bytes
  baseFeePerGas : Uint
  withdrawalsRoot : Root
  blobGasUsed : U64
  excessBlobGas : U64
  parentBeaconBlockRoot : Root
  requestsHash : Hash32
  /-- amsterdam-only (`Bytes.empty` when `isCurrentFork = false`). -/
  blockAccessListHash : Hash32
  /-- amsterdam-only (`0` when `isCurrentFork = false`). -/
  slotNumber : U64
  deriving Repr, BEq, DecidableEq

end EvmAsm.Stateless.SpecRef
