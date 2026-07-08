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
    `VersionedHash`) are raw `Bytes`; their length is a codec invariant, not
    a type-level one (mirrors `bytes(x)` in the Python conversions).
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
  /-- `_ssz_to_protocol_fork`: enum value out of range. -/
  | unknownProtocolFork (value : Nat)
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
  /-- `validate_chain_config`: fork ≠ Amsterdam or blob schedule mismatch
      (`UnsupportedForkConfigError`). -/
  | unsupportedForkConfig (why : String)
  /-- `_decode_account_from_leaf`: leaf RLP is not a 4-item list. -/
  | accountLeafMalformed
  /-- `_trie_lookup`: hit an unresolved `HashedNode`. -/
  | unresolvedHashedNode
  /-- Execution seam (`execute_new_payload_request`) rejected the payload. -/
  | executionRejected (why : String)
  deriving Repr, BEq, DecidableEq

/-! ## Protocol forks (`stateless.py:83` `ProtocolFork`) -/

/-- Semantic execution-layer fork names understood by stateless inputs.
    Constructor order MUST match Python declaration order, because
    `_protocol_fork_to_ssz` uses `tuple(ProtocolFork).index(fork)`. -/
inductive ProtocolFork where
  | Frontier | Homestead | DAOFork | TangerineWhistle | SpuriousDragon
  | Byzantium | StPetersburg | Istanbul | MuirGlacier | Berlin | London
  | ArrowGlacier | GrayGlacier | Paris | Shanghai | Cancun | Prague | Osaka
  | BPO1 | BPO2 | Amsterdam
  deriving Repr, BEq, DecidableEq

/-- `tuple(ProtocolFork)` — the SSZ enum ordering (`stateless_ssz.py:249`). -/
def protocolForks : List ProtocolFork :=
  [.Frontier, .Homestead, .DAOFork, .TangerineWhistle, .SpuriousDragon,
   .Byzantium, .StPetersburg, .Istanbul, .MuirGlacier, .Berlin, .London,
   .ArrowGlacier, .GrayGlacier, .Paris, .Shanghai, .Cancun, .Prague, .Osaka,
   .BPO1, .BPO2, .Amsterdam]

/-! ## Chain-config dataclasses (`stateless.py:139`–`183`) -/

/-- `ForkActivation` (`stateless.py:141`). -/
structure ForkActivation where
  blockNumber : Option U64
  timestamp : Option U64
  deriving Repr, BEq, DecidableEq

/-- `BlobSchedule` (`stateless.py:152`). -/
structure BlobSchedule where
  target : U64
  max : U64
  baseFeeUpdateFraction : U64
  deriving Repr, BEq, DecidableEq

/-- `ForkConfig` (`stateless.py:164`). -/
structure ForkConfig where
  fork : ProtocolFork
  activation : ForkActivation
  blobSchedule : Option BlobSchedule
  deriving Repr, BEq, DecidableEq

/-- `ChainConfig` (`stateless.py:176`). -/
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

/-- `ExecutionRequests` (`execution_engine/requests.py:67`). -/
structure ExecutionRequests where
  deposits : List DepositRequest
  withdrawals : List WithdrawalRequest
  consolidations : List ConsolidationRequest
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

/-! ## Amsterdam-compiled constants (`vm/gas.py`) -/

/-- `BLOB_SCHEDULE_TARGET` (`vm/gas.py:106`). -/
def blobScheduleTarget : U64 := 14
/-- `BLOB_SCHEDULE_MAX` (`vm/gas.py:109`). -/
def blobScheduleMax : U64 := 21
/-- `BLOB_BASE_FEE_UPDATE_FRACTION` (`vm/gas.py:111`). -/
def blobBaseFeeUpdateFraction : Uint := 11684671

end EvmAsm.Stateless.SpecRef
