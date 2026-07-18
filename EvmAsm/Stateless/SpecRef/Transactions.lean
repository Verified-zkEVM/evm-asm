/-
  EvmAsm.Stateless.SpecRef.Transactions

  Port of the transaction-envelope *decode* side of
  `execution-specs/src/ethereum/forks/amsterdam/transactions.py`
  (`@tests-zkevm@v0.6.0`, `40f956fab`):

  * the five transaction dataclasses (classes `LegacyTransaction`,
    `AccessListTransaction`, `FeeMarketTransaction`, `BlobTransaction`,
    `SetCodeTransaction`) + `Access` (class `Access`) and the
    `fork_types.py` `Authorization` (class `Authorization`)
  * `decode_transaction` (function `decode_transaction`)

  This began as the decode subset the seam shell needs
  (`is_valid_versioned_hashes`, bead `evm-asm-s1d19.3`); Stack C stage 2
  (`s1d19.5`) adds the rest of `transactions.py`:

  * `IntrinsicGasCost` (class `IntrinsicGasCost`), `TX_MAX_GAS_LIMIT`
  * `encode_transaction`, `get_transaction_hash` (functions of the
    same names)
  * `validate_transaction`, `calculate_intrinsic_cost`,
    `count_tokens_in_data` (functions of the same names)
  * `chain_id` (function `chain_id`, v0.6.0/EIP-155), `recover_sender`,
    `recover_transaction_public_key`,
    `recover_sender_from_public_key`, `_sender_address_from_public_key`,
    `_signature_recovery_parameters`, and the five `signing_hash_*`
    (functions of the same names) — secp256k1 recovery delegates to
    `Secp256k1Recover.lean` (the project-side reference for the
    coincurve dependency).

  ## Modeling notes

  * Python decodes via `ethereum_rlp.rlp.decode_to(T, bytes)`, which is
    STRICT: dataclasses need the exact field count; scalars reject
    leading zero bytes ("non-canonical integer") and widths beyond the
    type (`U8`/`U64`/`U256`; `Uint` unbounded); fixed byte fields need
    the exact length; the `Bytes0 | Address` union succeeds on exactly
    one variant (0- xor 20-byte).  `decodeItem*` below mirror those
    rules; every `DecodingError` is a `SpecError.txDecodeError`.
  * `decode_transaction` on raw bytes dispatches on the first byte:
    `0x01`–`0x04` typed envelopes (RLP payload after the type byte),
    `0xC0`–`0xFE` legacy (the whole input is the RLP), anything else is
    `TransactionTypeError` (and `0xFF` the trailing `assert`) — all
    rejections.  An empty input is Python's `tx[0]` `IndexError`.
-/

import EvmAsm.Stateless.SpecRef.Types
import EvmAsm.Stateless.SpecRef.Gas
import EvmAsm.Stateless.SpecRef.Secp256k1Recover
import EvmAsm.EL.RLP.FullDecode

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP (RLPItem decodeFully)

/-! ## Transaction dataclasses -/

/-- `Access` (`transactions.py`, class `Access`). -/
structure Access where
  account : Address
  slots : List Bytes32
  deriving Repr, BEq, DecidableEq

/-- `Authorization` (`fork_types.py`, class `Authorization`). -/
structure Authorization where
  chainId : U256
  address : Address
  nonce : U64
  yParity : Nat
  r : U256
  s : U256
  deriving Repr, BEq, DecidableEq

/-- `LegacyTransaction` (`transactions.py`, class `LegacyTransaction`).
    `to = none` is the `Bytes0` contract-creation variant. -/
structure LegacyTransaction where
  nonce : U256
  gasPrice : Uint
  gas : Uint
  to : Option Address
  value : U256
  data : Bytes
  v : U256
  r : U256
  s : U256
  deriving Repr, BEq, DecidableEq

/-- `AccessListTransaction` (`transactions.py`, class
    `AccessListTransaction`, EIP-2930). -/
structure AccessListTransaction where
  chainId : U64
  nonce : U256
  gasPrice : Uint
  gas : Uint
  to : Option Address
  value : U256
  data : Bytes
  accessList : List Access
  yParity : U256
  r : U256
  s : U256
  deriving Repr, BEq, DecidableEq

/-- `FeeMarketTransaction` (`transactions.py`, class
    `FeeMarketTransaction`, EIP-1559). -/
structure FeeMarketTransaction where
  chainId : U64
  nonce : U256
  maxPriorityFeePerGas : Uint
  maxFeePerGas : Uint
  gas : Uint
  to : Option Address
  value : U256
  data : Bytes
  accessList : List Access
  yParity : U256
  r : U256
  s : U256
  deriving Repr, BEq, DecidableEq

/-- `BlobTransaction` (`transactions.py`, class `BlobTransaction`,
    EIP-4844).  `to` is a mandatory `Address` (no creation). -/
structure BlobTransaction where
  chainId : U64
  nonce : U256
  maxPriorityFeePerGas : Uint
  maxFeePerGas : Uint
  gas : Uint
  to : Address
  value : U256
  data : Bytes
  accessList : List Access
  maxFeePerBlobGas : U256
  blobVersionedHashes : List VersionedHash
  yParity : U256
  r : U256
  s : U256
  deriving Repr, BEq, DecidableEq

/-- `SetCodeTransaction` (`transactions.py`, class `SetCodeTransaction`,
    EIP-7702).  `nonce` is a `U64` here (unlike the other types). -/
structure SetCodeTransaction where
  chainId : U64
  nonce : U64
  maxPriorityFeePerGas : Uint
  maxFeePerGas : Uint
  gas : Uint
  to : Address
  value : U256
  data : Bytes
  accessList : List Access
  authorizations : List Authorization
  yParity : U256
  r : U256
  s : U256
  deriving Repr, BEq, DecidableEq

/-- The `Transaction` union (`transactions.py`). -/
inductive Transaction where
  | legacy (tx : LegacyTransaction)
  | accessList (tx : AccessListTransaction)
  | feeMarket (tx : FeeMarketTransaction)
  | blob (tx : BlobTransaction)
  | setCode (tx : SetCodeTransaction)
  deriving Repr, BEq

/-! ## Strict `rlp.decode_to` field decoders -/

private def txErr {α} (why : String) : Except SpecError α :=
  throw (.txDecodeError why)

/-- Scalar field: bytes, no leading zero, at most `maxBytes` wide
    (`none` = unbounded `Uint`). -/
def decodeItemScalar (maxBytes : Option Nat) : RLPItem → Except SpecError Nat
  | .bytes b => do
      if b.headD 0 == 0 && !b.isEmpty then txErr "non-canonical integer"
      else if let some w := maxBytes then
        if b.length > w then txErr "integer out of range" else pure (bytesBEtoNat b)
      else pure (bytesBEtoNat b)
  | .list _ => txErr "invalid uint"

/-- Unbounded-width `Bytes` field. -/
def decodeItemBytes : RLPItem → Except SpecError Bytes
  | .bytes b => pure b
  | .list _ => txErr "invalid bytes"

/-- Fixed-width byte field (`Address`/`Bytes32`/…). -/
def decodeItemFixedBytes (width : Nat) : RLPItem → Except SpecError Bytes
  | .bytes b => if b.length == width then pure b else txErr "invalid fixed bytes"
  | .list _ => txErr "invalid bytes"

/-- The `Bytes0 | Address` union: empty (creation) xor 20 bytes. -/
def decodeItemTo : RLPItem → Except SpecError (Option Address)
  | .bytes [] => pure none
  | .bytes b => if b.length == 20 then pure (some b) else txErr "invalid to"
  | .list _ => txErr "invalid to"

/-- An `Access` entry: `[address, [slot32, …]]`. -/
def decodeItemAccess : RLPItem → Except SpecError Access
  | .list [addr, .list slots] => do
      pure { account := ← decodeItemFixedBytes 20 addr
             slots := ← slots.mapM (decodeItemFixedBytes 32) }
  | _ => txErr "invalid access-list entry"

/-- An `Authorization`: `[chain_id, address, nonce, y_parity, r, s]`
    (`y_parity : U8`). -/
def decodeItemAuthorization : RLPItem → Except SpecError Authorization
  | .list [cid, addr, nonce, yp, r, s] => do
      pure { chainId := ← decodeItemScalar (some 32) cid
             address := ← decodeItemFixedBytes 20 addr
             nonce := ← decodeItemScalar (some 8) nonce
             yParity := ← decodeItemScalar (some 1) yp
             r := ← decodeItemScalar (some 32) r
             s := ← decodeItemScalar (some 32) s }
  | _ => txErr "invalid authorization"

/-! ## Per-type decoders (`rlp.decode_to(T, …)`) -/

def decodeLegacy : RLPItem → Except SpecError LegacyTransaction
  | .list [nonce, gasPrice, gas, to, value, data, v, r, s] => do
      pure { nonce := ← decodeItemScalar (some 32) nonce
             gasPrice := ← decodeItemScalar none gasPrice
             gas := ← decodeItemScalar none gas
             to := ← decodeItemTo to
             value := ← decodeItemScalar (some 32) value
             data := ← decodeItemBytes data
             v := ← decodeItemScalar (some 32) v
             r := ← decodeItemScalar (some 32) r
             s := ← decodeItemScalar (some 32) s }
  | _ => txErr "LegacyTransaction needs 9 fields"

def decodeAccessListTx : RLPItem → Except SpecError AccessListTransaction
  | .list [cid, nonce, gasPrice, gas, to, value, data, .list al, yp, r, s] => do
      pure { chainId := ← decodeItemScalar (some 8) cid
             nonce := ← decodeItemScalar (some 32) nonce
             gasPrice := ← decodeItemScalar none gasPrice
             gas := ← decodeItemScalar none gas
             to := ← decodeItemTo to
             value := ← decodeItemScalar (some 32) value
             data := ← decodeItemBytes data
             accessList := ← al.mapM decodeItemAccess
             yParity := ← decodeItemScalar (some 32) yp
             r := ← decodeItemScalar (some 32) r
             s := ← decodeItemScalar (some 32) s }
  | _ => txErr "AccessListTransaction needs 11 fields"

def decodeFeeMarketTx : RLPItem → Except SpecError FeeMarketTransaction
  | .list [cid, nonce, prio, maxFee, gas, to, value, data, .list al, yp, r, s] => do
      pure { chainId := ← decodeItemScalar (some 8) cid
             nonce := ← decodeItemScalar (some 32) nonce
             maxPriorityFeePerGas := ← decodeItemScalar none prio
             maxFeePerGas := ← decodeItemScalar none maxFee
             gas := ← decodeItemScalar none gas
             to := ← decodeItemTo to
             value := ← decodeItemScalar (some 32) value
             data := ← decodeItemBytes data
             accessList := ← al.mapM decodeItemAccess
             yParity := ← decodeItemScalar (some 32) yp
             r := ← decodeItemScalar (some 32) r
             s := ← decodeItemScalar (some 32) s }
  | _ => txErr "FeeMarketTransaction needs 12 fields"

def decodeBlobTx : RLPItem → Except SpecError BlobTransaction
  | .list [cid, nonce, prio, maxFee, gas, to, value, data, .list al,
           blobFee, .list bvh, yp, r, s] => do
      pure { chainId := ← decodeItemScalar (some 8) cid
             nonce := ← decodeItemScalar (some 32) nonce
             maxPriorityFeePerGas := ← decodeItemScalar none prio
             maxFeePerGas := ← decodeItemScalar none maxFee
             gas := ← decodeItemScalar none gas
             to := ← decodeItemFixedBytes 20 to
             value := ← decodeItemScalar (some 32) value
             data := ← decodeItemBytes data
             accessList := ← al.mapM decodeItemAccess
             maxFeePerBlobGas := ← decodeItemScalar (some 32) blobFee
             blobVersionedHashes := ← bvh.mapM (decodeItemFixedBytes 32)
             yParity := ← decodeItemScalar (some 32) yp
             r := ← decodeItemScalar (some 32) r
             s := ← decodeItemScalar (some 32) s }
  | _ => txErr "BlobTransaction needs 14 fields"

def decodeSetCodeTx : RLPItem → Except SpecError SetCodeTransaction
  | .list [cid, nonce, prio, maxFee, gas, to, value, data, .list al,
           .list auths, yp, r, s] => do
      pure { chainId := ← decodeItemScalar (some 8) cid
             nonce := ← decodeItemScalar (some 8) nonce
             maxPriorityFeePerGas := ← decodeItemScalar none prio
             maxFeePerGas := ← decodeItemScalar none maxFee
             gas := ← decodeItemScalar none gas
             to := ← decodeItemFixedBytes 20 to
             value := ← decodeItemScalar (some 32) value
             data := ← decodeItemBytes data
             accessList := ← al.mapM decodeItemAccess
             authorizations := ← auths.mapM decodeItemAuthorization
             yParity := ← decodeItemScalar (some 32) yp
             r := ← decodeItemScalar (some 32) r
             s := ← decodeItemScalar (some 32) s }
  | _ => txErr "SetCodeTransaction needs 13 fields"

/-! ## `decode_transaction` (function `decode_transaction`) -/

/-- Decode a raw transaction envelope.  First byte: `0x01`–`0x04` typed
    (RLP after the type byte), `0xC0`–`0xFE` legacy (whole input is the
    RLP), else `TransactionTypeError`/`assert` → rejection; empty input
    is the `tx[0]` `IndexError`. -/
def decode_transaction (tx : Bytes) : Except SpecError Transaction := do
  match tx with
  | [] => txErr "empty transaction"
  | b0 :: rest =>
      let payload := fun (_ : Unit) =>
        match decodeFully rest with
        | some item => pure item
        | none => txErr (α := RLPItem) "transaction RLP decode failed"
      if b0 == 0x01 then .accessList <$> (decodeAccessListTx (← payload ()))
      else if b0 == 0x02 then .feeMarket <$> (decodeFeeMarketTx (← payload ()))
      else if b0 == 0x03 then .blob <$> (decodeBlobTx (← payload ()))
      else if b0 == 0x04 then .setCode <$> (decodeSetCodeTx (← payload ()))
      else if 0xC0 ≤ b0.toNat && b0.toNat ≤ 0xFE then
        match decodeFully tx with
        | some item => .legacy <$> decodeLegacy item
        | none => txErr "transaction RLP decode failed"
      else txErr s!"unknown transaction type {b0.toNat}"

/-! ## Uniform accessors over the `Transaction` union -/

namespace Transaction

def gas : Transaction → Uint
  | .legacy tx => tx.gas | .accessList tx => tx.gas | .feeMarket tx => tx.gas
  | .blob tx => tx.gas | .setCode tx => tx.gas

def nonce : Transaction → Nat
  | .legacy tx => tx.nonce | .accessList tx => tx.nonce | .feeMarket tx => tx.nonce
  | .blob tx => tx.nonce | .setCode tx => tx.nonce

/-- `tx.to` — `none` is the `Bytes0` creation form (only legacy /
    access-list / fee-market allow it). -/
def to : Transaction → Option Address
  | .legacy tx => tx.to | .accessList tx => tx.to | .feeMarket tx => tx.to
  | .blob tx => some tx.to | .setCode tx => some tx.to

def value : Transaction → U256
  | .legacy tx => tx.value | .accessList tx => tx.value | .feeMarket tx => tx.value
  | .blob tx => tx.value | .setCode tx => tx.value

def data : Transaction → Bytes
  | .legacy tx => tx.data | .accessList tx => tx.data | .feeMarket tx => tx.data
  | .blob tx => tx.data | .setCode tx => tx.data

def r : Transaction → U256
  | .legacy tx => tx.r | .accessList tx => tx.r | .feeMarket tx => tx.r
  | .blob tx => tx.r | .setCode tx => tx.r

def s : Transaction → U256
  | .legacy tx => tx.s | .accessList tx => tx.s | .feeMarket tx => tx.s
  | .blob tx => tx.s | .setCode tx => tx.s

/-- `has_access_list(tx)` (function `has_access_list`) — the access
    list itself (`[]` for legacy). -/
def accessList? : Transaction → Option (List Access)
  | .legacy _ => none
  | .accessList tx => some tx.accessList
  | .feeMarket tx => some tx.accessList
  | .blob tx => some tx.accessList
  | .setCode tx => some tx.accessList

end Transaction

/-! ## Envelope encoding (`encode_transaction`, `get_transaction_hash`) -/

private def scalarT (n : Nat) : RLPItem := .bytes (EvmAsm.EL.RLP.Nat.toBytesBE n)
private def toItem : Option Address → RLPItem
  | none => .bytes []
  | some a => .bytes a
private def accessItem (a : Access) : RLPItem :=
  .list [.bytes a.account, .list (a.slots.map .bytes)]
private def authItem (a : Authorization) : RLPItem :=
  .list [scalarT a.chainId, .bytes a.address, scalarT a.nonce,
         scalarT a.yParity, scalarT a.r, scalarT a.s]

/-- The RLP item of each dataclass (`rlp.encode(tx)`'s argument). -/
def txToRlpItem : Transaction → RLPItem
  | .legacy tx => .list
      [scalarT tx.nonce, scalarT tx.gasPrice, scalarT tx.gas, toItem tx.to,
       scalarT tx.value, .bytes tx.data, scalarT tx.v, scalarT tx.r, scalarT tx.s]
  | .accessList tx => .list
      [scalarT tx.chainId, scalarT tx.nonce, scalarT tx.gasPrice, scalarT tx.gas,
       toItem tx.to, scalarT tx.value, .bytes tx.data,
       .list (tx.accessList.map accessItem), scalarT tx.yParity, scalarT tx.r,
       scalarT tx.s]
  | .feeMarket tx => .list
      [scalarT tx.chainId, scalarT tx.nonce, scalarT tx.maxPriorityFeePerGas,
       scalarT tx.maxFeePerGas, scalarT tx.gas, toItem tx.to, scalarT tx.value,
       .bytes tx.data, .list (tx.accessList.map accessItem), scalarT tx.yParity,
       scalarT tx.r, scalarT tx.s]
  | .blob tx => .list
      [scalarT tx.chainId, scalarT tx.nonce, scalarT tx.maxPriorityFeePerGas,
       scalarT tx.maxFeePerGas, scalarT tx.gas, .bytes tx.to, scalarT tx.value,
       .bytes tx.data, .list (tx.accessList.map accessItem),
       scalarT tx.maxFeePerBlobGas, .list (tx.blobVersionedHashes.map .bytes),
       scalarT tx.yParity, scalarT tx.r, scalarT tx.s]
  | .setCode tx => .list
      [scalarT tx.chainId, scalarT tx.nonce, scalarT tx.maxPriorityFeePerGas,
       scalarT tx.maxFeePerGas, scalarT tx.gas, .bytes tx.to, scalarT tx.value,
       .bytes tx.data, .list (tx.accessList.map accessItem),
       .list (tx.authorizations.map authItem), scalarT tx.yParity, scalarT tx.r,
       scalarT tx.s]

/-- `encode_transaction(tx)` (function `encode_transaction`): the raw
    envelope — legacy is its RLP, typed forms get their type byte. -/
def encode_transaction (tx : Transaction) : Bytes :=
  match tx with
  | .legacy _ => EvmAsm.EL.RLP.encode (txToRlpItem tx)
  | .accessList _ => 0x01 :: EvmAsm.EL.RLP.encode (txToRlpItem tx)
  | .feeMarket _ => 0x02 :: EvmAsm.EL.RLP.encode (txToRlpItem tx)
  | .blob _ => 0x03 :: EvmAsm.EL.RLP.encode (txToRlpItem tx)
  | .setCode _ => 0x04 :: EvmAsm.EL.RLP.encode (txToRlpItem tx)

/-- `get_transaction_hash(tx)` (function `get_transaction_hash`) on the
    raw envelope bytes (payload transactions are always `Bytes`; a
    legacy envelope IS its RLP, so one keccak covers both arms). -/
def get_transaction_hash (encoded_tx : Bytes) : Hash32 :=
  keccak256 encoded_tx

/-! ## Intrinsic gas (`IntrinsicGasCost`, `validate_transaction`,
`calculate_intrinsic_cost`, `count_tokens_in_data`) -/

/-- `IntrinsicGasCost` (class `IntrinsicGasCost`). v0.6.0 wraps the
    fields in `RegularGas`/`StateGas` NewTypes (type hygiene only, no
    numeric change); the port keeps plain `Uint`. -/
structure IntrinsicGasCost where
  regular : Uint
  state : Uint
  calldataFloor : Uint
  deriving Repr, BEq

/-- `TX_MAX_GAS_LIMIT` (EIP-8037). -/
def TX_MAX_GAS_LIMIT : Uint := 16777216

/-- `ACCESS_LIST_ADDRESS_FLOOR_TOKENS` (EIP-7981). -/
def ACCESS_LIST_ADDRESS_FLOOR_TOKENS : Uint := 80
/-- `ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS` (EIP-7981). -/
def ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS : Uint := 128

/-- `MAX_CODE_SIZE` / `MAX_INIT_CODE_SIZE` (`vm/interpreter.py`). -/
def MAX_CODE_SIZE : Nat := 0x10000
def MAX_INIT_CODE_SIZE : Nat := 2 * MAX_CODE_SIZE

/-- `count_tokens_in_data(data)`: zero bytes 1 token, non-zero 4. -/
def count_tokens_in_data (data : Bytes) : Uint :=
  let num_zeros := data.countP (· == 0)
  num_zeros + (data.length - num_zeros) * 4

/-- `calculate_intrinsic_cost(tx, sender)`. v0.6.0 (EIP-2780 rework):
    state-dependent charges leave the intrinsic — a creation's
    `NEW_ACCOUNT` state gas is charged at the top frame
    (`prepare_dispatch`), and an authorization's account-creation /
    delegation-write costs are charged by `set_delegation`; only the
    state-independent `REGULAR_PER_AUTH_BASE_COST` remains per tuple.
    `init_code_cost` is split out of the recipient gas, and the calldata
    floor is anchored on `base_regular_gas = TX_BASE +
    recipient_regular_gas` rather than `TX_BASE` alone. -/
def calculate_intrinsic_cost (tx : Transaction) (sender : Address) :
    IntrinsicGasCost :=
  let tokens_in_calldata := count_tokens_in_data tx.data
  let data_cost := tokens_in_calldata * GasCosts.TX_DATA_TOKEN_STANDARD
  let is_create := tx.to == none
  let is_self_transfer := tx.to == some sender
  let (recipient_regular_gas, init_code_gas) :=
    if is_create then
      (GasCosts.CREATE_ACCESS
        + (if tx.value > 0 then GasCosts.TRANSFER_LOG_COST else 0),
       init_code_cost tx.data.length)
    else if !is_self_transfer then
      (GasCosts.COLD_ACCOUNT_ACCESS
        + (if tx.value > 0 then GasCosts.TRANSFER_LOG_COST + GasCosts.TX_VALUE_COST else 0),
       0)
    else (0, 0)
  let (access_list_cost, tokens_in_access_list) :=
    match tx.accessList? with
    | none => (0, 0)
    | some al => al.foldl (fun (cost, tokens) access =>
        (cost + GasCosts.TX_ACCESS_LIST_ADDRESS
           + access.slots.length * GasCosts.TX_ACCESS_LIST_STORAGE_KEY,
         tokens + ACCESS_LIST_ADDRESS_FLOOR_TOKENS
           + access.slots.length * ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS)) (0, 0)
  let access_list_cost := access_list_cost
    + tokens_in_access_list * GasCosts.TX_DATA_TOKEN_FLOOR
  let auth_regular_gas :=
    match tx with
    | .setCode t => GasCosts.REGULAR_PER_AUTH_BASE_COST * t.authorizations.length
    | _ => 0
  let floor_tokens_in_calldata := tx.data.length * GasCosts.TX_DATA_TOKEN_STANDARD
  let total_floor_tokens := floor_tokens_in_calldata + tokens_in_access_list
  -- Decomposed regular-gas intrinsic base (EIP-2780), which also anchors
  -- the calldata floor.
  let base_regular_gas := GasCosts.TX_BASE + recipient_regular_gas
  { regular := base_regular_gas + init_code_gas + data_cost
      + access_list_cost + auth_regular_gas
    state := 0
    calldataFloor := total_floor_tokens * GasCosts.TX_DATA_TOKEN_FLOOR
      + base_regular_gas }

/-- `validate_transaction(tx, sender)`: each raise is a distinct
    rejection reason. -/
def validate_transaction (tx : Transaction) (sender : Address) :
    Except SpecError IntrinsicGasCost := do
  let intrinsic := calculate_intrinsic_cost tx sender
  if intrinsic.regular + intrinsic.state > tx.gas then
    throw (.invalidTransaction "Insufficient intrinsic gas")
  if intrinsic.calldataFloor > tx.gas then
    throw (.invalidTransaction "Insufficient calldata floor")
  if tx.to == none && tx.data.length > MAX_INIT_CODE_SIZE then
    throw (.invalidTransaction "Code size too large")
  if intrinsic.regular > TX_MAX_GAS_LIMIT then
    throw (.invalidTransaction "Intrinsic regular gas exceeds TX_MAX_GAS_LIMIT")
  if intrinsic.calldataFloor > TX_MAX_GAS_LIMIT then
    throw (.invalidTransaction "Intrinsic calldata floor exceeds TX_MAX_GAS_LIMIT")
  if tx.nonce ≥ 2^64 - 1 then
    throw (.invalidTransaction "Nonce too high")
  pure intrinsic

/-! ## Sender recovery (`_signature_recovery_parameters`,
`recover_transaction_public_key`, `recover_sender_from_public_key`,
`_sender_address_from_public_key`, `signing_hash_*`) -/

/-- `SECP256K1N` (`ethereum/crypto/elliptic_curve.py`). -/
def SECP256K1N : Nat := Secp256k1.n

private def signPrefix (typeByte : Option (BitVec 8)) (item : RLPItem) : Hash32 :=
  keccak256 ((typeByte.map ([·])).getD [] ++ EvmAsm.EL.RLP.encode item)

/-- `signing_hash_pre155(tx)` (function `signing_hash_pre155`). -/
def signing_hash_pre155 (tx : LegacyTransaction) : Hash32 :=
  signPrefix none (.list [scalarT tx.nonce, scalarT tx.gasPrice, scalarT tx.gas,
    toItem tx.to, scalarT tx.value, .bytes tx.data])

/-- `signing_hash_155(tx, chain_id)` (function `signing_hash_155`). -/
def signing_hash_155 (tx : LegacyTransaction) (chain_id : U64) : Hash32 :=
  signPrefix none (.list [scalarT tx.nonce, scalarT tx.gasPrice, scalarT tx.gas,
    toItem tx.to, scalarT tx.value, .bytes tx.data, scalarT chain_id,
    scalarT 0, scalarT 0])

/-- `signing_hash_2930(tx)` (function `signing_hash_2930`). -/
def signing_hash_2930 (tx : AccessListTransaction) : Hash32 :=
  signPrefix (some 0x01) (.list [scalarT tx.chainId, scalarT tx.nonce,
    scalarT tx.gasPrice, scalarT tx.gas, toItem tx.to, scalarT tx.value,
    .bytes tx.data, .list (tx.accessList.map accessItem)])

/-- `signing_hash_1559(tx)` (function `signing_hash_1559`). -/
def signing_hash_1559 (tx : FeeMarketTransaction) : Hash32 :=
  signPrefix (some 0x02) (.list [scalarT tx.chainId, scalarT tx.nonce,
    scalarT tx.maxPriorityFeePerGas, scalarT tx.maxFeePerGas, scalarT tx.gas,
    toItem tx.to, scalarT tx.value, .bytes tx.data,
    .list (tx.accessList.map accessItem)])

/-- `signing_hash_4844(tx)` (function `signing_hash_4844`). -/
def signing_hash_4844 (tx : BlobTransaction) : Hash32 :=
  signPrefix (some 0x03) (.list [scalarT tx.chainId, scalarT tx.nonce,
    scalarT tx.maxPriorityFeePerGas, scalarT tx.maxFeePerGas, scalarT tx.gas,
    .bytes tx.to, scalarT tx.value, .bytes tx.data,
    .list (tx.accessList.map accessItem), scalarT tx.maxFeePerBlobGas,
    .list (tx.blobVersionedHashes.map .bytes)])

/-- `signing_hash_7702(tx)` (function `signing_hash_7702`). -/
def signing_hash_7702 (tx : SetCodeTransaction) : Hash32 :=
  signPrefix (some 0x04) (.list [scalarT tx.chainId, scalarT tx.nonce,
    scalarT tx.maxPriorityFeePerGas, scalarT tx.maxFeePerGas, scalarT tx.gas,
    .bytes tx.to, scalarT tx.value, .bytes tx.data,
    .list (tx.accessList.map accessItem),
    .list (tx.authorizations.map authItem)])

/-- `_signature_recovery_parameters(chain_id, tx)`: `(r, s, recovery_id,
    signing_hash)`; every `InvalidSignatureError` is a rejection. -/
def _signature_recovery_parameters (chain_id : U64) (tx : Transaction) :
    Except SpecError (U256 × U256 × U256 × Hash32) := do
  let r := tx.r
  let s := tx.s
  if 0 ≥ r || r ≥ SECP256K1N then throw (.invalidSignature "bad r")
  if 0 ≥ s || s > SECP256K1N / 2 then throw (.invalidSignature "bad s")
  match tx with
  | .legacy t =>
      if t.v == 27 || t.v == 28 then
        pure (r, s, t.v - 27, signing_hash_pre155 t)
      else
        let chain_id_x2 := chain_id * 2
        if t.v ≠ 35 + chain_id_x2 && t.v ≠ 36 + chain_id_x2 then
          throw (.invalidSignature "bad v")
        pure (r, s, t.v - 35 - chain_id_x2, signing_hash_155 t chain_id)
  | .accessList t =>
      if t.yParity ≠ 0 && t.yParity ≠ 1 then throw (.invalidSignature "bad y_parity")
      pure (r, s, t.yParity, signing_hash_2930 t)
  | .feeMarket t =>
      if t.yParity ≠ 0 && t.yParity ≠ 1 then throw (.invalidSignature "bad y_parity")
      pure (r, s, t.yParity, signing_hash_1559 t)
  | .blob t =>
      if t.yParity ≠ 0 && t.yParity ≠ 1 then throw (.invalidSignature "bad y_parity")
      pure (r, s, t.yParity, signing_hash_4844 t)
  | .setCode t =>
      if t.yParity ≠ 0 && t.yParity ≠ 1 then throw (.invalidSignature "bad y_parity")
      pure (r, s, t.yParity, signing_hash_7702 t)

/-- `recover_transaction_public_key(chain_id, tx)`: the canonical
    uncompressed SEC1 key `0x04 ‖ x ‖ y`; any recovery failure is the
    Python exception → rejection. -/
def recover_transaction_public_key (chain_id : U64) (tx : Transaction) :
    Except SpecError Bytes := do
  let (r, s, recovery_id, signing_hash) ← _signature_recovery_parameters chain_id tx
  match Secp256k1.recover (bytesBEtoNat signing_hash) r s recovery_id with
  | .ok (x, y) => pure (0x04 :: (natToBytesBE 32 x ++ natToBytesBE 32 y))
  | .error _ => throw (.invalidSignature "recovery failed")

/-- `_sender_address_from_public_key(public_key)`. -/
def _sender_address_from_public_key (public_key : Bytes) : Address :=
  (keccak256 (public_key.drop 1)).drop 12

/-- `chain_id(tx)` (function `chain_id`, v0.6.0/EIP-155): the chain
    identifier a transaction commits to, or `none` for a pre-155 legacy
    transaction (`v ∈ {27, 28}`). A legacy `v < 35` outside that pair is
    an invalid signature. -/
def chain_id (tx : Transaction) : Except SpecError (Option U64) :=
  match tx with
  | .legacy t =>
      if t.v == 27 || t.v == 28 then pure none
      else if t.v < 35 then throw (.invalidSignature "bad v")
      else pure (some ((t.v - 35) >>> 1))
  | .accessList t => pure (some t.chainId)
  | .feeMarket t => pure (some t.chainId)
  | .blob t => pure (some t.chainId)
  | .setCode t => pure (some t.chainId)

/-- `recover_sender(tx)` (function `recover_sender`). v0.6.0 drops the
    `chain_id` parameter: the recovery chain id comes from the
    transaction itself (`0` for pre-155 legacy). -/
def recover_sender (tx : Transaction) : Except SpecError Address := do
  let tx_chain_id ← chain_id tx
  let recovery_chain_id := tx_chain_id.getD 0
  pure (_sender_address_from_public_key
    (← recover_transaction_public_key recovery_chain_id tx))

/-- `recover_sender_from_public_key(chain_id, tx, public_key)`: verify
    the supplied key by full recovery + comparison (the stateless-guest
    path, fed from `StatelessInput.publicKeys`). -/
def recover_sender_from_public_key (chain_id : U64) (tx : Transaction)
    (public_key : Bytes) : Except SpecError Address := do
  if public_key != (← recover_transaction_public_key chain_id tx) then
    throw (.invalidSignature "public key mismatch")
  pure (_sender_address_from_public_key public_key)

/-! ## Sanity checks -/

private def encT (i : RLPItem) : Bytes := EvmAsm.EL.RLP.encode i
private def scalar (n : Nat) : RLPItem := .bytes (EvmAsm.EL.RLP.Nat.toBytesBE n)

-- A minimal legacy transaction round-trips.
private def legacyRlp : Bytes := encT (.list
  [scalar 1, scalar 20, scalar 21000, .bytes (List.replicate 20 0xAA),
   scalar 5, .bytes [], scalar 37, scalar 0x1234, scalar 0x5678])

#guard match decode_transaction legacyRlp with
  | .ok (.legacy tx) =>
      tx.nonce == 1 && tx.gasPrice == 20 && tx.gas == 21000
      && tx.to == some (List.replicate 20 0xAA) && tx.value == 5
      && tx.v == 37 && tx.r == 0x1234 && tx.s == 0x5678
  | _ => false

-- Creation (`to = Bytes0`) decodes to `none`.
#guard match decode_transaction (encT (.list
    [scalar 0, scalar 1, scalar 53000, .bytes [], scalar 0,
     .bytes [0x60], scalar 27, scalar 1, scalar 1])) with
  | .ok (.legacy tx) => tx.to == none
  | _ => false

-- A blob transaction: versioned hashes decode in order.
private def vh1 : Bytes := 0x01 :: List.replicate 31 0x11
private def vh2 : Bytes := 0x01 :: List.replicate 31 0x22
private def blobTxBytes : Bytes := 0x03 :: encT (.list
  [scalar 1, scalar 0, scalar 1, scalar 10, scalar 21000,
   .bytes (List.replicate 20 0xBB), scalar 0, .bytes [], .list [],
   scalar 100, .list [.bytes vh1, .bytes vh2], scalar 1, scalar 9, scalar 9])

#guard match decode_transaction blobTxBytes with
  | .ok (.blob tx) => tx.blobVersionedHashes == [vh1, vh2] && tx.chainId == 1
  | _ => false

-- Non-canonical scalar (leading zero) and unknown type byte reject.
#guard match decode_transaction (encT (.list
    [.bytes [0x00, 0x01], scalar 20, scalar 21000, .bytes [], scalar 0,
     .bytes [], scalar 37, scalar 1, scalar 1])) with
  | .error (.txDecodeError _) => true | _ => false

#guard match decode_transaction [0x05, 0xC0] with
  | .error (.txDecodeError _) => true | _ => false

#guard match decode_transaction [] with
  | .error (.txDecodeError _) => true | _ => false

-- An access-list entry with a wrong-width slot rejects.
#guard match decode_transaction (0x01 :: encT (.list
    [scalar 1, scalar 0, scalar 1, scalar 21000, .bytes [], scalar 0,
     .bytes [], .list [.list [.bytes (List.replicate 20 0xCC),
                              .list [.bytes [0x01]]]],
     scalar 0, scalar 1, scalar 1])) with
  | .error (.txDecodeError _) => true | _ => false

/-! Intrinsic-cost and recovery vectors, cross-checked against the
Python spec at `bd8c673` (generator in the PR description). -/

private def vSender : Address := List.replicate 20 0xAA

-- Legacy call with mixed calldata.
private def vTx1 : LegacyTransaction :=
  { nonce := 1, gasPrice := 10, gas := 100000, to := some (List.replicate 20 0xBB),
    value := 5, data := [0x00, 0x01, 0x02, 0x00], v := 27, r := 1, s := 1 }

#guard calculate_intrinsic_cost (.legacy vTx1) vSender
  == { regular := 21040, state := 0, calldataFloor := 21256 }

-- Creation with value: CREATE_ACCESS + init-code words + transfer log;
-- v0.6.0 charges no NEW_ACCOUNT state gas here (top frame instead), and
-- the floor is anchored on TX_BASE + CREATE_ACCESS + TRANSFER_LOG_COST
-- (init-code gas excluded from the anchor).
#guard calculate_intrinsic_cost (.legacy
    { nonce := 1, gasPrice := 10, gas := 500000, to := none, value := 1,
      data := List.replicate 40 0x60, v := 27, r := 1, s := 1 }) vSender
  == { regular := 25400, state := 0, calldataFloor := 27316 }

-- Self-transfer with an access list: recipient/value charges skipped.
#guard calculate_intrinsic_cost (.feeMarket
    { chainId := 1, nonce := 0, maxPriorityFeePerGas := 1, maxFeePerGas := 10,
      gas := 100000, to := some vSender, value := 0, data := [],
      accessList := [{ account := List.replicate 20 0xCC,
                       slots := [List.replicate 32 0x01, List.replicate 32 0x02] }],
      yParity := 0, r := 1, s := 1 }) vSender
  == { regular := 26376, state := 0, calldataFloor := 17376 }

-- Set-code with one authorization.
#guard calculate_intrinsic_cost (.setCode
    { chainId := 1, nonce := 0, maxPriorityFeePerGas := 1, maxFeePerGas := 10,
      gas := 200000, to := some (List.replicate 20 0xBB) |>.getD [], value := 0,
      data := [], accessList := [],
      authorizations := [{ chainId := 1, address := List.replicate 20 0xDD,
                           nonce := 0, yParity := 0, r := 1, s := 1 }],
      yParity := 0, r := 1, s := 1 }) vSender
  == { regular := 22816, state := 0, calldataFloor := 15000 }

-- validate_transaction: vTx1 passes; a 21k-gas creation is short.
#guard (validate_transaction (.legacy vTx1) vSender).toOption
  == some { regular := 21040, state := 0, calldataFloor := 21256 }
#guard match validate_transaction (.legacy { vTx1 with to := none, gas := 21000 })
    vSender with
  | .error (.invalidTransaction _) => true | _ => false

-- EIP-155 signing hash + full sender recovery on a coincurve-signed
-- transaction (privkey 0x0101…01, chain id 1).
#guard bytesBEtoNat (signing_hash_155 vTx1 1)
  == 0x65c3ae64d466f2a8ffeab9ea674e0275cd4428e6df077c3d786b5d7a5d8984db

private def vTx1Signed : LegacyTransaction :=
  { vTx1 with
    v := 38
    r := 0x1518619670d02fb8bf8f6f78b6b0885aae6820737cfdd8080a6d829e2f9cb327
    s := 0x6cb5e9483bb48d9ddc77f9ae18296e8df37e00a99d5ea4b927e2b54c41492eec }

private def vPubKey : Bytes :=
  0x04 :: (natToBytesBE 32 0x1b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f
    ++ natToBytesBE 32 0x70beaf8f588b541507fed6a642c5ab42dfdf8120a7f639de5122d47a69a8e8d1)

#guard (recover_transaction_public_key 1 (.legacy vTx1Signed)).toOption == some vPubKey
-- v0.6.0 `recover_sender` derives the chain id from the tx (v = 38 → 1).
#guard (recover_sender (.legacy vTx1Signed)).toOption.map bytesBEtoNat
  == some 0x1a642f0e3c3af545e7acbd38b07251b3990914f1
#guard (chain_id (.legacy vTx1Signed)).toOption == some (some 1)
#guard (chain_id (.legacy vTx1)).toOption == some none  -- v = 27, pre-155
#guard match chain_id (.legacy { vTx1 with v := 30 }) with
  | .error (.invalidSignature _) => true | _ => false
#guard (recover_sender_from_public_key 1 (.legacy vTx1Signed) vPubKey).toOption.map bytesBEtoNat
  == some 0x1a642f0e3c3af545e7acbd38b07251b3990914f1
-- A wrong supplied key is InvalidSignatureError.
#guard match recover_sender_from_public_key 1 (.legacy vTx1Signed)
    (0x04 :: List.replicate 64 0x01) with
  | .error (.invalidSignature _) => true | _ => false
-- High-s rejects (EIP-2).
#guard match recover_sender (.legacy { vTx1Signed with s := SECP256K1N - 1 }) with
  | .error (.invalidSignature _) => true | _ => false

-- encode_transaction round-trips through decode_transaction.
#guard match decode_transaction (encode_transaction (.legacy vTx1Signed)) with
  | .ok (.legacy tx) => tx == vTx1Signed | _ => false

end EvmAsm.Stateless.SpecRef
