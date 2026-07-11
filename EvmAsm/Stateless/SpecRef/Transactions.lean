/-
  EvmAsm.Stateless.SpecRef.Transactions

  Port of the transaction-envelope *decode* side of
  `execution-specs/src/ethereum/forks/amsterdam/transactions.py`
  (`@tests-zkevm@v0.5.0`, `bd8c673`):

  * the five transaction dataclasses (classes `LegacyTransaction`,
    `AccessListTransaction`, `FeeMarketTransaction`, `BlobTransaction`,
    `SetCodeTransaction`) + `Access` (class `Access`) and the
    `fork_types.py` `Authorization` (class `Authorization`)
  * `decode_transaction` (function `decode_transaction`)

  This is the decode subset the seam shell needs
  (`is_valid_versioned_hashes`, bead `evm-asm-s1d19.3`); the rest of
  `transactions.py` (intrinsic costs, sender recovery, signing hashes)
  is Stack C (`s1d19.5`).

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

end EvmAsm.Stateless.SpecRef
