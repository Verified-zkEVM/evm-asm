/-
  EvmAsm.Stateless.SpecRef.BlocksRlp

  The RLP *encode* side of
  `execution-specs/src/ethereum/forks/amsterdam/blocks.py`
  (`@tests-zkevm@v0.5.0`, `bd8c673`): `rlp.encode` over the `Header`
  (class `Header`), `Withdrawal` (class `Withdrawal`) and `Block`
  (class `Block`) dataclasses — needed by the seam shell (bead
  `evm-asm-s1d19.3`) for `is_valid_block_hash` (header hash),
  `validate_header` (parent-header hash) and `execute_block`'s
  `MAX_RLP_BLOCK_SIZE` check.  SpecRef so far only *decoded* headers
  (`Stateless.lean` `_decode_header`).

  `ethereum_rlp` encodes a dataclass as the RLP list of its fields in
  declaration order: `Uint`/`U64`/`U256` as minimal big-endian scalars,
  `Bytes`/fixed-byte fields verbatim.  The 21-field previous-fork
  header (`PreviousForkHeader`) omits the two amsterdam-only trailing
  fields — dispatched here on the decoded `isCurrentFork` tag.  Since #11513
  `_decode_header` DOES re-impose the reference's per-field canonicality check,
  so every header on the accepting path is canonically encoded and re-encoding
  reproduces the original bytes exactly.  (This note previously recorded the
  same round-trip conclusion as holding *despite* the missing check, restricted
  to canonically-encoded input; the check makes that restriction vacuous, so the
  claim is now unconditional on the accepting path.)
-/

import EvmAsm.Stateless.SpecRef.Types
import EvmAsm.EL.RLP.FullDecode

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP (RLPItem)

private def scalarItem (n : Nat) : RLPItem := .bytes (EvmAsm.EL.RLP.Nat.toBytesBE n)

/-- `rlp.encode(header)`'s item: the 23 amsterdam fields, or 21 for a
    previous-fork header. -/
def headerToRlpItem (h : Header) : RLPItem :=
  .list ([.bytes h.parentHash, .bytes h.ommersHash, .bytes h.coinbase,
    .bytes h.stateRoot, .bytes h.transactionsRoot, .bytes h.receiptRoot,
    .bytes h.bloom, scalarItem h.difficulty, scalarItem h.number,
    scalarItem h.gasLimit, scalarItem h.gasUsed, scalarItem h.timestamp,
    .bytes h.extraData, .bytes h.prevRandao, .bytes h.nonce,
    scalarItem h.baseFeePerGas, .bytes h.withdrawalsRoot,
    scalarItem h.blobGasUsed, scalarItem h.excessBlobGas,
    .bytes h.parentBeaconBlockRoot, .bytes h.requestsHash]
    ++ (if h.isCurrentFork then
          [.bytes h.blockAccessListHash, scalarItem h.slotNumber]
        else []))

/-- `rlp.encode(withdrawal)`'s item: `[index, validator_index, address,
    amount]`. -/
def withdrawalToRlpItem (w : Withdrawal) : RLPItem :=
  .list [scalarItem w.index, scalarItem w.validatorIndex,
         .bytes w.address, scalarItem w.amount]

/-- `Block` (class `Block`).  On the payload path (`_payload_block`)
    transactions are the raw payload envelopes and `ommers` is empty. -/
structure Block where
  header : Header
  transactions : List Bytes
  ommers : List Header
  withdrawals : List Withdrawal
  deriving Repr

/-- `rlp.encode(block)`'s item: `[header, transactions, ommers,
    withdrawals]`. -/
def blockToRlpItem (b : Block) : RLPItem :=
  .list [headerToRlpItem b.header,
         .list (b.transactions.map .bytes),
         .list (b.ommers.map headerToRlpItem),
         .list (b.withdrawals.map withdrawalToRlpItem)]

/-- `keccak256(rlp.encode(header))` — the block hash. -/
def headerHash (h : Header) : Hash32 :=
  keccak256 (EvmAsm.EL.RLP.encode (headerToRlpItem h))

/-! ## Sanity checks -/

-- keccak(rlp(header)) matches the Python spec on a synthetic header
-- (all-zero hashes, number 1, gas limit 3·10⁷, slot 1).
private def rlpTestHeader : Header :=
  { isCurrentFork := true, parentHash := List.replicate 32 0,
    ommersHash := List.replicate 32 0, coinbase := List.replicate 20 0,
    stateRoot := List.replicate 32 0, transactionsRoot := List.replicate 32 0,
    receiptRoot := List.replicate 32 0, bloom := List.replicate 256 0,
    difficulty := 0, number := 1, gasLimit := 30000000, gasUsed := 0,
    timestamp := 0, extraData := [], prevRandao := List.replicate 32 0,
    nonce := List.replicate 8 0, baseFeePerGas := 7,
    withdrawalsRoot := List.replicate 32 0, blobGasUsed := 0,
    excessBlobGas := 0, parentBeaconBlockRoot := List.replicate 32 0,
    requestsHash := List.replicate 32 0,
    blockAccessListHash := List.replicate 32 0, slotNumber := 1 }

#guard bytesBEtoNat (headerHash rlpTestHeader)
  == 0xaa1274562be0d8f34002861987fa166ee8903056f4df36509220bd9c7b8f89e2

-- Withdrawal RLP matches the Python encoding.
#guard EvmAsm.EL.RLP.encode (withdrawalToRlpItem
    { index := 1, validatorIndex := 2, address := List.replicate 20 0xAA, amount := 3 })
  == [0xD8, 0x01, 0x02, 0x94, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA,
      0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0x03]

end EvmAsm.Stateless.SpecRef
