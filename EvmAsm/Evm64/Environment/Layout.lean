/-
  EvmAsm.Evm64.Environment.Layout

  Slice 2 of #100 (EVM environment context layout).

  Concrete byte-offset table for every `EvmEnv` field, materialized as
  named `Nat` constants relative to a base address.  The layout follows
  two simple rules:

  - Fields whose runtime representation is 256-bit (`EvmWord`) or
    20-byte Ethereum addresses (zero-extended to 256 bits in memory)
    occupy a 32-byte slot, 32-byte aligned.
  - Fields whose runtime representation is 64-bit (`Word` — pointers
    and lengths under LP64) occupy an 8-byte slot, 8-byte aligned.

  All 32-byte fields are placed first so their alignment is automatic;
  the 8-byte fields tail the block.  `envSize` is the total footprint.

  This slice introduces only the offset constants and a small set of
  trivially decidable arithmetic facts about them; the `envIs`
  separation-logic assertion that decomposes a heap range into per-field
  cells is the next slice (#100 slice 3 / `evm-asm-3fr7`).

  Layout table (all values in bytes, relative to `base`):

  ```text
  offset  size  field
  ------  ----  ---------------------------
       0    32  address          (Address, zero-extended)
      32    32  selfBalance      (EvmWord)
      64    32  caller           (Address, zero-extended)
      96    32  callValue        (EvmWord)
     128    32  txOrigin         (Address, zero-extended)
     160    32  gasPrice         (EvmWord)
     192    32  blockCoinbase    (Address, zero-extended)
     224    32  blockTimestamp   (EvmWord)
     256    32  blockNumber      (EvmWord)
     288    32  blockPrevrandao  (EvmWord)
     320    32  blockGasLimit    (EvmWord)
     352    32  blockBaseFee     (EvmWord)
     384    32  chainId          (EvmWord)
     416     8  callDataPtr      (Word)
     424     8  callDataLen      (Word)
     432     8  returnDataPtr    (Word)
     440     8  returnDataSize   (Word)
     448        envSize          (total)
  ```
-/

import EvmAsm.Evm64.Environment

namespace EvmAsm.Evm64
namespace EvmEnv

/-! ## 32-byte slot offsets (EvmWord / Address) -/

/-- Byte offset of `address` within the env block. -/
def addressOff : Nat := 0
/-- Byte offset of `selfBalance` within the env block. -/
def selfBalanceOff : Nat := 32
/-- Byte offset of `caller` within the env block. -/
def callerOff : Nat := 64
/-- Byte offset of `callValue` within the env block. -/
def callValueOff : Nat := 96
/-- Byte offset of `txOrigin` within the env block. -/
def txOriginOff : Nat := 128
/-- Byte offset of `gasPrice` within the env block. -/
def gasPriceOff : Nat := 160
/-- Byte offset of `blockCoinbase` within the env block. -/
def blockCoinbaseOff : Nat := 192
/-- Byte offset of `blockTimestamp` within the env block. -/
def blockTimestampOff : Nat := 224
/-- Byte offset of `blockNumber` within the env block. -/
def blockNumberOff : Nat := 256
/-- Byte offset of `blockPrevrandao` within the env block. -/
def blockPrevrandaoOff : Nat := 288
/-- Byte offset of `blockGasLimit` within the env block. -/
def blockGasLimitOff : Nat := 320
/-- Byte offset of `blockBaseFee` within the env block. -/
def blockBaseFeeOff : Nat := 352
/-- Byte offset of `chainId` within the env block. -/
def chainIdOff : Nat := 384

/-! ## 8-byte slot offsets (Word — pointers / lengths) -/

/-- Byte offset of `callDataPtr` within the env block. -/
def callDataPtrOff : Nat := 416
/-- Byte offset of `callDataLen` within the env block. -/
def callDataLenOff : Nat := 424
/-- Byte offset of `returnDataPtr` within the env block. -/
def returnDataPtrOff : Nat := 432
/-- Byte offset of `returnDataSize` within the env block. -/
def returnDataSizeOff : Nat := 440

/-- Total byte size of an EVM environment context block.

    `envSize = 13 * 32 + 4 * 8 = 416 + 32 = 448`. -/
def envSize : Nat := 448

/-! ## Layout sanity facts

These are all concrete `Nat`-literal facts; they exist so downstream
slices (and tests) can `rfl`/`decide` against the named layout without
re-deriving each offset.  Bumping the layout in a future slice forces
exactly one consistent rewrite in this file. -/

/-- `addressOff` is 32-byte aligned. -/
theorem addressOff_align : addressOff % 32 = 0 := by decide
/-- `selfBalanceOff` is 32-byte aligned. -/
theorem selfBalanceOff_align : selfBalanceOff % 32 = 0 := by decide
/-- `callerOff` is 32-byte aligned. -/
theorem callerOff_align : callerOff % 32 = 0 := by decide
/-- `callValueOff` is 32-byte aligned. -/
theorem callValueOff_align : callValueOff % 32 = 0 := by decide
/-- `txOriginOff` is 32-byte aligned. -/
theorem txOriginOff_align : txOriginOff % 32 = 0 := by decide
/-- `gasPriceOff` is 32-byte aligned. -/
theorem gasPriceOff_align : gasPriceOff % 32 = 0 := by decide
/-- `blockCoinbaseOff` is 32-byte aligned. -/
theorem blockCoinbaseOff_align : blockCoinbaseOff % 32 = 0 := by decide
/-- `blockTimestampOff` is 32-byte aligned. -/
theorem blockTimestampOff_align : blockTimestampOff % 32 = 0 := by decide
/-- `blockNumberOff` is 32-byte aligned. -/
theorem blockNumberOff_align : blockNumberOff % 32 = 0 := by decide
/-- `blockPrevrandaoOff` is 32-byte aligned. -/
theorem blockPrevrandaoOff_align : blockPrevrandaoOff % 32 = 0 := by decide
/-- `blockGasLimitOff` is 32-byte aligned. -/
theorem blockGasLimitOff_align : blockGasLimitOff % 32 = 0 := by decide
/-- `blockBaseFeeOff` is 32-byte aligned. -/
theorem blockBaseFeeOff_align : blockBaseFeeOff % 32 = 0 := by decide
/-- `chainIdOff` is 32-byte aligned. -/
theorem chainIdOff_align : chainIdOff % 32 = 0 := by decide

/-- `callDataPtrOff` is 8-byte aligned. -/
theorem callDataPtrOff_align : callDataPtrOff % 8 = 0 := by decide
/-- `callDataLenOff` is 8-byte aligned. -/
theorem callDataLenOff_align : callDataLenOff % 8 = 0 := by decide
/-- `returnDataPtrOff` is 8-byte aligned. -/
theorem returnDataPtrOff_align : returnDataPtrOff % 8 = 0 := by decide
/-- `returnDataSizeOff` is 8-byte aligned. -/
theorem returnDataSizeOff_align : returnDataSizeOff % 8 = 0 := by decide

/-- `envSize` matches `13 * 32 + 4 * 8`. -/
theorem envSize_eq : envSize = 13 * 32 + 4 * 8 := by decide

/-- Every 32-byte field's slot ends at the next 32-byte field's start;
    all 8-byte fields then tail without gap up to `envSize`.  This is
    proved as a single concrete decidable fact: the disjoint union of
    every named slot exactly fills `[0, envSize)`. -/
theorem envSize_covers :
    addressOff + 32 = selfBalanceOff ∧
    selfBalanceOff + 32 = callerOff ∧
    callerOff + 32 = callValueOff ∧
    callValueOff + 32 = txOriginOff ∧
    txOriginOff + 32 = gasPriceOff ∧
    gasPriceOff + 32 = blockCoinbaseOff ∧
    blockCoinbaseOff + 32 = blockTimestampOff ∧
    blockTimestampOff + 32 = blockNumberOff ∧
    blockNumberOff + 32 = blockPrevrandaoOff ∧
    blockPrevrandaoOff + 32 = blockGasLimitOff ∧
    blockGasLimitOff + 32 = blockBaseFeeOff ∧
    blockBaseFeeOff + 32 = chainIdOff ∧
    chainIdOff + 32 = callDataPtrOff ∧
    callDataPtrOff + 8 = callDataLenOff ∧
    callDataLenOff + 8 = returnDataPtrOff ∧
    returnDataPtrOff + 8 = returnDataSizeOff ∧
    returnDataSizeOff + 8 = envSize := by decide

end EvmEnv
end EvmAsm.Evm64
