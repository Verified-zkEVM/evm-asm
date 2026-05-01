/-
  EvmAsm.Evm64.Environment

  Slice 1 of #100 (EVM environment context layout).

  This module defines the `EvmEnv` Lean structure that bundles every
  field of the EVM execution context (msg.*, block.*, tx.*, plus
  contract address / balance / returndata).

  Memory layout (offsets within an `envIs base env` block) and the
  `envIs` separation-logic assertion are deferred to slices 2 and 3
  respectively (#100 slices `evm-asm-2u94` / `evm-asm-3fr7`); this
  file only declares pure data so downstream slices have a stable
  Lean type to work against.

  Field types follow the existing 64-bit / 256-bit conventions:
  - All 256-bit EVM values use `EvmWord` (`BitVec 256`).
  - Ethereum addresses are 160-bit (`BitVec 160`); when stored in
    memory they will later be zero-extended to 256 bits, but at the
    structure level we keep the natural width.
  - Pointers and 64-bit-sized lengths use `Word` (`BitVec 64`).
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- A 160-bit Ethereum address (20 bytes). -/
abbrev Address := BitVec 160

/--
  Bundle of every EVM execution-context field read by the opcodes
  ADDRESS, BALANCE, ORIGIN, CALLER, CALLVALUE, CALLDATALOAD,
  CALLDATASIZE, CALLDATACOPY, GASPRICE, RETURNDATASIZE, COINBASE,
  TIMESTAMP, NUMBER, PREVRANDAO, GASLIMIT, CHAINID, SELFBALANCE,
  BASEFEE.

  Pointer-typed fields (`callDataPtr`, `returnDataPtr`) store the
  RISC-V memory address of the underlying byte buffer; their length
  partners (`callDataLen`, `returnDataSize`) hold the buffer size in
  bytes.  The actual bytes live elsewhere in the heap and are not
  part of `EvmEnv`.
-/
structure EvmEnv where
  /-- Address of the contract currently executing (ADDRESS). -/
  address       : Address
  /-- Native-token balance of `address` (SELFBALANCE). -/
  selfBalance   : EvmWord
  /-- Immediate sender of the current call (CALLER, msg.sender). -/
  caller        : Address
  /-- Wei sent with the current call (CALLVALUE, msg.value). -/
  callValue     : EvmWord
  /-- Memory pointer to the calldata buffer (msg.data). -/
  callDataPtr   : Word
  /-- Length of the calldata buffer in bytes (CALLDATASIZE). -/
  callDataLen   : Word
  /-- Memory pointer to the returndata buffer of the most recent
      sub-call. -/
  returnDataPtr : Word
  /-- Length of the returndata buffer in bytes (RETURNDATASIZE). -/
  returnDataSize : Word
  /-- Originating EOA of the transaction (ORIGIN, tx.origin). -/
  txOrigin      : Address
  /-- Effective gas price for the current transaction (GASPRICE). -/
  gasPrice      : EvmWord
  /-- Beneficiary of block rewards (COINBASE, block.coinbase). -/
  blockCoinbase : Address
  /-- Unix timestamp of the current block (TIMESTAMP). -/
  blockTimestamp : EvmWord
  /-- Height of the current block (NUMBER). -/
  blockNumber   : EvmWord
  /-- Mixed-hash from the beacon chain (PREVRANDAO; legacy
      DIFFICULTY pre-merge). -/
  blockPrevrandao : EvmWord
  /-- Gas limit of the current block (GASLIMIT). -/
  blockGasLimit : EvmWord
  /-- Base fee per gas of the current block (BASEFEE, EIP-1559). -/
  blockBaseFee  : EvmWord
  /-- EIP-155 chain identifier (CHAINID). -/
  chainId       : EvmWord
  deriving Repr

namespace EvmEnv

/-- Sanity check: structure type-checks and is non-empty.  We use a
    let-binding rather than an `instance Inhabited EvmEnv` so this
    file stays free of any further infrastructure commitments. -/
example : EvmEnv :=
  { address         := 0
    selfBalance     := 0
    caller          := 0
    callValue       := 0
    callDataPtr     := 0
    callDataLen     := 0
    returnDataPtr   := 0
    returnDataSize  := 0
    txOrigin        := 0
    gasPrice        := 0
    blockCoinbase   := 0
    blockTimestamp  := 0
    blockNumber     := 0
    blockPrevrandao := 0
    blockGasLimit   := 0
    blockBaseFee    := 0
    chainId         := 0 }

end EvmEnv

end EvmAsm.Evm64
