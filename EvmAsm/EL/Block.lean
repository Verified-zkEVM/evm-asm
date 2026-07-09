/-
  EvmAsm.EL.Block

  Pure block transition surface for GH #124. This layer is intentionally
  parameterized by the transaction executor so it can connect to the executable
  EVM/interpreter relation as that surface lands.
-/

import EvmAsm.EL.TransactionCall

namespace EvmAsm.EL

/-- Header fields needed by the first block-transition layer. -/
structure BlockHeader where
  parentHash : Hash256
  beneficiary : Address
  stateRoot : Hash256
  transactionsRoot : Hash256
  receiptsRoot : Hash256
  gasLimit : Nat
  baseFee : Nat
  number : Nat
  timestamp : Nat
  prevRandao : Hash256
  deriving Repr

/-- Coarse result for one transaction in the block fold. -/
inductive BlockTransactionStatus where
  | executed
  | createUnsupported
  deriving DecidableEq, Repr

/-- Per-transaction trace item exposed by the block transition fold. -/
structure BlockTransactionResult where
  status : BlockTransactionStatus
  transaction : Transaction
  callFrame? : Option CallFrame
  callResult? : Option CallResult
  state : WorldState
  gasRemaining : Nat

/-- Accumulator threaded through the ordered transaction list. -/
structure BlockAccumulator where
  state : WorldState
  gasRemaining : Nat
  transactionResults : List BlockTransactionResult

/-- Final block-transition result, with the candidate post-state root kept as a hook. -/
structure BlockResult where
  finalState : WorldState
  gasRemaining : Nat
  transactionResults : List BlockTransactionResult
  stateRoot : Hash256

namespace BlockTransition

end BlockTransition

end EvmAsm.EL
