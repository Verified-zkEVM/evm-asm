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

/-- Pure block input: an initial world state plus the ordered transaction list. -/
structure BlockInput where
  header : BlockHeader
  initialState : WorldState
  transactions : List Transaction

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

/-- Abstract execution hook for ordinary message-call transactions. -/
abbrev TransactionExecutor := WorldState → CallFrame → CallResult

namespace BlockTransition

def initialAccumulator (input : BlockInput) : BlockAccumulator :=
  { state := input.initialState
    gasRemaining := input.header.gasLimit
    transactionResults := [] }

/-- Execute one transaction-shaped call when it has a call frame. CREATE-family
    transactions are recorded but left to the CREATE/CREATE2 surface. -/
def applyTransaction
    (executor : TransactionExecutor) (acc : BlockAccumulator) (tx : Transaction) :
    BlockAccumulator :=
  match tx.toCallFrame? with
  | none =>
      { acc with
        transactionResults :=
          acc.transactionResults ++
            [{ status := .createUnsupported
               transaction := tx
               callFrame? := none
               callResult? := none
               state := acc.state
               gasRemaining := acc.gasRemaining }] }
  | some frame =>
      let result := executor acc.state frame
      { state := result.state
        gasRemaining := result.gasRemaining
        transactionResults :=
          acc.transactionResults ++
            [{ status := .executed
               transaction := tx
               callFrame? := some frame
               callResult? := some result
               state := result.state
               gasRemaining := result.gasRemaining }] }

/-- Ordered transaction-list fold for the block transition surface. -/
def applyTransactions
    (executor : TransactionExecutor) (acc : BlockAccumulator) (txs : List Transaction) :
    BlockAccumulator :=
  txs.foldl (applyTransaction executor) acc

def run (executor : TransactionExecutor) (input : BlockInput) : BlockResult :=
  let acc := applyTransactions executor (initialAccumulator input) input.transactions
  { finalState := acc.state
    gasRemaining := acc.gasRemaining
    transactionResults := acc.transactionResults
    stateRoot := input.header.stateRoot }

/-- Hook connecting the final state to the block header's state-root commitment. -/
def StateRootRelation := WorldState → Hash256 → Prop

def stateRootMatches (rel : StateRootRelation) (result : BlockResult) : Prop :=
  rel result.finalState result.stateRoot

theorem applyTransactions_nil (executor : TransactionExecutor) (acc : BlockAccumulator) :
    applyTransactions executor acc [] = acc := rfl

theorem applyTransactions_cons
    (executor : TransactionExecutor) (acc : BlockAccumulator)
    (tx : Transaction) (txs : List Transaction) :
    applyTransactions executor acc (tx :: txs) =
      applyTransactions executor (applyTransaction executor acc tx) txs := rfl

theorem run_nil_finalState (executor : TransactionExecutor) (input : BlockInput)
    (h_txs : input.transactions = []) :
    (run executor input).finalState = input.initialState := by
  simp [run, applyTransactions, initialAccumulator, h_txs]

theorem stateRootMatches_iff
    (rel : StateRootRelation) (result : BlockResult) :
    stateRootMatches rel result ↔ rel result.finalState result.stateRoot := Iff.rfl

end BlockTransition

end EvmAsm.EL
