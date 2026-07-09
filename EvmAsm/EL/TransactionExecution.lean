/-
  EvmAsm.EL.TransactionExecution

  Pure transaction execution hooks for GH #122.
-/

import EvmAsm.EL.TransactionCall
import EvmAsm.EL.MessageCallExecution

namespace EvmAsm.EL

namespace TransactionExecution

/-- Inputs needed to run one already-validated transaction. -/
structure TransactionExecutionInput where
  state : WorldState
  tx : Transaction
  baseFee : Nat
  blockGasRemaining : Nat

/-- Caller-visible execution output for ordinary message-call transactions. -/
structure TransactionExecutionResult where
  status : CallStatus
  state : WorldState
  output : List Byte
  gasRemaining : Nat

def transactionCallerVisible
    (callInput : MessageCallExecution.CallExecutionInput) (callResult : CallResult) :
    TransactionExecutionResult :=
  let visible := MessageCallExecution.toCallerVisible callInput callResult
  { status := visible.status
    state := visible.state
    output := visible.output
    gasRemaining := visible.gasRemaining }

/-- Execute an ordinary transaction through the supplied message-call executor.
    Contract-creation transactions return `none` here and are handled by #115. -/
def execute? (executor : MessageCallExecution.CallExecutor)
    (input : TransactionExecutionInput) : Option TransactionExecutionResult :=
  match input.tx.toCallFrame? with
  | none => none
  | some frame =>
      let callInput : MessageCallExecution.CallExecutionInput :=
        { state := input.state, frame := frame }
      some (transactionCallerVisible callInput (executor callInput))

theorem execute?_create_none
    (executor : MessageCallExecution.CallExecutor) (input : TransactionExecutionInput)
    (h_to : input.tx.to = none) :
    execute? executor input = none := by
  simp [execute?, Transaction.toCallFrame?_create input.tx h_to]

theorem execute?_some_call
    (executor : MessageCallExecution.CallExecutor) (input : TransactionExecutionInput)
    {callee : Address} (h_to : input.tx.to = some callee) :
    execute? executor input =
      let frame := CallFrame.forCall input.tx.sender callee input.tx.value input.tx.data
        input.tx.gasLimit false
      let callInput : MessageCallExecution.CallExecutionInput :=
        { state := input.state, frame := frame }
      some (transactionCallerVisible callInput (executor callInput)) := by
  simp [execute?, Transaction.toCallFrame?_some input.tx h_to]

theorem transactionCallerVisible_status
    (callInput : MessageCallExecution.CallExecutionInput) (callResult : CallResult) :
    (transactionCallerVisible callInput callResult).status = callResult.status := rfl

theorem transactionCallerVisible_state
    (callInput : MessageCallExecution.CallExecutionInput) (callResult : CallResult) :
    (transactionCallerVisible callInput callResult).state =
      MessageCallExecution.committedState callInput callResult := rfl

theorem transactionCallerVisible_output
    (callInput : MessageCallExecution.CallExecutionInput) (callResult : CallResult) :
    (transactionCallerVisible callInput callResult).output =
      MessageCallExecution.propagatedOutput callResult := rfl

end TransactionExecution

end EvmAsm.EL
