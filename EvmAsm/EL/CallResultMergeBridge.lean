/-
  EvmAsm.EL.CallResultMergeBridge

  Pure CALL-family parent/child merge facts.
-/

import EvmAsm.EL.CallPrecheck

namespace EvmAsm.EL

namespace CallResultMergeBridge

abbrev CallExecutionInput := MessageCallExecution.CallExecutionInput
abbrev CallerVisibleResult := MessageCallExecution.CallerVisibleResult
abbrev CallResult := EvmAsm.EL.CallResult
abbrev Byte := EvmAsm.EL.Byte

/-- Parent-visible merge of a child call result. Successful child frames commit
    their state and returndata; REVERT restores the parent state while preserving
    returndata; failure restores parent state and exposes empty returndata. -/
def mergeChildResult (input : CallExecutionInput) (result : CallResult) :
    CallerVisibleResult :=
  MessageCallExecution.toCallerVisible input result

/-- Execute outcome for the CALL precheck surface, delegating to the supplied
    child result only when the precheck chose `.execute`. The static-context
    exceptional branch has no caller-visible result; concrete handlers map it to
    an execution error before this merge layer. -/
def mergePrecheckResult (input : CallPrecheck.Input) (childResult : CallResult) :
    Option CallerVisibleResult :=
  match CallPrecheck.decide input with
  | .writeInStaticContext => none
  | .zeroResult => some (mergeChildResult (CallPrecheck.executionInput input)
      (CallPrecheck.zeroResult input))
  | .execute => some (mergeChildResult (CallPrecheck.executionInput input) childResult)

@[simp] theorem mergeChildResult_status
    (input : CallExecutionInput) (result : CallResult) :
    (mergeChildResult input result).status = result.status := rfl

@[simp] theorem mergeChildResult_state
    (input : CallExecutionInput) (result : CallResult) :
    (mergeChildResult input result).state =
      MessageCallExecution.committedState input result := rfl

@[simp] theorem mergeChildResult_output
    (input : CallExecutionInput) (result : CallResult) :
    (mergeChildResult input result).output =
      MessageCallExecution.propagatedOutput result := rfl

@[simp] theorem mergeChildResult_gasRemaining
    (input : CallExecutionInput) (result : CallResult) :
    (mergeChildResult input result).gasRemaining = result.gasRemaining := rfl

/-- Success commits the child state and propagates child returndata. -/
theorem mergeChildResult_success
    (input : CallExecutionInput)
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    mergeChildResult input
        { status := .success, state := state, output := output, gasRemaining := gasRemaining } =
      { status := .success, state := state, output := output, gasRemaining := gasRemaining } :=
  rfl

/-- REVERT restores the pre-call parent state while preserving returndata. -/
theorem mergeChildResult_revert
    (input : CallExecutionInput)
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    mergeChildResult input
        { status := .revert, state := state, output := output, gasRemaining := gasRemaining } =
      { status := .revert, state := input.state, output := output, gasRemaining := gasRemaining } :=
  rfl

/-- Failure restores the pre-call parent state and exposes empty returndata. -/
theorem mergeChildResult_failure
    (input : CallExecutionInput)
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    mergeChildResult input
        { status := .failure, state := state, output := output, gasRemaining := gasRemaining } =
      { status := .failure, state := input.state, output := [], gasRemaining := gasRemaining } :=
  rfl

/-- The caller-visible merge preserves the child gas bound obligation. -/
theorem mergeChildResult_gas_le_frame
    {input : CallExecutionInput} {result : CallResult}
    (h_gas : MessageCallExecution.callGasBounded input result) :
    (mergeChildResult input result).gasRemaining ≤ input.frame.gas :=
  h_gas

theorem mergePrecheckResult_staticValueViolation
    {input : CallPrecheck.Input} {childResult : CallResult}
    (h_static : CallPrecheck.staticValueViolation input = true) :
    mergePrecheckResult input childResult = none := by
  simp [mergePrecheckResult, CallPrecheck.decide_staticValueViolation h_static]

theorem mergePrecheckResult_depthOverflow
    {input : CallPrecheck.Input} {childResult : CallResult}
    (h_static : CallPrecheck.staticValueViolation input = false)
    (h_depth : input.depth + 1 > CallPrecheck.stackDepthLimit) :
    mergePrecheckResult input childResult =
      some (mergeChildResult (CallPrecheck.executionInput input)
        (CallPrecheck.zeroResult input)) := by
  simp [mergePrecheckResult, CallPrecheck.decide_depthOverflow h_static h_depth]

theorem mergePrecheckResult_insufficientBalance
    {input : CallPrecheck.Input} {childResult : CallResult}
    (h_static : CallPrecheck.staticValueViolation input = false)
    (h_depth : ¬ input.depth + 1 > CallPrecheck.stackDepthLimit)
    (h_balance : input.caller.balance.toNat < input.frame.transferredValue.toNat) :
    mergePrecheckResult input childResult =
      some (mergeChildResult (CallPrecheck.executionInput input)
        (CallPrecheck.zeroResult input)) := by
  simp [mergePrecheckResult,
    CallPrecheck.decide_insufficientBalance h_static h_depth h_balance]

theorem mergePrecheckResult_execute
    {input : CallPrecheck.Input} {childResult : CallResult}
    (h_static : CallPrecheck.staticValueViolation input = false)
    (h_depth : ¬ input.depth + 1 > CallPrecheck.stackDepthLimit)
    (h_balance : ¬ input.caller.balance.toNat < input.frame.transferredValue.toNat) :
    mergePrecheckResult input childResult =
      some (mergeChildResult (CallPrecheck.executionInput input) childResult) := by
  simp [mergePrecheckResult, CallPrecheck.decide_execute h_static h_depth h_balance]

theorem mergePrecheckResult_zero_status
    {input : CallPrecheck.Input} {childResult : CallResult}
    (h_merge : mergePrecheckResult input childResult =
      some (mergeChildResult (CallPrecheck.executionInput input) (CallPrecheck.zeroResult input))) :
    ∃ visible, mergePrecheckResult input childResult = some visible ∧
      visible.status = .failure ∧ visible.output = [] ∧ visible.state = input.state := by
  refine ⟨mergeChildResult (CallPrecheck.executionInput input) (CallPrecheck.zeroResult input),
    h_merge, ?_⟩
  simp [mergeChildResult, CallPrecheck.zeroResult, CallPrecheck.executionInput,
    MessageCallExecution.toCallerVisible,
    MessageCallExecution.committedState,
    MessageCallExecution.propagatedOutput]

end CallResultMergeBridge

end EvmAsm.EL
