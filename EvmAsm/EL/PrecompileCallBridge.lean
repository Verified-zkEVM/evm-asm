/-
  EvmAsm.EL.PrecompileCallBridge

  Pure bridge from EVM precompile dispatch results to CALL-family
  caller-visible result and stack framing.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.CallStackBridge
import EvmAsm.EL.MessageCallExecution
import EvmAsm.Evm64.PrecompileDispatch

namespace EvmAsm.EL

namespace PrecompileCallBridge

abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult
abbrev PrecompileInput := EvmAsm.Evm64.PrecompileInput
abbrev PrecompileStatus := EvmAsm.Evm64.PrecompileStatus

/-- Convert a precompile dispatch result into the same result shape consumed by
    CALL-family stack and caller-visible bridges.

    Precompiles do not mutate world state in this pure surface. Successful
    precompiles expose their returndata; failed precompiles push zero and expose
    empty returndata. -/
def callResultFromPrecompile (state : WorldState) (result : PrecompileResult) :
    CallResult :=
  match result.status with
  | .success =>
      { status := .success
        state := state
        output := result.output
        gasRemaining := result.gasRemaining }
  | .failure =>
      { status := .failure
        state := state
        output := []
        gasRemaining := result.gasRemaining }

/-- Stack word pushed by CALL/STATICCALL after a precompile dispatch. -/
def stackResultFromPrecompile (result : PrecompileResult) : List Word256 :=
  CallStackBridge.callStackResult (callResultFromPrecompile WorldState.empty result)

/-- Caller-visible CALL result for a precompile dispatch. -/
def callerVisibleFromPrecompile
    (input : MessageCallExecution.CallExecutionInput) (result : PrecompileResult) :
    MessageCallExecution.CallerVisibleResult :=
  MessageCallExecution.toCallerVisible input
    (callResultFromPrecompile input.state result)

/-- Try known-cost precompile dispatch for a CALL-family frame. `none` means
    either the callee is not an active precompile address or the precompile needs
    payload-specific dispatch supplied by a later bridge. -/
def attemptKnownCostPrecompileCall
    (input : MessageCallExecution.CallExecutionInput) (out : List Byte) :
    Option CallResult :=
  match EvmAsm.Evm64.PrecompileDispatch.dispatchAddress?
      input.frame.callee input.frame.caller input.frame.input out input.frame.gas with
  | none => none
  | some result => some (callResultFromPrecompile input.state result)

/-- Caller-visible wrapper for `attemptKnownCostPrecompileCall`. -/
def attemptKnownCostPrecompileVisible
    (input : MessageCallExecution.CallExecutionInput) (out : List Byte) :
    Option MessageCallExecution.CallerVisibleResult :=
  (attemptKnownCostPrecompileCall input out).map
    (MessageCallExecution.toCallerVisible input)

theorem callResultFromPrecompile_success
    (state : WorldState) (out : List Byte) (gasRemaining : Nat) :
    callResultFromPrecompile state (EvmAsm.Evm64.PrecompileResult.ok out gasRemaining) =
      { status := .success
        state := state
        output := out
        gasRemaining := gasRemaining } := rfl

theorem callResultFromPrecompile_failure
    (state : WorldState) (gasRemaining : Nat) :
    callResultFromPrecompile state (EvmAsm.Evm64.PrecompileResult.fail gasRemaining) =
      { status := .failure
        state := state
        output := []
        gasRemaining := gasRemaining } := rfl

theorem stackResultFromPrecompile_success
    (out : List Byte) (gasRemaining : Nat) :
    stackResultFromPrecompile (EvmAsm.Evm64.PrecompileResult.ok out gasRemaining) = [1] := rfl

theorem stackResultFromPrecompile_failure (gasRemaining : Nat) :
    stackResultFromPrecompile (EvmAsm.Evm64.PrecompileResult.fail gasRemaining) = [0] := rfl

theorem callerVisibleFromPrecompile_success
    (input : MessageCallExecution.CallExecutionInput)
    (out : List Byte) (gasRemaining : Nat) :
    callerVisibleFromPrecompile input (EvmAsm.Evm64.PrecompileResult.ok out gasRemaining) =
      { status := .success
        state := input.state
        output := out
        gasRemaining := gasRemaining } := rfl

theorem callerVisibleFromPrecompile_failure
    (input : MessageCallExecution.CallExecutionInput) (gasRemaining : Nat) :
    callerVisibleFromPrecompile input (EvmAsm.Evm64.PrecompileResult.fail gasRemaining) =
      { status := .failure
        state := input.state
        output := []
        gasRemaining := gasRemaining } := rfl

theorem attemptKnownCostPrecompileCall_none_of_dispatch_none
    {input : MessageCallExecution.CallExecutionInput} {out : List Byte}
    (h_dispatch : EvmAsm.Evm64.PrecompileDispatch.dispatchAddress?
      input.frame.callee input.frame.caller input.frame.input out input.frame.gas = none) :
    attemptKnownCostPrecompileCall input out = none := by
  simp [attemptKnownCostPrecompileCall, h_dispatch]

theorem attemptKnownCostPrecompileCall_some_of_dispatch_some
    {input : MessageCallExecution.CallExecutionInput} {out : List Byte}
    {result : PrecompileResult}
    (h_dispatch : EvmAsm.Evm64.PrecompileDispatch.dispatchAddress?
      input.frame.callee input.frame.caller input.frame.input out input.frame.gas =
        some result) :
    attemptKnownCostPrecompileCall input out =
      some (callResultFromPrecompile input.state result) := by
  simp [attemptKnownCostPrecompileCall, h_dispatch]

theorem attemptKnownCostPrecompileCall_none_non_precompile
    {input : MessageCallExecution.CallExecutionInput} {out : List Byte}
    (h_decode : EvmAsm.Evm64.PrecompileDispatch.decode? input.frame.callee = none) :
    attemptKnownCostPrecompileCall input out = none := by
  apply attemptKnownCostPrecompileCall_none_of_dispatch_none
  exact EvmAsm.Evm64.PrecompileDispatch.dispatchAddress?_none_of_decode?_none h_decode

theorem attemptKnownCostPrecompileCall_none_zero_callee
    (input : MessageCallExecution.CallExecutionInput) (out : List Byte)
    (h_callee : input.frame.callee = 0) :
    attemptKnownCostPrecompileCall input out = none := by
  apply attemptKnownCostPrecompileCall_none_non_precompile
  rw [h_callee]
  exact EvmAsm.Evm64.PrecompileDispatch.decode?_zero

theorem attemptKnownCostPrecompileCall_address
    (input : MessageCallExecution.CallExecutionInput)
    (target : EvmAsm.Evm64.Precompile) (out : List Byte)
    (h_callee : input.frame.callee = target.address) :
    attemptKnownCostPrecompileCall input out =
      (EvmAsm.Evm64.PrecompileDispatch.dispatch?
        { target := target
          caller := input.frame.caller
          input := input.frame.input
          gas := input.frame.gas }
        out).map (callResultFromPrecompile input.state) := by
  unfold attemptKnownCostPrecompileCall
  rw [h_callee]
  rw [EvmAsm.Evm64.PrecompileDispatch.dispatchAddress?_address target]
  cases EvmAsm.Evm64.PrecompileDispatch.dispatch?
      { target := target
        caller := input.frame.caller
        input := input.frame.input
        gas := input.frame.gas }
      out <;> rfl

theorem attemptKnownCostPrecompileCall_knownCost_success
    {input : MessageCallExecution.CallExecutionInput} {out : List Byte} {cost : Nat}
    (h_decode : EvmAsm.Evm64.PrecompileDispatch.decode? input.frame.callee = some target)
    (h_cost : EvmAsm.Evm64.Precompile.precompileGasCost?
      target input.frame.input.length = some cost)
    (h_gas : cost ≤ input.frame.gas) :
    attemptKnownCostPrecompileCall input out =
      some
        { status := .success
          state := input.state
          output := out
          gasRemaining := input.frame.gas - cost } := by
  have h_dispatch : EvmAsm.Evm64.PrecompileDispatch.dispatchAddress?
      input.frame.callee input.frame.caller input.frame.input out input.frame.gas =
        some (EvmAsm.Evm64.PrecompileResult.ok out (input.frame.gas - cost)) := by
    unfold EvmAsm.Evm64.PrecompileDispatch.dispatchAddress?
    rw [h_decode]
    exact EvmAsm.Evm64.PrecompileDispatch.dispatch?_ok_of_gasCost?_le h_cost h_gas
  simpa [callResultFromPrecompile] using
    attemptKnownCostPrecompileCall_some_of_dispatch_some h_dispatch

theorem attemptKnownCostPrecompileCall_knownCost_failure
    {input : MessageCallExecution.CallExecutionInput} {out : List Byte} {cost : Nat}
    (h_decode : EvmAsm.Evm64.PrecompileDispatch.decode? input.frame.callee = some target)
    (h_cost : EvmAsm.Evm64.Precompile.precompileGasCost?
      target input.frame.input.length = some cost)
    (h_gas : input.frame.gas < cost) :
    attemptKnownCostPrecompileCall input out =
      some
        { status := .failure
          state := input.state
          output := []
          gasRemaining := input.frame.gas } := by
  have h_dispatch : EvmAsm.Evm64.PrecompileDispatch.dispatchAddress?
      input.frame.callee input.frame.caller input.frame.input out input.frame.gas =
        some (EvmAsm.Evm64.PrecompileResult.fail input.frame.gas) := by
    unfold EvmAsm.Evm64.PrecompileDispatch.dispatchAddress?
    rw [h_decode]
    exact EvmAsm.Evm64.PrecompileDispatch.dispatch?_fail_of_gasCost?_gt h_cost h_gas
  simpa [callResultFromPrecompile] using
    attemptKnownCostPrecompileCall_some_of_dispatch_some h_dispatch

theorem attemptKnownCostPrecompileCall_none_payloadDependent
    {input : MessageCallExecution.CallExecutionInput} {out : List Byte}
    (h_decode : EvmAsm.Evm64.PrecompileDispatch.decode? input.frame.callee = some target)
    (h_cost : EvmAsm.Evm64.Precompile.precompileGasCost?
      target input.frame.input.length = none) :
    attemptKnownCostPrecompileCall input out = none := by
  apply attemptKnownCostPrecompileCall_none_of_dispatch_none
  unfold EvmAsm.Evm64.PrecompileDispatch.dispatchAddress?
  rw [h_decode]
  apply EvmAsm.Evm64.PrecompileDispatch.dispatch?_none_of_gasCost?_none
  exact h_cost

theorem attemptKnownCostPrecompileCall_gasBound
    {input : MessageCallExecution.CallExecutionInput} {out : List Byte}
    {result : CallResult}
    (h_attempt : attemptKnownCostPrecompileCall input out = some result) :
    result.gasRemaining ≤ input.frame.gas := by
  unfold attemptKnownCostPrecompileCall at h_attempt
  cases h_dispatch : EvmAsm.Evm64.PrecompileDispatch.dispatchAddress?
      input.frame.callee input.frame.caller input.frame.input out input.frame.gas with
  | none =>
      simp [h_dispatch] at h_attempt
  | some precompileResult =>
      simp [h_dispatch] at h_attempt
      rw [← h_attempt]
      cases precompileResult with
      | mk status output gasRemaining =>
          cases status <;> simp [callResultFromPrecompile]
          all_goals
            exact EvmAsm.Evm64.PrecompileDispatch.dispatchAddress?_preservesGasBound h_dispatch

theorem attemptKnownCostPrecompileVisible_some_of_call_some
    {input : MessageCallExecution.CallExecutionInput} {out : List Byte}
    {result : CallResult}
    (h_attempt : attemptKnownCostPrecompileCall input out = some result) :
    attemptKnownCostPrecompileVisible input out =
      some (MessageCallExecution.toCallerVisible input result) := by
  simp [attemptKnownCostPrecompileVisible, h_attempt]

end PrecompileCallBridge

end EvmAsm.EL
