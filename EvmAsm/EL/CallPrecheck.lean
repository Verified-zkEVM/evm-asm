/-
  EvmAsm.EL.CallPrecheck

  Pure CALL-family precheck outcome surface.
-/

import EvmAsm.EL.CallResultEffectsBridge
import EvmAsm.EL.WorldStateAccount

namespace EvmAsm.EL

namespace CallPrecheck

/-- EVM maximum child call/create depth from execution-specs `STACK_DEPTH_LIMIT`. -/
def stackDepthLimit : Nat := 1024

/-- Value-transfer stipend from execution-specs `GasCosts.CALL_STIPEND`. -/
def callStipend : Nat := 2300

/-- Account metadata read by the CALL precheck layer. -/
structure CallerAccountView where
  balance : Word256
  deriving Repr

namespace CallerAccountView

def fromAccount (account : Account) : CallerAccountView :=
  { balance := account.balance }

def fromState (state : WorldState) (caller : Address) : CallerAccountView :=
  match WorldState.getAccount state caller with
  | some account => fromAccount account
  | none => fromAccount Account.empty

@[simp] theorem fromAccount_balance (account : Account) :
    (fromAccount account).balance = account.balance := rfl

theorem fromState_of_getAccount_some
    {state : WorldState} {caller : Address} {account : Account}
    (h_account : WorldState.getAccount state caller = some account) :
    fromState state caller = fromAccount account := by
  simp [fromState, h_account]

theorem fromState_of_getAccount_none
    {state : WorldState} {caller : Address}
    (h_account : WorldState.getAccount state caller = none) :
    fromState state caller = fromAccount Account.empty := by
  simp [fromState, h_account]

end CallerAccountView

/--
Inputs known after stack decoding, memory expansion/access accounting, and
code lookup, but before child execution. `calleeExists` and `calleeWarm` are
explicit hooks for account-existence and access-list plumbing; `subCallGas`
is the already-capped child gas from the gas layer.
-/
structure Input where
  state : WorldState
  frame : CallFrame
  depth : Nat
  caller : CallerAccountView
  calleeExists : Bool
  calleeWarm : Bool
  subCallGas : Nat

def inputFromState
    (state : WorldState) (frame : CallFrame) (depth : Nat)
    (calleeExists calleeWarm : Bool) (subCallGas : Nat) : Input :=
  { state := state
    frame := frame
    depth := depth
    caller := CallerAccountView.fromState state frame.caller
    calleeExists := calleeExists
    calleeWarm := calleeWarm
    subCallGas := subCallGas }

def transfersValue (frame : CallFrame) : Bool :=
  frame.transferredValue != 0

def staticValueViolation (input : Input) : Bool :=
  input.frame.kind = .call && input.frame.isStatic && transfersValue input.frame

def depthOverflow (input : Input) : Prop :=
  input.depth + 1 > stackDepthLimit

def insufficientBalance (input : Input) : Prop :=
  input.caller.balance.toNat < input.frame.transferredValue.toNat

def stipendEligible (input : Input) : Bool :=
  transfersValue input.frame

def childGasWithStipend (input : Input) : Nat :=
  input.subCallGas + if stipendEligible input then callStipend else 0

/-- High-level branch taken before CALL-family child execution. -/
inductive Outcome where
  | writeInStaticContext
  | zeroResult
  | execute
  deriving DecidableEq, Repr

def decide (input : Input) : Outcome :=
  if staticValueViolation input then
    .writeInStaticContext
  else if input.depth + 1 > stackDepthLimit then
    .zeroResult
  else if input.caller.balance.toNat < input.frame.transferredValue.toNat then
    .zeroResult
  else
    .execute

def zeroResult (input : Input) : CallResult :=
  { status := .failure
    state := input.state
    output := []
    gasRemaining := input.frame.gas }

def executionInput (input : Input) : MessageCallExecution.CallExecutionInput :=
  { state := input.state
    frame := { input.frame with gas := childGasWithStipend input } }

theorem transfersValue_iff (frame : CallFrame) :
    transfersValue frame = true ↔ frame.transferredValue ≠ 0 := by
  simp [transfersValue]

theorem transfersValue_forStaticCall
    (caller callee : Address) (inputBytes : List Byte) (gas : Nat) :
    transfersValue (CallFrame.forStaticCall caller callee inputBytes gas) = false := rfl

theorem transfersValue_forDelegateCall
    (caller callee : Address) (apparentValue : Word256) (inputBytes : List Byte)
    (gas : Nat) (isStatic : Bool) :
    transfersValue
      (CallFrame.forDelegateCall caller callee apparentValue inputBytes gas isStatic) = false := rfl

theorem staticValueViolation_call
    (caller callee : Address) (value : Word256) (inputBytes : List Byte)
    (gas : Nat) (h_value : value ≠ 0) :
    staticValueViolation
      { state := WorldState.empty
        frame := CallFrame.forCall caller callee value inputBytes gas true
        depth := 0
        caller := CallerAccountView.fromAccount Account.empty
        calleeExists := false
        calleeWarm := false
        subCallGas := gas } = true := by
  by_cases h_zero : value = 0
  · exact False.elim (h_value h_zero)
  · simp [staticValueViolation, transfersValue]
    exact ⟨⟨rfl, rfl⟩, h_zero⟩

theorem staticValueViolation_staticCall
    (state : WorldState) (caller callee : Address) (inputBytes : List Byte)
    (gas depth subCallGas : Nat) (calleeExists calleeWarm : Bool)
    (callerView : CallerAccountView) :
    staticValueViolation
      { state := state
        frame := CallFrame.forStaticCall caller callee inputBytes gas
        depth := depth
        caller := callerView
        calleeExists := calleeExists
        calleeWarm := calleeWarm
        subCallGas := subCallGas } = false := rfl

theorem inputFromState_caller
    (state : WorldState) (frame : CallFrame) (depth : Nat)
    (calleeExists calleeWarm : Bool) (subCallGas : Nat) :
    (inputFromState state frame depth calleeExists calleeWarm subCallGas).caller =
      CallerAccountView.fromState state frame.caller := rfl

theorem inputFromState_frame
    (state : WorldState) (frame : CallFrame) (depth : Nat)
    (calleeExists calleeWarm : Bool) (subCallGas : Nat) :
    (inputFromState state frame depth calleeExists calleeWarm subCallGas).frame = frame := rfl

theorem stipendEligible_iff (input : Input) :
    stipendEligible input = true ↔ input.frame.transferredValue ≠ 0 := by
  exact transfersValue_iff input.frame

theorem childGasWithStipend_noValue
    {input : Input} (h_value : input.frame.transferredValue = 0) :
    childGasWithStipend input = input.subCallGas := by
  simp [childGasWithStipend, stipendEligible, transfersValue, h_value]

theorem childGasWithStipend_value
    {input : Input} (h_value : input.frame.transferredValue ≠ 0) :
    childGasWithStipend input = input.subCallGas + callStipend := by
  by_cases h_zero : input.frame.transferredValue = 0
  · exact False.elim (h_value h_zero)
  · simp [childGasWithStipend, stipendEligible, transfersValue]
    intro h_zero'
    exact False.elim (h_zero h_zero')

theorem decide_staticValueViolation
    {input : Input} (h_static : staticValueViolation input = true) :
    decide input = .writeInStaticContext := by
  simp [decide, h_static]

theorem decide_depthOverflow
    {input : Input} (h_static : staticValueViolation input = false)
    (h_depth : input.depth + 1 > stackDepthLimit) :
    decide input = .zeroResult := by
  simp [decide, h_static, h_depth]

theorem decide_insufficientBalance
    {input : Input} (h_static : staticValueViolation input = false)
    (h_depth : ¬ input.depth + 1 > stackDepthLimit)
    (h_balance : input.caller.balance.toNat < input.frame.transferredValue.toNat) :
    decide input = .zeroResult := by
  simp [decide, h_static, h_depth, h_balance]

theorem decide_execute
    {input : Input} (h_static : staticValueViolation input = false)
    (h_depth : ¬ input.depth + 1 > stackDepthLimit)
    (h_balance : ¬ input.caller.balance.toNat < input.frame.transferredValue.toNat) :
    decide input = .execute := by
  simp [decide, h_static, h_depth, h_balance]

theorem zeroResult_status (input : Input) :
    (zeroResult input).status = .failure := rfl

theorem zeroResult_state (input : Input) :
    (zeroResult input).state = input.state := rfl

theorem zeroResult_output (input : Input) :
    (zeroResult input).output = [] := rfl

theorem zeroResult_stack_head_eq_zero
    (input : Input) (outputRange : EvmAsm.Evm64.CallArgs.MemoryRange) :
    (CallResultEffectsBridge.callVisibleEffects (zeroResult input) outputRange).stackWords.head? =
      some 0 := by
  simp [zeroResult, CallResultEffectsBridge.callVisibleEffects_failure]

theorem executionInput_state (input : Input) :
    (executionInput input).state = input.state := rfl

theorem executionInput_frame_gas (input : Input) :
    (executionInput input).frame.gas = childGasWithStipend input := rfl

theorem executionInput_frame_kind (input : Input) :
    (executionInput input).frame.kind = input.frame.kind := rfl

theorem executionInput_frame_callee (input : Input) :
    (executionInput input).frame.callee = input.frame.callee := rfl

theorem executionInput_preserves_static (input : Input) :
    (executionInput input).frame.isStatic = input.frame.isStatic := rfl

end CallPrecheck

end EvmAsm.EL
