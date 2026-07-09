/-
  EvmAsm.EL.MessageCall

  Pure message-call frame and result surface for GH #121.
-/

import EvmAsm.EL.WorldState

namespace EvmAsm.EL

/-- CALL-family variants modeled by the first message-call layer. -/
inductive CallKind where
  | call
  | staticcall
  | delegatecall
  deriving DecidableEq, Repr

namespace CallKind

/-- Whether the call kind transfers value from caller to callee. -/
def transfersValue : CallKind → Bool
  | call => true
  | staticcall => false
  | delegatecall => false

/-- Whether the callee is allowed to write state in this call mode. -/
def mayWriteState : CallKind → Bool
  | call => true
  | staticcall => false
  | delegatecall => true

/-- Whether execution preserves the caller/value context from the parent frame. -/
def preservesCallerContext : CallKind → Bool
  | call => false
  | staticcall => false
  | delegatecall => true

theorem transfersValue_call : transfersValue call = true := rfl
theorem transfersValue_staticcall : transfersValue staticcall = false := rfl
theorem transfersValue_delegatecall : transfersValue delegatecall = false := rfl

theorem mayWriteState_staticcall : mayWriteState staticcall = false := rfl
theorem preservesCallerContext_delegatecall : preservesCallerContext delegatecall = true := rfl

end CallKind

/-- Pure input frame for one message-call execution. -/
structure CallFrame where
  kind : CallKind
  caller : Address
  callee : Address
  apparentValue : Word256
  transferredValue : Word256
  input : List Byte
  gas : Nat
  isStatic : Bool
  deriving Repr

namespace CallFrame

/-- CALL frame: value is both apparent to the callee and transferred. -/
def forCall
    (caller callee : Address) (value : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) : CallFrame :=
  { kind := .call
    caller := caller
    callee := callee
    apparentValue := value
    transferredValue := value
    input := input
    gas := gas
    isStatic := isStatic }

/-- STATICCALL frame: no value transfer and state writes are forbidden. -/
def forStaticCall
    (caller callee : Address) (input : List Byte) (gas : Nat) : CallFrame :=
  { kind := .staticcall
    caller := caller
    callee := callee
    apparentValue := 0
    transferredValue := 0
    input := input
    gas := gas
    isStatic := true }

/-- DELEGATECALL frame: caller/value context is preserved and no value is transferred. -/
def forDelegateCall
    (caller callee : Address) (apparentValue : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) : CallFrame :=
  { kind := .delegatecall
    caller := caller
    callee := callee
    apparentValue := apparentValue
    transferredValue := 0
    input := input
    gas := gas
    isStatic := isStatic }

theorem transferredValue_forCall
    (caller callee : Address) (value : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) :
    (forCall caller callee value input gas isStatic).transferredValue = value := rfl

theorem transferredValue_forStaticCall
    (caller callee : Address) (input : List Byte) (gas : Nat) :
    (forStaticCall caller callee input gas).transferredValue = 0 := rfl

theorem transferredValue_forDelegateCall
    (caller callee : Address) (apparentValue : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) :
    (forDelegateCall caller callee apparentValue input gas isStatic).transferredValue = 0 := rfl

theorem isStatic_forStaticCall
    (caller callee : Address) (input : List Byte) (gas : Nat) :
    (forStaticCall caller callee input gas).isStatic = true := rfl

theorem kind_forDelegateCall
    (caller callee : Address) (apparentValue : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) :
    (forDelegateCall caller callee apparentValue input gas isStatic).kind = .delegatecall := rfl

end CallFrame

/-- Coarse result status for one message-call execution. -/
inductive CallStatus where
  | success
  | revert
  | failure
  deriving DecidableEq, Repr

namespace CallResult

end CallResult

end EvmAsm.EL
