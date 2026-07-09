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

@[simp] theorem fromAccount_balance (account : Account) :
    (fromAccount account).balance = account.balance := rfl

end CallerAccountView

def transfersValue (frame : CallFrame) : Bool :=
  frame.transferredValue != 0

/-- High-level branch taken before CALL-family child execution. -/
inductive Outcome where
  | writeInStaticContext
  | zeroResult
  | execute
  deriving DecidableEq, Repr

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

end CallPrecheck

end EvmAsm.EL
