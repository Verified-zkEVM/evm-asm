/-
  EvmAsm.EL.SelfdestructEffects

  Pure SELFDESTRUCT post-Cancun side-effect bridge (GH #113).
-/

import EvmAsm.EL.CallValueTransfer
import EvmAsm.EL.CreatedAccounts
import EvmAsm.EL.MessageCallExecution

namespace EvmAsm.EL

namespace SelfdestructEffects

abbrev CallSideEffects := MessageCallExecution.CallSideEffects

/-- Pure result surface for SELFDESTRUCT state and side effects. -/
structure SelfdestructEffect where
  state : WorldState
  sideEffects : CallSideEffects

/-- Convert a pure SELFDESTRUCT effect into a message-call result. The status
    decides whether the caller-visible layer commits the state/effects or
    restores/clears them. -/
def callResultFromEffect
    (effect : SelfdestructEffect) (status : CallStatus) (gasRemaining : Nat) :
    CallResult :=
  { status := status
    state := effect.state
    output := []
    gasRemaining := gasRemaining }

end SelfdestructEffects

end EvmAsm.EL
