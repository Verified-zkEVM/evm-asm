/-
  EvmAsm.EL.MessageCallExecution

  Pure execution hooks for message-call processing (GH #121).
-/

import EvmAsm.EL.Logs
import EvmAsm.EL.MessageCall

namespace EvmAsm.EL

namespace MessageCallExecution
/-- Side effects surfaced by the executable-spec `MessageCallOutput`. The
    output bytes and committed state remain in `CallResult`/`CallerVisibleResult`;
    this record tracks the auxiliary effects that are cleared on errors. -/
structure CallSideEffects where
  refundCounter : Nat
  logs : LogState
  accountsToDelete : List Address
  touchedAccounts : List Address

def empty : CallSideEffects :=
  { refundCounter := 0
    logs := LogState.empty
    accountsToDelete := []
    touchedAccounts := [] }

@[simp] theorem refundCounter_empty : empty.refundCounter = 0 := rfl
@[simp] theorem logs_empty : empty.logs = LogState.empty := rfl
@[simp] theorem accountsToDelete_empty : empty.accountsToDelete = [] := rfl
@[simp] theorem touchedAccounts_empty : empty.touchedAccounts = [] := rfl


/-- Executable-spec-shaped message-call output surface. Mirrors the Python
    `MessageCallOutput` fields while using `status` as the Lean error summary. -/
structure MessageCallOutput where
  gasLeft : Nat
  refundCounter : Nat
  logs : LogState
  accountsToDelete : List Address
  touchedAccounts : List Address
  status : CallStatus

end MessageCallExecution

end EvmAsm.EL
