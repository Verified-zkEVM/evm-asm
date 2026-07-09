/-
  EvmAsm.EL.CreateDeploymentBridge

  Caller-visible CREATE-family deployment effects: stack word, return data,
  gas, world-state result, and transaction-local created-account tracking.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.CreateEffects
import EvmAsm.EL.CreatedAccounts
import EvmAsm.EL.CreateResultBridge

namespace EvmAsm.EL

namespace CreateDeploymentBridge

/-- Caller-visible CREATE/CREATE2 result after child execution and code-deposit
    handling have already determined a `CreateResult`.

    This intentionally stays pure EL: concrete opcode handlers can compute a
    `CreateResult`, then use this structure as the single source for the stack
    return word, returndata, remaining gas, state, and EIP-6780 created marker. -/
structure CallerVisibleEffect where
  stackWord : Word256
  state : WorldState
  returndata : List Byte
  gasRemaining : Nat
  created : CreatedAccounts.CreatedAccountSet

/-- Project a CREATE-family result into caller-visible fields. -/
def callerVisibleEffect
    (created : CreatedAccounts.CreatedAccountSet) (result : CreateResult) :
    CallerVisibleEffect :=
  { stackWord := CreateResultBridge.createResultStackWord result
    state := result.state
    returndata := result.returndata
    gasRemaining := result.gasRemaining
    created := CreatedAccounts.markCreateResult created result }

/-- A canonical pure result for code-deposit failure: the child did not deploy
    code, pushes zero to the caller, returns no data, and leaves the created
    account set unchanged. -/
def codeDepositFailureResult (state : WorldState) (gasRemaining : Nat) :
    CreateResult :=
  { status := .failed
    address? := none
    state := state
    returndata := []
    gasRemaining := gasRemaining }

theorem callerVisibleEffect_reverted
    (created : CreatedAccounts.CreatedAccountSet) (address? : Option Address)
    (state : WorldState) (returndata : List Byte) (gasRemaining : Nat) :
    callerVisibleEffect created
        { status := .reverted
          address? := address?
          state := state
          returndata := returndata
          gasRemaining := gasRemaining } =
      { stackWord := 0
        state := state
        returndata := returndata
        gasRemaining := gasRemaining
        created := created } := by
  cases address? <;> rfl

theorem callerVisibleEffect_failed
    (created : CreatedAccounts.CreatedAccountSet) (address? : Option Address)
    (state : WorldState) (returndata : List Byte) (gasRemaining : Nat) :
    callerVisibleEffect created
        { status := .failed
          address? := address?
          state := state
          returndata := returndata
          gasRemaining := gasRemaining } =
      { stackWord := 0
        state := state
        returndata := returndata
        gasRemaining := gasRemaining
        created := created } := by
  cases address? <;> rfl

theorem callerVisibleEffect_codeDepositFailure
    (created : CreatedAccounts.CreatedAccountSet)
    (state : WorldState) (gasRemaining : Nat) :
    callerVisibleEffect created (codeDepositFailureResult state gasRemaining) =
      { stackWord := 0
        state := state
        returndata := []
        gasRemaining := gasRemaining
        created := created } := rfl

theorem codeDepositFailure_createdInSameTx
    (created : CreatedAccounts.CreatedAccountSet)
    (state : WorldState) (gasRemaining : Nat) (address : Address) :
    CreatedAccounts.createdInSameTx
        (callerVisibleEffect created
          (codeDepositFailureResult state gasRemaining)).created
        address =
      CreatedAccounts.createdInSameTx created address := rfl

end CreateDeploymentBridge

end EvmAsm.EL
