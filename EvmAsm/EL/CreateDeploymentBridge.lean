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

theorem callerVisibleEffect_deployResult
    (created : CreatedAccounts.CreatedAccountSet)
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    callerVisibleEffect created
        (CreateEffects.deployResult state request address codeHash gasRemaining) =
      { stackWord := address.zeroExtend 256
        state :=
          WorldState.setAccount state address
            (CreateEffects.deployedAccount request codeHash)
        returndata := []
        gasRemaining := gasRemaining
        created := CreatedAccounts.markCreated created address } := rfl

theorem callerVisibleEffect_deployResult_account
    (created : CreatedAccounts.CreatedAccountSet)
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    WorldState.getAccount
        (callerVisibleEffect created
          (CreateEffects.deployResult state request address codeHash gasRemaining)).state
        address =
      some (CreateEffects.deployedAccount request codeHash) := by
  simpa [callerVisibleEffect] using
    CreateEffects.deployResultAccount state request address codeHash gasRemaining

theorem callerVisibleEffect_deployResult_code?
    (created : CreatedAccounts.CreatedAccountSet)
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    WorldState.accountCode?
        (callerVisibleEffect created
          (CreateEffects.deployResult state request address codeHash gasRemaining)).state
        address =
      some request.initcode := by
  simpa [callerVisibleEffect] using
    CreateEffects.deployResultCode? state request address codeHash gasRemaining

theorem callerVisibleEffect_deployResult_createdInSameTx
    (created : CreatedAccounts.CreatedAccountSet)
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    CreatedAccounts.createdInSameTx
        (callerVisibleEffect created
          (CreateEffects.deployResult state request address codeHash gasRemaining)).created
        address =
      true := by
  simp [callerVisibleEffect, CreateEffects.deployResult,
    CreatedAccounts.createdInSameTx, CreatedAccounts.markCreateResult,
    CreatedAccounts.contains_markCreated_self]

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
