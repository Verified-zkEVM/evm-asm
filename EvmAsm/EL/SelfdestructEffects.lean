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

/-- Post-Cancun SELFDESTRUCT transfers the account balance to the beneficiary
    and touches the beneficiary, but it does not schedule account deletion.
    Distinctive token: SelfdestructEffects.postCancunSelfdestructEffect. -/
def postCancunSelfdestructEffect
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) : SelfdestructEffect :=
  { state :=
      CallValueTransfer.transferValue
        state account beneficiary accountBalance beneficiaryBalance accountBalance
    sideEffects :=
      { refundCounter := 0
        logs := LogState.empty
        accountsToDelete := []
        touchedAccounts := [beneficiary] } }

theorem postCancunSelfdestructEffect_state
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).state =
      CallValueTransfer.transferValue
        state account beneficiary accountBalance beneficiaryBalance accountBalance := rfl

theorem postCancunSelfdestructEffect_refundCounter
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).sideEffects.refundCounter =
      0 := rfl

theorem postCancunSelfdestructEffect_logs
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).sideEffects.logs =
      LogState.empty := rfl

theorem postCancunSelfdestructEffect_accountsToDelete
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).sideEffects.accountsToDelete =
      [] := rfl

theorem postCancunSelfdestructEffect_touchedAccounts
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).sideEffects.touchedAccounts =
      [beneficiary] := rfl

theorem postCancunSelfdestructEffect_accountBalance?
    {state : WorldState} {account beneficiary : Address} {accountRecord : Account}
    (accountBalance beneficiaryBalance : Word256)
    (h_account : WorldState.getAccount state account = some accountRecord)
    (h_ne : account ≠ beneficiary) :
    WorldState.accountBalance?
        (postCancunSelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance).state
        account =
      some (accountBalance - accountBalance) := by
  rw [postCancunSelfdestructEffect_state]
  exact CallValueTransfer.transferValue_callerBalance?
    accountBalance beneficiaryBalance accountBalance h_account h_ne

theorem postCancunSelfdestructEffect_beneficiaryBalance?
    {state : WorldState} {account beneficiary : Address} {beneficiaryRecord : Account}
    (accountBalance beneficiaryBalance : Word256)
    (h_beneficiary : WorldState.getAccount state beneficiary = some beneficiaryRecord)
    (h_ne : account ≠ beneficiary) :
    WorldState.accountBalance?
        (postCancunSelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance).state
        beneficiary =
      some (beneficiaryBalance + accountBalance) := by
  rw [postCancunSelfdestructEffect_state]
  exact CallValueTransfer.transferValue_calleeBalance?
    accountBalance beneficiaryBalance accountBalance h_beneficiary h_ne

/-- EIP-6780 SELFDESTRUCT effect. Accounts created in the same transaction are
    still deleted; pre-existing accounts keep the post-Cancun transfer-only
    behavior exposed by `postCancunSelfdestructEffect`. -/
def eip6780SelfdestructEffect
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) (createdInSameTx : Bool) :
    SelfdestructEffect :=
  if createdInSameTx then
    let transferredState :=
      CallValueTransfer.transferValue
        state account beneficiary accountBalance beneficiaryBalance accountBalance
    { state := WorldState.deleteAccount transferredState account
      sideEffects :=
        { refundCounter := 0
          logs := LogState.empty
          accountsToDelete := [account]
          touchedAccounts := [beneficiary] } }
  else
    postCancunSelfdestructEffect state account beneficiary accountBalance beneficiaryBalance

theorem eip6780SelfdestructEffect_preExisting_eq_postCancunSelfdestructEffect
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance false =
      postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance := rfl

theorem eip6780SelfdestructEffect_sameTx_state
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance true).state =
      WorldState.deleteAccount
        (CallValueTransfer.transferValue
          state account beneficiary accountBalance beneficiaryBalance accountBalance)
        account := rfl

theorem eip6780SelfdestructEffect_sameTx_refundCounter
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance true).sideEffects.refundCounter =
      0 := rfl

theorem eip6780SelfdestructEffect_sameTx_logs
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance true).sideEffects.logs =
      LogState.empty := rfl

theorem eip6780SelfdestructEffect_sameTx_accountsToDelete
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance true).sideEffects.accountsToDelete =
      [account] := rfl

theorem eip6780SelfdestructEffect_sameTx_touchedAccounts
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance true).sideEffects.touchedAccounts =
      [beneficiary] := rfl

theorem eip6780SelfdestructEffect_sameTx_accountDeleted
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    WorldState.getAccount
        (eip6780SelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance true).state
        account =
      none := by
  rw [eip6780SelfdestructEffect_sameTx_state]
  exact WorldState.getAccount_deleteAccount_same _ _

theorem eip6780SelfdestructEffect_preExisting_refundCounter
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance false).sideEffects.refundCounter =
      0 := rfl

theorem eip6780SelfdestructEffect_preExisting_logs
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance false).sideEffects.logs =
      LogState.empty := rfl

theorem eip6780SelfdestructEffect_preExisting_accountsToDelete
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance false).sideEffects.accountsToDelete =
      [] := rfl

theorem eip6780SelfdestructEffect_preExisting_touchedAccounts
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance false).sideEffects.touchedAccounts =
      [beneficiary] := rfl

theorem eip6780SelfdestructEffect_preExisting_accountBalance?
    {state : WorldState} {account beneficiary : Address} {accountRecord : Account}
    (accountBalance beneficiaryBalance : Word256)
    (h_account : WorldState.getAccount state account = some accountRecord)
    (h_ne : account ≠ beneficiary) :
    WorldState.accountBalance?
        (eip6780SelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance false).state
        account =
      some (accountBalance - accountBalance) :=
  postCancunSelfdestructEffect_accountBalance?
    accountBalance beneficiaryBalance h_account h_ne

theorem eip6780SelfdestructEffect_preExisting_beneficiaryBalance?
    {state : WorldState} {account beneficiary : Address} {beneficiaryRecord : Account}
    (accountBalance beneficiaryBalance : Word256)
    (h_beneficiary : WorldState.getAccount state beneficiary = some beneficiaryRecord)
    (h_ne : account ≠ beneficiary) :
    WorldState.accountBalance?
        (eip6780SelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance false).state
        beneficiary =
      some (beneficiaryBalance + accountBalance) :=
  postCancunSelfdestructEffect_beneficiaryBalance?
    accountBalance beneficiaryBalance h_beneficiary h_ne

theorem eip6780SelfdestructEffect_accountsToDelete_fromCreatedSet_created
    (state : WorldState) (created : CreatedAccounts.CreatedAccountSet)
    (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256)
    (h_created : CreatedAccounts.createdInSameTx created account = true) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance
        (CreatedAccounts.createdInSameTx created account)).sideEffects.accountsToDelete =
      [account] := by
  rw [h_created]
  exact eip6780SelfdestructEffect_sameTx_accountsToDelete
    state account beneficiary accountBalance beneficiaryBalance

theorem eip6780SelfdestructEffect_accountsToDelete_fromCreatedSet_preExisting
    (state : WorldState) (created : CreatedAccounts.CreatedAccountSet)
    (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256)
    (h_not_created : CreatedAccounts.createdInSameTx created account = false) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance
        (CreatedAccounts.createdInSameTx created account)).sideEffects.accountsToDelete =
      [] := by
  rw [h_not_created]
  exact eip6780SelfdestructEffect_preExisting_accountsToDelete
    state account beneficiary accountBalance beneficiaryBalance

theorem eip6780SelfdestructEffect_state_fromCreatedSet_created_deleted
    (state : WorldState) (created : CreatedAccounts.CreatedAccountSet)
    (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256)
    (h_created : CreatedAccounts.createdInSameTx created account = true) :
    WorldState.getAccount
        (eip6780SelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance
          (CreatedAccounts.createdInSameTx created account)).state
        account =
      none := by
  rw [h_created]
  exact eip6780SelfdestructEffect_sameTx_accountDeleted
    state account beneficiary accountBalance beneficiaryBalance

theorem eip6780SelfdestructEffect_fromEmptyCreatedSet_accountsToDelete
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance
        (CreatedAccounts.createdInSameTx CreatedAccounts.empty account)).sideEffects.accountsToDelete =
      [] := by
  rw [CreatedAccounts.createdInSameTx_empty]
  exact eip6780SelfdestructEffect_preExisting_accountsToDelete
    state account beneficiary accountBalance beneficiaryBalance

theorem callResultFromEffect_status
    (effect : SelfdestructEffect) (status : CallStatus) (gasRemaining : Nat) :
    (callResultFromEffect effect status gasRemaining).status = status := rfl

theorem callResultFromEffect_state
    (effect : SelfdestructEffect) (status : CallStatus) (gasRemaining : Nat) :
    (callResultFromEffect effect status gasRemaining).state = effect.state := rfl

theorem callResultFromEffect_output
    (effect : SelfdestructEffect) (status : CallStatus) (gasRemaining : Nat) :
    (callResultFromEffect effect status gasRemaining).output = [] := rfl

theorem selfdestruct_committedState_success
    (input : MessageCallExecution.CallExecutionInput)
    (effect : SelfdestructEffect) (gasRemaining : Nat) :
    MessageCallExecution.committedState input
        (callResultFromEffect effect .success gasRemaining) =
      effect.state := rfl

theorem selfdestruct_committedState_revert
    (input : MessageCallExecution.CallExecutionInput)
    (effect : SelfdestructEffect) (gasRemaining : Nat) :
    MessageCallExecution.committedState input
        (callResultFromEffect effect .revert gasRemaining) =
      input.state := rfl

theorem selfdestruct_committedState_failure
    (input : MessageCallExecution.CallExecutionInput)
    (effect : SelfdestructEffect) (gasRemaining : Nat) :
    MessageCallExecution.committedState input
        (callResultFromEffect effect .failure gasRemaining) =
      input.state := rfl

theorem selfdestruct_visibleSideEffects_success
    (effect : SelfdestructEffect) (gasRemaining : Nat) :
    MessageCallExecution.visibleSideEffects
        (callResultFromEffect effect .success gasRemaining)
        effect.sideEffects =
      effect.sideEffects := rfl

theorem selfdestruct_visibleSideEffects_revert
    (effect : SelfdestructEffect) (gasRemaining : Nat) :
    MessageCallExecution.visibleSideEffects
        (callResultFromEffect effect .revert gasRemaining)
        effect.sideEffects =
      MessageCallExecution.CallSideEffects.empty := rfl

theorem selfdestruct_visibleSideEffects_failure
    (effect : SelfdestructEffect) (gasRemaining : Nat) :
    MessageCallExecution.visibleSideEffects
        (callResultFromEffect effect .failure gasRemaining)
        effect.sideEffects =
      MessageCallExecution.CallSideEffects.empty := rfl

theorem selfdestruct_messageCallOutput_success
    (effect : SelfdestructEffect) (gasRemaining : Nat) :
    MessageCallExecution.messageCallOutput_fromResult
        (callResultFromEffect effect .success gasRemaining)
        effect.sideEffects =
      { gasLeft := gasRemaining
        refundCounter := effect.sideEffects.refundCounter
        logs := effect.sideEffects.logs
        accountsToDelete := effect.sideEffects.accountsToDelete
        touchedAccounts := effect.sideEffects.touchedAccounts
        status := .success } := rfl

theorem selfdestruct_messageCallOutput_revert
    (effect : SelfdestructEffect) (gasRemaining : Nat) :
    MessageCallExecution.messageCallOutput_fromResult
        (callResultFromEffect effect .revert gasRemaining)
        effect.sideEffects =
      { gasLeft := gasRemaining
        refundCounter := 0
        logs := LogState.empty
        accountsToDelete := []
        touchedAccounts := []
        status := .revert } := rfl

theorem selfdestruct_messageCallOutput_failure
    (effect : SelfdestructEffect) (gasRemaining : Nat) :
    MessageCallExecution.messageCallOutput_fromResult
        (callResultFromEffect effect .failure gasRemaining)
        effect.sideEffects =
      { gasLeft := gasRemaining
        refundCounter := 0
        logs := LogState.empty
        accountsToDelete := []
        touchedAccounts := []
        status := .failure } := rfl

theorem eip6780SelfdestructEffect_revert_stateRestored
    (input : MessageCallExecution.CallExecutionInput)
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) (createdInSameTx : Bool)
    (gasRemaining : Nat) :
    MessageCallExecution.committedState input
        (callResultFromEffect
          (eip6780SelfdestructEffect
            state account beneficiary accountBalance beneficiaryBalance createdInSameTx)
          .revert
          gasRemaining) =
      input.state := rfl

theorem eip6780SelfdestructEffect_failure_stateRestored
    (input : MessageCallExecution.CallExecutionInput)
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) (createdInSameTx : Bool)
    (gasRemaining : Nat) :
    MessageCallExecution.committedState input
        (callResultFromEffect
          (eip6780SelfdestructEffect
            state account beneficiary accountBalance beneficiaryBalance createdInSameTx)
          .failure
          gasRemaining) =
      input.state := rfl

theorem eip6780SelfdestructEffect_revert_accountsToDeleteCleared
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) (createdInSameTx : Bool)
    (gasRemaining : Nat) :
    (MessageCallExecution.messageCallOutput_fromResult
        (callResultFromEffect
          (eip6780SelfdestructEffect
            state account beneficiary accountBalance beneficiaryBalance createdInSameTx)
          .revert
          gasRemaining)
        (eip6780SelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance createdInSameTx).sideEffects).accountsToDelete =
      [] := rfl

theorem eip6780SelfdestructEffect_revert_touchedAccountsCleared
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) (createdInSameTx : Bool)
    (gasRemaining : Nat) :
    (MessageCallExecution.messageCallOutput_fromResult
        (callResultFromEffect
          (eip6780SelfdestructEffect
            state account beneficiary accountBalance beneficiaryBalance createdInSameTx)
          .revert
          gasRemaining)
        (eip6780SelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance createdInSameTx).sideEffects).touchedAccounts =
      [] := rfl

theorem eip6780SelfdestructEffect_revert_logsCleared
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) (createdInSameTx : Bool)
    (gasRemaining : Nat) :
    (MessageCallExecution.messageCallOutput_fromResult
        (callResultFromEffect
          (eip6780SelfdestructEffect
            state account beneficiary accountBalance beneficiaryBalance createdInSameTx)
          .revert
          gasRemaining)
        (eip6780SelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance createdInSameTx).sideEffects).logs =
      LogState.empty := rfl

end SelfdestructEffects

end EvmAsm.EL
