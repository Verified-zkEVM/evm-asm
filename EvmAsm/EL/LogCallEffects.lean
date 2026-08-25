/-
  EvmAsm.EL.LogCallEffects

  Bridge from LOG entries to message-call side effects (GH #112 / #121).
-/

module

public import EvmAsm.EL.LogArgsBridge
public import EvmAsm.EL.MessageCallExecution

@[expose] public section

namespace EvmAsm.EL

namespace LogCallEffects

abbrev CallSideEffects := MessageCallExecution.CallSideEffects
abbrev LogArgs := LogArgsBridge.LogArgs
abbrev LogKind := LogArgsBridge.LogKind

/-- Append a LOG entry into the message-call side-effect bundle, preserving
    every non-log side-effect field. Distinctive token: appendLogSideEffect. -/
def appendLogSideEffect
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    CallSideEffects :=
  { refundCounter := effects.refundCounter
    logs := LogArgsBridge.appendLogFromArgs effects.logs emitter data args
    accountsToDelete := effects.accountsToDelete
    touchedAccounts := effects.touchedAccounts }

@[simp] theorem appendLogSideEffect_refundCounter
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogSideEffect effects emitter data args).refundCounter =
      effects.refundCounter := rfl

@[simp] theorem appendLogSideEffect_accountsToDelete
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogSideEffect effects emitter data args).accountsToDelete =
      effects.accountsToDelete := rfl

@[simp] theorem appendLogSideEffect_touchedAccounts
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogSideEffect effects emitter data args).touchedAccounts =
      effects.touchedAccounts := rfl

@[simp] theorem appendLogSideEffect_logs
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogSideEffect effects emitter data args).logs =
      LogArgsBridge.appendLogFromArgs effects.logs emitter data args := rfl

theorem appendLogSideEffect_log_entries
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogSideEffect effects emitter data args).logs.entries =
      effects.logs.entries ++ [LogArgsBridge.mkLogEntry emitter data args] := rfl

theorem appendLogSideEffect_log_length
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogSideEffect effects emitter data args).logs.entries.length =
      effects.logs.entries.length + 1 := by
  simp [appendLogSideEffect, LogArgsBridge.appendLogFromArgs]

theorem appendLogSideEffect_last_topicCountOk
    (effects : CallSideEffects) (kind : LogKind) (emitter : Address) (data : List Byte)
    (args : LogArgs) (h_topics : EvmAsm.Evm64.LogArgs.topicCountOk kind args) :
    ((appendLogSideEffect effects emitter data args).logs.entries.getLast
        (by simp [appendLogSideEffect, LogArgsBridge.appendLogFromArgs,
          LogState.appendLog])).topicCountOk := by
  simpa [appendLogSideEffect] using
    LogArgsBridge.topicCountOk_appended effects.logs kind emitter data args h_topics

end LogCallEffects

end EvmAsm.EL
