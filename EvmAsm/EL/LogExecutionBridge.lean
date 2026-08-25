/-
  EvmAsm.EL.LogExecutionBridge

  End-to-end pure bridge from LOG memory data to call side effects.
-/

module

public import EvmAsm.EL.LogCallEffects
public import EvmAsm.EL.LogDataBridge

@[expose] public section

namespace EvmAsm.EL

namespace LogExecutionBridge

abbrev CallSideEffects := LogCallEffects.CallSideEffects
abbrev LogArgs := LogDataBridge.LogArgs
abbrev LogKind := LogArgsBridge.LogKind
abbrev MemoryReader := LogDataBridge.MemoryReader

/-- Distinctive token: LogExecutionBridge.appendLogFromMemory #112. -/
def appendLogFromMemory
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) : CallSideEffects :=
  LogCallEffects.appendLogSideEffect effects emitter
    (LogDataBridge.logDataFromMemory readByte args) args

@[simp] theorem appendLogFromMemory_refundCounter
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory effects emitter readByte args).refundCounter =
      effects.refundCounter := rfl

@[simp] theorem appendLogFromMemory_accountsToDelete
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory effects emitter readByte args).accountsToDelete =
      effects.accountsToDelete := rfl

@[simp] theorem appendLogFromMemory_touchedAccounts
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory effects emitter readByte args).touchedAccounts =
      effects.touchedAccounts := rfl

@[simp] theorem appendLogFromMemory_logs
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory effects emitter readByte args).logs =
      LogArgsBridge.appendLogFromArgs effects.logs emitter
        (LogDataBridge.logDataFromMemory readByte args) args := rfl

theorem appendLogFromMemory_log_entries
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory effects emitter readByte args).logs.entries =
      effects.logs.entries ++
        [LogDataBridge.mkLogEntryFromMemory emitter readByte args] := rfl

theorem appendLogFromMemory_log_length
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory effects emitter readByte args).logs.entries.length =
      effects.logs.entries.length + 1 := by
  simp [appendLogFromMemory, LogCallEffects.appendLogSideEffect,
    LogArgsBridge.appendLogFromArgs]

theorem appendLogFromMemory_last_topicCountOk
    (effects : CallSideEffects) (kind : LogKind) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs)
    (h_topics : EvmAsm.Evm64.LogArgs.topicCountOk kind args) :
    ((appendLogFromMemory effects emitter readByte args).logs.entries.getLast
        (by simp [appendLogFromMemory, LogCallEffects.appendLogSideEffect,
          LogArgsBridge.appendLogFromArgs, LogState.appendLog])).topicCountOk := by
  simpa [appendLogFromMemory, LogCallEffects.appendLogSideEffect,
    LogDataBridge.mkLogEntryFromMemory_eq] using
    LogDataBridge.mkLogEntryFromMemoryTopicCountOk
      kind emitter readByte args h_topics

end LogExecutionBridge

end EvmAsm.EL
