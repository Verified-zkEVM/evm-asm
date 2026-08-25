/-
  EvmAsm.EL.LogArgsBridge

  Bridge from EVM LOG stack arguments to EL log entries (GH #112).
-/

module

public import EvmAsm.EL.Logs
public import EvmAsm.Evm64.LogArgs

@[expose] public section

namespace EvmAsm.EL

namespace LogArgsBridge

abbrev LogArgs := EvmAsm.Evm64.LogArgs.Args
abbrev LogKind := EvmAsm.Evm64.LogArgs.Kind

def topic (word : EvmAsm.Evm64.EvmWord) : LogTopic :=
  word

def topics (args : LogArgs) : List LogTopic :=
  args.topics

/-- Build the EL log entry once the memory slice has been loaded into bytes. -/
def mkLogEntry (emitter : Address) (data : List Byte) (args : LogArgs) : LogEntry :=
  LogEntry.mkChecked emitter (topics args) data

theorem mkLogEntryEmitter (emitter : Address) (data : List Byte) (args : LogArgs) :
    (mkLogEntry emitter data args).emitter = emitter := rfl

theorem mkLogEntryData (emitter : Address) (data : List Byte) (args : LogArgs) :
    (mkLogEntry emitter data args).data = data := rfl

theorem mkLogEntryTopics (emitter : Address) (data : List Byte) (args : LogArgs) :
    (mkLogEntry emitter data args).topics = topics args := rfl

theorem topicCountOk_of_logArgs
    (kind : LogKind) (emitter : Address) (data : List Byte) (args : LogArgs)
    (h_topics : EvmAsm.Evm64.LogArgs.topicCountOk kind args) :
    (mkLogEntry emitter data args).topicCountOk := by
  cases kind
  · simp [mkLogEntry, topics, LogEntry.mkChecked, LogEntry.topicCountOk,
      EvmAsm.Evm64.LogArgs.topicCountOk, EvmAsm.Evm64.LogArgs.topicCount] at h_topics ⊢
    simp [h_topics]
  · simp [mkLogEntry, topics, LogEntry.mkChecked, LogEntry.topicCountOk,
      EvmAsm.Evm64.LogArgs.topicCountOk, EvmAsm.Evm64.LogArgs.topicCount] at h_topics ⊢
    omega
  · simp [mkLogEntry, topics, LogEntry.mkChecked, LogEntry.topicCountOk,
      EvmAsm.Evm64.LogArgs.topicCountOk, EvmAsm.Evm64.LogArgs.topicCount] at h_topics ⊢
    omega
  · simp [mkLogEntry, topics, LogEntry.mkChecked, LogEntry.topicCountOk,
      EvmAsm.Evm64.LogArgs.topicCountOk, EvmAsm.Evm64.LogArgs.topicCount] at h_topics ⊢
    omega
  · simp [mkLogEntry, topics, LogEntry.mkChecked, LogEntry.topicCountOk,
      EvmAsm.Evm64.LogArgs.topicCountOk, EvmAsm.Evm64.LogArgs.topicCount] at h_topics ⊢
    omega

theorem topicCountOk_log0 (emitter : Address) (data : List Byte)
    (range : EvmAsm.Evm64.LogArgs.MemoryRange) :
    (mkLogEntry emitter data { data := range, topics := [] }).topicCountOk := by
  exact topicCountOk_of_logArgs .log0 emitter data { data := range, topics := [] } rfl

theorem topicCountOk_log4
    (emitter : Address) (data : List Byte) (range : EvmAsm.Evm64.LogArgs.MemoryRange)
    (topic0 topic1 topic2 topic3 : EvmAsm.Evm64.EvmWord) :
    (mkLogEntry emitter data
        { data := range, topics := [topic0, topic1, topic2, topic3] }).topicCountOk := by
  exact topicCountOk_of_logArgs .log4 emitter data
    { data := range, topics := [topic0, topic1, topic2, topic3] } rfl

/--
Append a log entry built from `LogArgs` to a `LogState`, bundling
`mkLogEntry` with `LogState.appendLog`. Mirrors how
`TerminatingArgsBridge.mkReturnResult` / `mkRevertResult` package the
bridge output for downstream consumers.
-/
def appendLogFromArgs
    (logs : LogState) (emitter : Address) (data : List Byte) (args : LogArgs) : LogState :=
  logs.appendLog (mkLogEntry emitter data args)

@[simp] theorem appendLogFromArgs_entries
    (logs : LogState) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogFromArgs logs emitter data args).entries =
      logs.entries ++ [mkLogEntry emitter data args] := rfl

theorem appendLogFromArgs_length
    (logs : LogState) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogFromArgs logs emitter data args).entries.length =
      logs.entries.length + 1 := by
  simp [appendLogFromArgs]

theorem appendLogFromArgs_emitter
    (logs : LogState) (emitter : Address) (data : List Byte) (args : LogArgs) :
    ((appendLogFromArgs logs emitter data args).entries.getLast
        (by simp [appendLogFromArgs, LogState.appendLog])).emitter = emitter := by
  simp [appendLogFromArgs, LogState.appendLog, mkLogEntry, LogEntry.mkChecked]

theorem appendLogFromArgs_data
    (logs : LogState) (emitter : Address) (data : List Byte) (args : LogArgs) :
    ((appendLogFromArgs logs emitter data args).entries.getLast
        (by simp [appendLogFromArgs, LogState.appendLog])).data = data := by
  simp [appendLogFromArgs, LogState.appendLog, mkLogEntry, LogEntry.mkChecked]

theorem appendLogFromArgs_topics
    (logs : LogState) (emitter : Address) (data : List Byte) (args : LogArgs) :
    ((appendLogFromArgs logs emitter data args).entries.getLast
        (by simp [appendLogFromArgs, LogState.appendLog])).topics = topics args := by
  simp [appendLogFromArgs, LogState.appendLog, mkLogEntry, LogEntry.mkChecked]

theorem topicCountOk_appended
    (logs : LogState) (kind : LogKind) (emitter : Address) (data : List Byte)
    (args : LogArgs) (h_topics : EvmAsm.Evm64.LogArgs.topicCountOk kind args) :
    ((appendLogFromArgs logs emitter data args).entries.getLast
        (by simp [appendLogFromArgs, LogState.appendLog])).topicCountOk := by
  simpa [appendLogFromArgs, LogState.appendLog] using
    topicCountOk_of_logArgs kind emitter data args h_topics

end LogArgsBridge

end EvmAsm.EL
