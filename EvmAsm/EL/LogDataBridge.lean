/-
  EvmAsm.EL.LogDataBridge

  Bridge from LOG stack arguments to event data bytes (GH #112).
-/

module

public import EvmAsm.EL.LogArgsBridge

@[expose] public section

namespace EvmAsm.EL

namespace LogDataBridge

abbrev LogArgs := EvmAsm.Evm64.LogArgs.Args
abbrev MemoryReader := Nat → Byte

/-- First memory byte consumed as LOG event data. -/
def dataStart (args : LogArgs) : Nat :=
  args.data.offset.toNat

/-- Number of memory bytes consumed as LOG event data. -/
def dataSize (args : LogArgs) : Nat :=
  args.data.size.toNat

/-- LOG event data bytes loaded from a pure memory-reader function. -/
def logDataFromMemory (readByte : MemoryReader) (args : LogArgs) : List Byte :=
  (List.range (dataSize args)).map (fun i => readByte (dataStart args + i))

/-- Build a LOG entry directly from stack args and a pure memory reader.
    Distinctive token: LogDataBridge.mkLogEntryFromMemory #112. -/
def mkLogEntryFromMemory (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    LogEntry :=
  LogArgsBridge.mkLogEntry emitter (logDataFromMemory readByte args) args

theorem dataStart_eq (args : LogArgs) :
    dataStart args = args.data.offset.toNat := rfl

theorem dataSize_eq (args : LogArgs) :
    dataSize args = args.data.size.toNat := rfl

@[simp] theorem logDataFromMemory_length (readByte : MemoryReader) (args : LogArgs) :
    (logDataFromMemory readByte args).length = dataSize args := by
  simp [logDataFromMemory]

theorem logDataFromMemory_get
    {readByte : MemoryReader} {args : LogArgs} {i : Nat}
    (h : i < dataSize args) :
    (logDataFromMemory readByte args)[i]'(by
      simpa [logDataFromMemory_length] using h) =
      readByte (dataStart args + i) := by
  simp [logDataFromMemory, List.getElem_map, List.getElem_range]

theorem logDataFromMemory_get?
    (readByte : MemoryReader) (args : LogArgs) (i : Nat)
    (h : i < dataSize args) :
    (logDataFromMemory readByte args)[i]? =
      some (readByte (dataStart args + i)) := by
  simp [logDataFromMemory, h]

@[simp] theorem logDataFromMemory_zero_size
    (readByte : MemoryReader) (rangeOffset : EvmAsm.Evm64.EvmWord)
    (topics : List EvmAsm.Evm64.EvmWord) :
    logDataFromMemory readByte
        { data := { offset := rangeOffset, size := 0 }, topics := topics } =
      [] := rfl

theorem mkLogEntryFromMemory_eq
    (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    mkLogEntryFromMemory emitter readByte args =
      LogArgsBridge.mkLogEntry emitter (logDataFromMemory readByte args) args := rfl

theorem mkLogEntryFromMemoryEmitter
    (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    (mkLogEntryFromMemory emitter readByte args).emitter = emitter := rfl

theorem mkLogEntryFromMemoryData
    (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    (mkLogEntryFromMemory emitter readByte args).data =
      logDataFromMemory readByte args := rfl

theorem mkLogEntryFromMemoryTopics
    (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    (mkLogEntryFromMemory emitter readByte args).topics =
      LogArgsBridge.topics args := rfl

theorem mkLogEntryFromMemoryTopicCountOk
    (kind : LogArgsBridge.LogKind) (emitter : Address) (readByte : MemoryReader)
    (args : LogArgs)
    (h_topics : EvmAsm.Evm64.LogArgs.topicCountOk kind args) :
    (mkLogEntryFromMemory emitter readByte args).topicCountOk := by
  exact LogArgsBridge.topicCountOk_of_logArgs
    kind emitter (logDataFromMemory readByte args) args h_topics

/-- Append a LOG entry directly from stack args and a pure memory reader.
    Distinctive token: LogDataBridge.appendLogFromMemory #112. -/
def appendLogFromMemory
    (logs : LogState) (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    LogState :=
  LogArgsBridge.appendLogFromArgs logs emitter (logDataFromMemory readByte args) args

theorem appendLogFromMemory_entries
    (logs : LogState) (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory logs emitter readByte args).entries =
      logs.entries ++ [mkLogEntryFromMemory emitter readByte args] := rfl

theorem appendLogFromMemory_length
    (logs : LogState) (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory logs emitter readByte args).entries.length =
      logs.entries.length + 1 := by
  simp [appendLogFromMemory, LogArgsBridge.appendLogFromArgs]

theorem appendLogFromMemory_lastData
    (logs : LogState) (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    ((appendLogFromMemory logs emitter readByte args).entries.getLast
        (by simp [appendLogFromMemory, LogArgsBridge.appendLogFromArgs])).data =
      logDataFromMemory readByte args := by
  simp [appendLogFromMemory, LogArgsBridge.appendLogFromArgs,
    LogArgsBridge.mkLogEntry, LogEntry.mkChecked]

theorem appendLogFromMemory_lastTopicCountOk
    (logs : LogState) (kind : LogArgsBridge.LogKind) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs)
    (h_topics : EvmAsm.Evm64.LogArgs.topicCountOk kind args) :
    ((appendLogFromMemory logs emitter readByte args).entries.getLast
        (by simp [appendLogFromMemory, LogArgsBridge.appendLogFromArgs])).topicCountOk := by
  simpa [appendLogFromMemory, LogArgsBridge.appendLogFromArgs, mkLogEntryFromMemory]
    using mkLogEntryFromMemoryTopicCountOk kind emitter readByte args h_topics

end LogDataBridge

end EvmAsm.EL
