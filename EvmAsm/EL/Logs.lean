/-
  EvmAsm.EL.Logs

  Pure LOG0-LOG4 event surface for GH #112.
-/

module

public import EvmAsm.EL.WorldState

@[expose] public section

namespace EvmAsm.EL

/-- A LOG topic is a full 256-bit EVM word. -/
abbrev LogTopic := Word256

/-- One EVM log entry emitted by LOG0 through LOG4. -/
structure LogEntry where
  emitter : Address
  topics : List LogTopic
  data : List Byte
  deriving Repr

namespace LogEntry

/-- Topic-count validity for LOG0 through LOG4. -/
def topicCountOk (entry : LogEntry) : Prop :=
  entry.topics.length ≤ 4

/-- Construct a log entry when the caller already has the concrete topics/data. -/
def mkChecked (emitter : Address) (topics : List LogTopic) (data : List Byte) : LogEntry :=
  { emitter := emitter, topics := topics, data := data }

theorem topicCountOk_iff (entry : LogEntry) :
    entry.topicCountOk ↔ entry.topics.length ≤ 4 := Iff.rfl

theorem topicCountOk_nil (emitter : Address) (data : List Byte) :
    (mkChecked emitter [] data).topicCountOk := by
  simp [topicCountOk, mkChecked]

theorem topicCountOk_single (emitter : Address) (topic : LogTopic) (data : List Byte) :
    (mkChecked emitter [topic] data).topicCountOk := by
  simp [topicCountOk, mkChecked]

theorem topicCountOk_two
    (emitter : Address) (topic0 topic1 : LogTopic) (data : List Byte) :
    (mkChecked emitter [topic0, topic1] data).topicCountOk := by
  simp [topicCountOk, mkChecked]

theorem topicCountOk_three
    (emitter : Address) (topic0 topic1 topic2 : LogTopic) (data : List Byte) :
    (mkChecked emitter [topic0, topic1, topic2] data).topicCountOk := by
  simp [topicCountOk, mkChecked]

theorem topicCountOk_four
    (emitter : Address) (topic0 topic1 topic2 topic3 : LogTopic) (data : List Byte) :
    (mkChecked emitter [topic0, topic1, topic2, topic3] data).topicCountOk := by
  simp [topicCountOk, mkChecked]

end LogEntry

/-- Append-only sequence of EVM log entries accumulated during execution. -/
structure LogState where
  entries : List LogEntry
  deriving Repr

namespace LogState

def empty : LogState :=
  { entries := [] }

/-- Append one log entry to the end of the execution log. -/
def appendLog (logs : LogState) (entry : LogEntry) : LogState :=
  { entries := logs.entries ++ [entry] }

@[simp] theorem entries_empty : empty.entries = [] := rfl

@[simp] theorem entries_appendLog (logs : LogState) (entry : LogEntry) :
    (appendLog logs entry).entries = logs.entries ++ [entry] := rfl

theorem length_appendLog (logs : LogState) (entry : LogEntry) :
    (appendLog logs entry).entries.length = logs.entries.length + 1 := by
  simp [appendLog]

theorem appendLog_empty_entries (entry : LogEntry) :
    (appendLog empty entry).entries = [entry] := rfl

theorem appended_log_topicCountOk
    (logs : LogState) {entry : LogEntry} (h_topics : entry.topicCountOk) :
    (appendLog logs entry).entries.getLast (by simp [appendLog]) |>.topicCountOk := by
  simpa [appendLog] using h_topics

end LogState

end EvmAsm.EL
