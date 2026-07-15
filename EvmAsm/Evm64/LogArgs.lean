/-
  EvmAsm.Evm64.LogArgs

  Pure stack-argument records for LOG0 through LOG4 (GH #112).
-/

import EvmAsm.Evm64.EvmWord

namespace EvmAsm.Evm64

namespace LogArgs

/-- Memory slice described by an EVM offset and byte size. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr

/-- LOG opcode arity classifier. -/
inductive Kind where
  | log0
  | log1
  | log2
  | log3
  | log4
  deriving DecidableEq, Repr

/-- Stack arguments shared by LOG0 through LOG4: a data range plus topics. -/
structure Args where
  data : MemoryRange
  topics : List EvmWord
  deriving Repr

def topicCount : Kind → Nat
  | .log0 => 0
  | .log1 => 1
  | .log2 => 2
  | .log3 => 3
  | .log4 => 4

def stackArgumentCount (kind : Kind) : Nat :=
  2 + topicCount kind

def topicCountOk (kind : Kind) (args : Args) : Prop :=
  args.topics.length = topicCount kind

def dataRange (args : Args) : MemoryRange :=
  args.data

theorem topicCountLog0 : topicCount .log0 = 0 := rfl
theorem topicCountLog1 : topicCount .log1 = 1 := rfl
theorem topicCountLog2 : topicCount .log2 = 2 := rfl
theorem topicCountLog3 : topicCount .log3 = 3 := rfl
theorem topicCountLog4 : topicCount .log4 = 4 := rfl

theorem stackArgumentCountLog0 : stackArgumentCount .log0 = 2 := rfl
theorem stackArgumentCountLog1 : stackArgumentCount .log1 = 3 := rfl
theorem stackArgumentCountLog2 : stackArgumentCount .log2 = 4 := rfl
theorem stackArgumentCountLog3 : stackArgumentCount .log3 = 5 := rfl
theorem stackArgumentCountLog4 : stackArgumentCount .log4 = 6 := rfl

theorem topicCountOk_iff (kind : Kind) (args : Args) :
    topicCountOk kind args ↔ args.topics.length = topicCount kind := Iff.rfl

theorem topicCountOk_log0 (data : MemoryRange) :
    topicCountOk .log0 { data := data, topics := [] } := rfl

theorem topicCountOk_log1 (data : MemoryRange) (topic : EvmWord) :
    topicCountOk .log1 { data := data, topics := [topic] } := rfl

theorem topicCountOk_log4
    (data : MemoryRange) (topic0 topic1 topic2 topic3 : EvmWord) :
    topicCountOk .log4 { data := data, topics := [topic0, topic1, topic2, topic3] } := rfl

end LogArgs

end EvmAsm.Evm64
