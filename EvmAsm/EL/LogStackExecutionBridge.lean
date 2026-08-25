/-
  EvmAsm.EL.LogStackExecutionBridge

  Pure stack-to-log execution bridge for LOG0 through LOG4 (GH #112).
-/

module

public import EvmAsm.Evm64.LogArgsStackDecode
public import EvmAsm.EL.LogExecutionBridge

@[expose] public section

namespace EvmAsm.EL

namespace LogStackExecutionBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev LogKind := EvmAsm.Evm64.LogArgs.Kind
abbrev LogArgs := EvmAsm.Evm64.LogArgs.Args
abbrev CallSideEffects := LogExecutionBridge.CallSideEffects
abbrev MemoryReader := LogExecutionBridge.MemoryReader

/-- Runtime state visible to the pure LOG stack bridge. -/
structure LogStackState where
  effects : CallSideEffects
  stack : List EvmWord

def stackRestAfterLog? (kind : LogKind) : List EvmWord -> Option (List EvmWord)
  | _offset :: _size :: rest =>
      match kind with
      | .log0 => some rest
      | .log1 =>
          match rest with
          | _topic0 :: rest => some rest
          | _ => none
      | .log2 =>
          match rest with
          | _topic0 :: _topic1 :: rest => some rest
          | _ => none
      | .log3 =>
          match rest with
          | _topic0 :: _topic1 :: _topic2 :: rest => some rest
          | _ => none
      | .log4 =>
          match rest with
          | _topic0 :: _topic1 :: _topic2 :: _topic3 :: rest => some rest
          | _ => none
  | _ => none

/--
Run the pure LOG stack effect: decode the opcode-specific stack arguments,
read the memory data slice, append the log side effect, and consume all LOG
arguments without pushing a result.

Distinctive token: LogStackExecutionBridge.runLogStack? #112.
-/
def runLogStack? (kind : LogKind) (emitter : Address) (readByte : MemoryReader) :
    LogStackState -> Option LogStackState
  | state =>
      match EvmAsm.Evm64.LogArgsStackDecode.decodeLogStack? kind state.stack,
          stackRestAfterLog? kind state.stack with
      | some args, some rest =>
          some
            { effects :=
                LogExecutionBridge.appendLogFromMemory
                  state.effects emitter readByte args
              stack := rest }
      | _, _ => none

theorem stackRestAfterLog?_log0
    (offset size : EvmWord) (rest : List EvmWord) :
    stackRestAfterLog? .log0 (offset :: size :: rest) = some rest := rfl

theorem stackRestAfterLog?_log1
    (offset size topic0 : EvmWord) (rest : List EvmWord) :
    stackRestAfterLog? .log1 (offset :: size :: topic0 :: rest) = some rest := rfl

theorem stackRestAfterLog?_log2
    (offset size topic0 topic1 : EvmWord) (rest : List EvmWord) :
    stackRestAfterLog? .log2 (offset :: size :: topic0 :: topic1 :: rest) =
      some rest := rfl

theorem stackRestAfterLog?_log3
    (offset size topic0 topic1 topic2 : EvmWord) (rest : List EvmWord) :
    stackRestAfterLog? .log3
        (offset :: size :: topic0 :: topic1 :: topic2 :: rest) =
      some rest := rfl

theorem stackRestAfterLog?_log4
    (offset size topic0 topic1 topic2 topic3 : EvmWord)
    (rest : List EvmWord) :
    stackRestAfterLog? .log4
        (offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: rest) =
      some rest := rfl

@[simp] theorem stackRestAfterLog?_nil (kind : LogKind) :
    stackRestAfterLog? kind [] = none := rfl

@[simp] theorem stackRestAfterLog?_singleton (kind : LogKind) (offset : EvmWord) :
    stackRestAfterLog? kind [offset] = none := rfl

theorem stackRestAfterLog?_log0_none_of_empty :
    stackRestAfterLog? .log0 [] = none := rfl

theorem stackRestAfterLog?_log0_none_of_one
    (offset : EvmWord) :
    stackRestAfterLog? .log0 [offset] = none := rfl

theorem stackRestAfterLog?_log1_none_of_empty :
    stackRestAfterLog? .log1 [] = none := rfl

theorem stackRestAfterLog?_log1_none_of_one
    (offset : EvmWord) :
    stackRestAfterLog? .log1 [offset] = none := rfl

theorem stackRestAfterLog?_log1_none_of_two
    (offset size : EvmWord) :
    stackRestAfterLog? .log1 [offset, size] = none := rfl

theorem stackRestAfterLog?_log2_none_of_empty :
    stackRestAfterLog? .log2 [] = none := rfl

theorem stackRestAfterLog?_log2_none_of_one
    (offset : EvmWord) :
    stackRestAfterLog? .log2 [offset] = none := rfl

theorem stackRestAfterLog?_log2_none_of_two
    (offset size : EvmWord) :
    stackRestAfterLog? .log2 [offset, size] = none := rfl

theorem stackRestAfterLog?_log2_none_of_three
    (offset size topic0 : EvmWord) :
    stackRestAfterLog? .log2 [offset, size, topic0] = none := rfl

theorem stackRestAfterLog?_log3_none_of_empty :
    stackRestAfterLog? .log3 [] = none := rfl

theorem stackRestAfterLog?_log3_none_of_one
    (offset : EvmWord) :
    stackRestAfterLog? .log3 [offset] = none := rfl

theorem stackRestAfterLog?_log3_none_of_two
    (offset size : EvmWord) :
    stackRestAfterLog? .log3 [offset, size] = none := rfl

theorem stackRestAfterLog?_log3_none_of_three
    (offset size topic0 : EvmWord) :
    stackRestAfterLog? .log3 [offset, size, topic0] = none := rfl

theorem stackRestAfterLog?_log3_none_of_four
    (offset size topic0 topic1 : EvmWord) :
    stackRestAfterLog? .log3 [offset, size, topic0, topic1] = none := rfl

theorem stackRestAfterLog?_log4_none_of_empty :
    stackRestAfterLog? .log4 [] = none := rfl

theorem stackRestAfterLog?_log4_none_of_one
    (offset : EvmWord) :
    stackRestAfterLog? .log4 [offset] = none := rfl

theorem stackRestAfterLog?_log4_none_of_two
    (offset size : EvmWord) :
    stackRestAfterLog? .log4 [offset, size] = none := rfl

theorem stackRestAfterLog?_log4_none_of_three
    (offset size topic0 : EvmWord) :
    stackRestAfterLog? .log4 [offset, size, topic0] = none := rfl

theorem stackRestAfterLog?_log4_none_of_four
    (offset size topic0 topic1 : EvmWord) :
    stackRestAfterLog? .log4 [offset, size, topic0, topic1] = none := rfl

theorem stackRestAfterLog?_log4_none_of_five
    (offset size topic0 topic1 topic2 : EvmWord) :
    stackRestAfterLog? .log4 [offset, size, topic0, topic1, topic2] = none := rfl

theorem runLogStack?_eq_none_iff
    (kind : LogKind) (emitter : Address) (readByte : MemoryReader)
    (state : LogStackState) :
    runLogStack? kind emitter readByte state = none ↔
      EvmAsm.Evm64.LogArgsStackDecode.decodeLogStack? kind state.stack = none ∨
        stackRestAfterLog? kind state.stack = none := by
  cases state with
  | mk effects stack =>
      simp [runLogStack?]
      cases h_decode :
          EvmAsm.Evm64.LogArgsStackDecode.decodeLogStack? kind stack with
      | none => simp
      | some args =>
          cases h_rest : stackRestAfterLog? kind stack with
          | none => simp
          | some rest => simp

theorem runLogStack?_log0
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size : EvmWord) (rest : List EvmWord) :
    runLogStack? .log0 emitter readByte
        { effects := effects, stack := offset :: size :: rest } =
      some
        { effects :=
            LogExecutionBridge.appendLogFromMemory effects emitter readByte
              (EvmAsm.Evm64.LogArgsStackDecode.mkArgs offset size [])
          stack := rest } := rfl

theorem runLogStack?_log1
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 : EvmWord) (rest : List EvmWord) :
    runLogStack? .log1 emitter readByte
        { effects := effects, stack := offset :: size :: topic0 :: rest } =
      some
        { effects :=
            LogExecutionBridge.appendLogFromMemory effects emitter readByte
              (EvmAsm.Evm64.LogArgsStackDecode.mkArgs offset size [topic0])
          stack := rest } := rfl

theorem runLogStack?_log2
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 topic1 : EvmWord) (rest : List EvmWord) :
    runLogStack? .log2 emitter readByte
        { effects := effects, stack := offset :: size :: topic0 :: topic1 :: rest } =
      some
        { effects :=
            LogExecutionBridge.appendLogFromMemory effects emitter readByte
              (EvmAsm.Evm64.LogArgsStackDecode.mkArgs offset size [topic0, topic1])
          stack := rest } := rfl

theorem runLogStack?_log3
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 topic1 topic2 : EvmWord) (rest : List EvmWord) :
    runLogStack? .log3 emitter readByte
        { effects := effects,
          stack := offset :: size :: topic0 :: topic1 :: topic2 :: rest } =
      some
        { effects :=
            LogExecutionBridge.appendLogFromMemory effects emitter readByte
              (EvmAsm.Evm64.LogArgsStackDecode.mkArgs offset size
                [topic0, topic1, topic2])
          stack := rest } := rfl

theorem runLogStack?_log4
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 topic1 topic2 topic3 : EvmWord)
    (rest : List EvmWord) :
    runLogStack? .log4 emitter readByte
        { effects := effects,
          stack := offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: rest } =
      some
        { effects :=
            LogExecutionBridge.appendLogFromMemory effects emitter readByte
              (EvmAsm.Evm64.LogArgsStackDecode.mkArgs offset size
                [topic0, topic1, topic2, topic3])
          stack := rest } := rfl

theorem runLogStack?_log0_none_of_empty
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader) :
    runLogStack? .log0 emitter readByte { effects := effects, stack := [] } =
      none := rfl

theorem runLogStack?_log0_none_of_one
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset : EvmWord) :
    runLogStack? .log0 emitter readByte { effects := effects, stack := [offset] } =
      none := rfl

theorem runLogStack?_log1_none_of_empty
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader) :
    runLogStack? .log1 emitter readByte { effects := effects, stack := [] } =
      none := rfl

theorem runLogStack?_log1_none_of_one
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset : EvmWord) :
    runLogStack? .log1 emitter readByte { effects := effects, stack := [offset] } =
      none := rfl

theorem runLogStack?_log1_none_of_two
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size : EvmWord) :
    runLogStack? .log1 emitter readByte
        { effects := effects, stack := [offset, size] } =
      none := rfl

theorem runLogStack?_log2_none_of_empty
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader) :
    runLogStack? .log2 emitter readByte { effects := effects, stack := [] } =
      none := rfl

theorem runLogStack?_log2_none_of_one
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset : EvmWord) :
    runLogStack? .log2 emitter readByte { effects := effects, stack := [offset] } =
      none := rfl

theorem runLogStack?_log2_none_of_two
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size : EvmWord) :
    runLogStack? .log2 emitter readByte
        { effects := effects, stack := [offset, size] } =
      none := rfl

theorem runLogStack?_log2_none_of_three
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 : EvmWord) :
    runLogStack? .log2 emitter readByte
        { effects := effects, stack := [offset, size, topic0] } =
      none := rfl

theorem runLogStack?_log3_none_of_empty
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader) :
    runLogStack? .log3 emitter readByte { effects := effects, stack := [] } =
      none := rfl

theorem runLogStack?_log3_none_of_one
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset : EvmWord) :
    runLogStack? .log3 emitter readByte { effects := effects, stack := [offset] } =
      none := rfl

theorem runLogStack?_log3_none_of_two
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size : EvmWord) :
    runLogStack? .log3 emitter readByte
        { effects := effects, stack := [offset, size] } =
      none := rfl

theorem runLogStack?_log3_none_of_three
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 : EvmWord) :
    runLogStack? .log3 emitter readByte
        { effects := effects, stack := [offset, size, topic0] } =
      none := rfl

theorem runLogStack?_log3_none_of_four
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 topic1 : EvmWord) :
    runLogStack? .log3 emitter readByte
        { effects := effects, stack := [offset, size, topic0, topic1] } =
      none := rfl

theorem runLogStack?_log4_none_of_empty
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader) :
    runLogStack? .log4 emitter readByte { effects := effects, stack := [] } =
      none := rfl

theorem runLogStack?_log4_none_of_one
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset : EvmWord) :
    runLogStack? .log4 emitter readByte { effects := effects, stack := [offset] } =
      none := rfl

theorem runLogStack?_log4_none_of_two
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size : EvmWord) :
    runLogStack? .log4 emitter readByte
        { effects := effects, stack := [offset, size] } =
      none := rfl

theorem runLogStack?_log4_none_of_three
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 : EvmWord) :
    runLogStack? .log4 emitter readByte
        { effects := effects, stack := [offset, size, topic0] } =
      none := rfl

theorem runLogStack?_log4_none_of_four
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 topic1 : EvmWord) :
    runLogStack? .log4 emitter readByte
        { effects := effects, stack := [offset, size, topic0, topic1] } =
      none := rfl

theorem runLogStack?_log4_none_of_five
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 topic1 topic2 : EvmWord) :
    runLogStack? .log4 emitter readByte
        { effects := effects, stack := [offset, size, topic0, topic1, topic2] } =
      none := rfl

theorem runLogStack?_eq_some_iff
    (kind : LogKind) (emitter : Address) (readByte : MemoryReader)
    (state out : LogStackState) :
    runLogStack? kind emitter readByte state = some out ↔
      ∃ args rest,
        EvmAsm.Evm64.LogArgsStackDecode.decodeLogStack? kind state.stack =
          some args ∧
        stackRestAfterLog? kind state.stack = some rest ∧
        out =
          { effects :=
              LogExecutionBridge.appendLogFromMemory
                state.effects emitter readByte args
            stack := rest } := by
  cases state with
  | mk effects stack =>
      constructor
      · intro h_run
        simp [runLogStack?] at h_run
        cases h_decode :
            EvmAsm.Evm64.LogArgsStackDecode.decodeLogStack? kind stack with
        | none => simp [h_decode] at h_run
        | some args =>
            cases h_rest : stackRestAfterLog? kind stack with
            | none => simp [h_decode, h_rest] at h_run
            | some rest =>
                simp [h_decode, h_rest] at h_run
                exact ⟨args, rest, rfl, rfl, h_run.symm⟩
      · rintro ⟨args, rest, h_decode, h_rest, rfl⟩
        simp [runLogStack?, h_decode, h_rest]

/--
Successful LOG stack execution appends exactly one log entry to the current
side-effect log list.

Distinctive token:
LogStackExecutionBridge.runLogStack?_log_entries_length #112 #107.
-/
theorem runLogStack?_log_entries_length
    {kind : LogKind} {emitter : Address} {readByte : MemoryReader}
    {state out : LogStackState}
    (h_run : runLogStack? kind emitter readByte state = some out) :
    out.effects.logs.entries.length = state.effects.logs.entries.length + 1 := by
  rcases (runLogStack?_eq_some_iff kind emitter readByte state out).mp h_run with
    ⟨args, rest, _h_decode, _h_rest, h_out⟩
  subst h_out
  exact LogExecutionBridge.appendLogFromMemory_log_length
    state.effects emitter readByte args

theorem runLogStack?_stack_length
    {kind : LogKind} {emitter : Address} {readByte : MemoryReader}
    {state out : LogStackState}
    (h_run : runLogStack? kind emitter readByte state = some out) :
    out.stack.length + EvmAsm.Evm64.LogArgs.stackArgumentCount kind =
      state.stack.length := by
  cases state with
  | mk effects stack =>
      cases kind
      all_goals
        cases stack with
        | nil => simp [runLogStack?] at h_run
        | cons offset tail =>
            cases tail with
            | nil => simp [runLogStack?, stackRestAfterLog?] at h_run
            | cons size rest =>
                first
                | simp [runLogStack?, stackRestAfterLog?] at h_run
                  cases h_run
                  simp [EvmAsm.Evm64.LogArgs.stackArgumentCount,
                    EvmAsm.Evm64.LogArgs.topicCount]
                | cases rest with
                  | nil => simp [runLogStack?, stackRestAfterLog?] at h_run
                  | cons topic0 rest =>
                      first
                      | simp [runLogStack?, stackRestAfterLog?] at h_run
                        cases h_run
                        simp [EvmAsm.Evm64.LogArgs.stackArgumentCount,
                          EvmAsm.Evm64.LogArgs.topicCount]
                      | cases rest with
                        | nil => simp [runLogStack?, stackRestAfterLog?] at h_run
                        | cons topic1 rest =>
                            first
                            | simp [runLogStack?, stackRestAfterLog?] at h_run
                              cases h_run
                              simp [EvmAsm.Evm64.LogArgs.stackArgumentCount,
                                EvmAsm.Evm64.LogArgs.topicCount]
                            | cases rest with
                              | nil => simp [runLogStack?, stackRestAfterLog?] at h_run
                              | cons topic2 rest =>
                                  first
                                  | simp [runLogStack?, stackRestAfterLog?] at h_run
                                    cases h_run
                                    simp [EvmAsm.Evm64.LogArgs.stackArgumentCount,
                                      EvmAsm.Evm64.LogArgs.topicCount]
                                  | cases rest with
                                    | nil =>
                                        simp [runLogStack?, stackRestAfterLog?] at h_run
                                    | cons topic3 rest =>
                                        simp [runLogStack?, stackRestAfterLog?] at h_run
                                        cases h_run
                                        simp [EvmAsm.Evm64.LogArgs.stackArgumentCount,
                                          EvmAsm.Evm64.LogArgs.topicCount]

end LogStackExecutionBridge

end EvmAsm.EL
