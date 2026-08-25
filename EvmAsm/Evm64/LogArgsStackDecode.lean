/-
  EvmAsm.Evm64.LogArgsStackDecode

  Pure top-of-stack decoders for LOG0 through LOG4 arguments (GH #112).
-/

module

public import EvmAsm.Evm64.LogArgs

@[expose] public section

namespace EvmAsm.Evm64

namespace LogArgsStackDecode

open LogArgs

def mkArgs (offset size : EvmWord) (topics : List EvmWord) : Args :=
  { data := { offset := offset, size := size }, topics := topics }

/--
Decode LOG-family stack arguments from the top-of-stack list order:
`offset, size, topic0, topic1, ...`.

Distinctive token: LogArgsStackDecode.decodeLogStack? #112.
-/
def decodeLogStack? : Kind → List EvmWord → Option Args
  | .log0, offset :: size :: _ =>
      some (mkArgs offset size [])
  | .log1, offset :: size :: topic0 :: _ =>
      some (mkArgs offset size [topic0])
  | .log2, offset :: size :: topic0 :: topic1 :: _ =>
      some (mkArgs offset size [topic0, topic1])
  | .log3, offset :: size :: topic0 :: topic1 :: topic2 :: _ =>
      some (mkArgs offset size [topic0, topic1, topic2])
  | .log4, offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: _ =>
      some (mkArgs offset size [topic0, topic1, topic2, topic3])
  | _, _ => none

theorem decodeLogStack?_log0
    (offset size : EvmWord) (rest : List EvmWord) :
    decodeLogStack? .log0 (offset :: size :: rest) =
      some (mkArgs offset size []) := rfl

theorem decodeLogStack?_log1
    (offset size topic0 : EvmWord) (rest : List EvmWord) :
    decodeLogStack? .log1 (offset :: size :: topic0 :: rest) =
      some (mkArgs offset size [topic0]) := rfl

theorem decodeLogStack?_log2
    (offset size topic0 topic1 : EvmWord) (rest : List EvmWord) :
    decodeLogStack? .log2 (offset :: size :: topic0 :: topic1 :: rest) =
      some (mkArgs offset size [topic0, topic1]) := rfl

theorem decodeLogStack?_log3
    (offset size topic0 topic1 topic2 : EvmWord) (rest : List EvmWord) :
    decodeLogStack? .log3
      (offset :: size :: topic0 :: topic1 :: topic2 :: rest) =
      some (mkArgs offset size [topic0, topic1, topic2]) := rfl

theorem decodeLogStack?_log4
    (offset size topic0 topic1 topic2 topic3 : EvmWord)
    (rest : List EvmWord) :
    decodeLogStack? .log4
      (offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: rest) =
      some (mkArgs offset size [topic0, topic1, topic2, topic3]) := rfl

/--
LOG0 stack decoding succeeds exactly when the stack has at least an
`offset, size` pair on top.

Distinctive token: LogArgsStackDecode.decodeLogStack?_log0_eq_some_iff #112.
-/
theorem decodeLogStack?_log0_eq_some_iff
    (stack : List EvmWord) (decoded : Args) :
    decodeLogStack? .log0 stack = some decoded ↔
      ∃ offset size rest,
        stack = offset :: size :: rest ∧
        decoded = mkArgs offset size [] := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [decodeLogStack?] at h_decode
    | cons offset tail =>
        cases tail with
        | nil => simp [decodeLogStack?] at h_decode
        | cons size rest =>
            simp [decodeLogStack?] at h_decode
            cases h_decode
            exact ⟨offset, size, rest, rfl, rfl⟩
  · rintro ⟨offset, size, rest, rfl, rfl⟩
    rfl

theorem decodeLogStack?_log1_eq_some_iff
    (stack : List EvmWord) (decoded : Args) :
    decodeLogStack? .log1 stack = some decoded ↔
      ∃ offset size topic0 rest,
        stack = offset :: size :: topic0 :: rest ∧
        decoded = mkArgs offset size [topic0] := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨offset, _ | ⟨size, _ | ⟨topic0, rest⟩⟩⟩ <;>
      simp [decodeLogStack?] at h_decode
    cases h_decode
    exact ⟨offset, size, topic0, rest, rfl, rfl⟩
  · rintro ⟨offset, size, topic0, rest, rfl, rfl⟩
    rfl

theorem decodeLogStack?_log2_eq_some_iff
    (stack : List EvmWord) (decoded : Args) :
    decodeLogStack? .log2 stack = some decoded ↔
      ∃ offset size topic0 topic1 rest,
        stack = offset :: size :: topic0 :: topic1 :: rest ∧
        decoded = mkArgs offset size [topic0, topic1] := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨offset, _ | ⟨size, _ | ⟨topic0, _ | ⟨topic1, rest⟩⟩⟩⟩ <;>
      simp [decodeLogStack?] at h_decode
    cases h_decode
    exact ⟨offset, size, topic0, topic1, rest, rfl, rfl⟩
  · rintro ⟨offset, size, topic0, topic1, rest, rfl, rfl⟩
    rfl

theorem decodeLogStack?_log3_eq_some_iff
    (stack : List EvmWord) (decoded : Args) :
    decodeLogStack? .log3 stack = some decoded ↔
      ∃ offset size topic0 topic1 topic2 rest,
        stack = offset :: size :: topic0 :: topic1 :: topic2 :: rest ∧
        decoded = mkArgs offset size [topic0, topic1, topic2] := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨offset, _ | ⟨size, _ | ⟨topic0, _ | ⟨topic1, _ | ⟨topic2, rest⟩⟩⟩⟩⟩ <;>
      simp [decodeLogStack?] at h_decode
    cases h_decode
    exact ⟨offset, size, topic0, topic1, topic2, rest, rfl, rfl⟩
  · rintro ⟨offset, size, topic0, topic1, topic2, rest, rfl, rfl⟩
    rfl

theorem decodeLogStack?_log4_eq_some_iff
    (stack : List EvmWord) (decoded : Args) :
    decodeLogStack? .log4 stack = some decoded ↔
      ∃ offset size topic0 topic1 topic2 topic3 rest,
        stack = offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: rest ∧
        decoded = mkArgs offset size [topic0, topic1, topic2, topic3] := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨offset, _ | ⟨size, _ | ⟨topic0, _ | ⟨topic1, _ | ⟨topic2, _ | ⟨topic3, rest⟩⟩⟩⟩⟩⟩ <;>
      simp [decodeLogStack?] at h_decode
    cases h_decode
    exact ⟨offset, size, topic0, topic1, topic2, topic3, rest, rfl, rfl⟩
  · rintro ⟨offset, size, topic0, topic1, topic2, topic3, rest, rfl, rfl⟩
    rfl

theorem decodeLogStack?_eq_some_iff
    (kind : Kind) (stack : List EvmWord) (decoded : Args) :
    decodeLogStack? kind stack = some decoded ↔
      match kind with
      | .log0 =>
          ∃ offset size rest,
            stack = offset :: size :: rest ∧
            decoded = mkArgs offset size []
      | .log1 =>
          ∃ offset size topic0 rest,
            stack = offset :: size :: topic0 :: rest ∧
            decoded = mkArgs offset size [topic0]
      | .log2 =>
          ∃ offset size topic0 topic1 rest,
            stack = offset :: size :: topic0 :: topic1 :: rest ∧
            decoded = mkArgs offset size [topic0, topic1]
      | .log3 =>
          ∃ offset size topic0 topic1 topic2 rest,
            stack = offset :: size :: topic0 :: topic1 :: topic2 :: rest ∧
            decoded = mkArgs offset size [topic0, topic1, topic2]
      | .log4 =>
          ∃ offset size topic0 topic1 topic2 topic3 rest,
            stack = offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: rest ∧
            decoded = mkArgs offset size [topic0, topic1, topic2, topic3] := by
  cases kind
  · exact decodeLogStack?_log0_eq_some_iff stack decoded
  · exact decodeLogStack?_log1_eq_some_iff stack decoded
  · exact decodeLogStack?_log2_eq_some_iff stack decoded
  · exact decodeLogStack?_log3_eq_some_iff stack decoded
  · exact decodeLogStack?_log4_eq_some_iff stack decoded

/--
LOG-family stack decoding fails exactly when the stack is shorter than the
required number of stack arguments for that kind.

Distinctive token: LogArgsStackDecode.decodeLogStack?_log0_eq_none_iff #112.
-/
theorem decodeLogStack?_log0_eq_none_iff
    (stack : List EvmWord) :
    decodeLogStack? .log0 stack = none ↔
      stack.length < stackArgumentCount .log0 := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [stackArgumentCount, topicCount]
    | cons _ tail =>
        cases tail with
        | nil => simp [stackArgumentCount, topicCount]
        | cons _ _ => simp [decodeLogStack?] at h_decode
  · intro h_len
    cases stack with
    | nil => rfl
    | cons _ tail =>
        cases tail with
        | nil => rfl
        | cons _ _ =>
            simp [stackArgumentCount, topicCount] at h_len
            omega

theorem decodeLogStack?_log1_eq_none_iff
    (stack : List EvmWord) :
    decodeLogStack? .log1 stack = none ↔
      stack.length < stackArgumentCount .log1 := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [decodeLogStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · simp [stackArgumentCount, topicCount] at h_len
      omega

theorem decodeLogStack?_log2_eq_none_iff
    (stack : List EvmWord) :
    decodeLogStack? .log2 stack = none ↔
      stack.length < stackArgumentCount .log2 := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [decodeLogStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [stackArgumentCount, topicCount] at h_len
      omega

theorem decodeLogStack?_log3_eq_none_iff
    (stack : List EvmWord) :
    decodeLogStack? .log3 stack = none ↔
      stack.length < stackArgumentCount .log3 := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [decodeLogStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [stackArgumentCount, topicCount] at h_len
      omega

theorem decodeLogStack?_log4_eq_none_iff
    (stack : List EvmWord) :
    decodeLogStack? .log4 stack = none ↔
      stack.length < stackArgumentCount .log4 := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [stackArgumentCount, topicCount]
    · simp [decodeLogStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [stackArgumentCount, topicCount] at h_len
      omega

theorem decodeLogStack?_eq_none_iff
    (kind : Kind) (stack : List EvmWord) :
    decodeLogStack? kind stack = none ↔
      stack.length < stackArgumentCount kind := by
  cases kind with
  | log0 => exact decodeLogStack?_log0_eq_none_iff stack
  | log1 => exact decodeLogStack?_log1_eq_none_iff stack
  | log2 => exact decodeLogStack?_log2_eq_none_iff stack
  | log3 => exact decodeLogStack?_log3_eq_none_iff stack
  | log4 => exact decodeLogStack?_log4_eq_none_iff stack

theorem decodeLogStack?_log0_none_of_empty :
    decodeLogStack? .log0 [] = none := rfl

theorem decodeLogStack?_log0_none_of_one
    (offset : EvmWord) :
    decodeLogStack? .log0 [offset] = none := rfl

theorem decodeLogStack?_log1_none_of_empty :
    decodeLogStack? .log1 [] = none := rfl

theorem decodeLogStack?_log1_none_of_one
    (offset : EvmWord) :
    decodeLogStack? .log1 [offset] = none := rfl

theorem decodeLogStack?_log1_none_of_two
    (offset size : EvmWord) :
    decodeLogStack? .log1 [offset, size] = none := rfl

theorem decodeLogStack?_log2_none_of_empty :
    decodeLogStack? .log2 [] = none := rfl

theorem decodeLogStack?_log2_none_of_one
    (offset : EvmWord) :
    decodeLogStack? .log2 [offset] = none := rfl

theorem decodeLogStack?_log2_none_of_two
    (offset size : EvmWord) :
    decodeLogStack? .log2 [offset, size] = none := rfl

theorem decodeLogStack?_log2_none_of_three
    (offset size topic0 : EvmWord) :
    decodeLogStack? .log2 [offset, size, topic0] = none := rfl

theorem decodeLogStack?_log3_none_of_empty :
    decodeLogStack? .log3 [] = none := rfl

theorem decodeLogStack?_log3_none_of_one
    (offset : EvmWord) :
    decodeLogStack? .log3 [offset] = none := rfl

theorem decodeLogStack?_log3_none_of_two
    (offset size : EvmWord) :
    decodeLogStack? .log3 [offset, size] = none := rfl

theorem decodeLogStack?_log3_none_of_three
    (offset size topic0 : EvmWord) :
    decodeLogStack? .log3 [offset, size, topic0] = none := rfl

theorem decodeLogStack?_log3_none_of_four
    (offset size topic0 topic1 : EvmWord) :
    decodeLogStack? .log3 [offset, size, topic0, topic1] = none := rfl

theorem decodeLogStack?_log4_none_of_empty :
    decodeLogStack? .log4 [] = none := rfl

theorem decodeLogStack?_log4_none_of_one
    (offset : EvmWord) :
    decodeLogStack? .log4 [offset] = none := rfl

theorem decodeLogStack?_log4_none_of_two
    (offset size : EvmWord) :
    decodeLogStack? .log4 [offset, size] = none := rfl

theorem decodeLogStack?_log4_none_of_three
    (offset size topic0 : EvmWord) :
    decodeLogStack? .log4 [offset, size, topic0] = none := rfl

theorem decodeLogStack?_log4_none_of_four
    (offset size topic0 topic1 : EvmWord) :
    decodeLogStack? .log4 [offset, size, topic0, topic1] = none := rfl

theorem decodeLogStack?_log4_none_of_five
    (offset size topic0 topic1 topic2 : EvmWord) :
    decodeLogStack? .log4 [offset, size, topic0, topic1, topic2] = none := rfl

theorem decodeLogStack?_log0_topicCountOk
    (offset size : EvmWord) (_rest : List EvmWord) :
    topicCountOk .log0 (mkArgs offset size []) := rfl

theorem decodeLogStack?_log1_topicCountOk
    (offset size topic0 : EvmWord) (_rest : List EvmWord) :
    topicCountOk .log1 (mkArgs offset size [topic0]) := rfl

theorem decodeLogStack?_log2_topicCountOk
    (offset size topic0 topic1 : EvmWord) (_rest : List EvmWord) :
    topicCountOk .log2 (mkArgs offset size [topic0, topic1]) := rfl

theorem decodeLogStack?_log3_topicCountOk
    (offset size topic0 topic1 topic2 : EvmWord) (_rest : List EvmWord) :
    topicCountOk .log3 (mkArgs offset size [topic0, topic1, topic2]) := rfl

theorem decodeLogStack?_log4_topicCountOk
    (offset size topic0 topic1 topic2 topic3 : EvmWord)
    (_rest : List EvmWord) :
    topicCountOk .log4
      (mkArgs offset size [topic0, topic1, topic2, topic3]) := rfl

end LogArgsStackDecode

end EvmAsm.Evm64
