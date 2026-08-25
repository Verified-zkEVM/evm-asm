/-
  EvmAsm.Evm64.TerminatingArgsStackDecode

  Pure top-of-stack decoders for frame-terminating opcode arguments
  (GH #113).
-/

module

public import EvmAsm.Evm64.TerminatingArgs

@[expose] public section

namespace EvmAsm.Evm64

namespace TerminatingArgsStackDecode

open TerminatingArgs

inductive Decoded where
  | stop
  | return_ (args : Args)
  | revert (args : Args)
  | invalid
  | selfdestruct (beneficiary : EvmWord)
  deriving Repr

def decodedKind : Decoded → Kind
  | .stop => .stop
  | .return_ _ => .return_
  | .revert _ => .revert
  | .invalid => .invalid
  | .selfdestruct _ => .selfdestruct

def decodedData? : Decoded → Option MemoryRange
  | .return_ args => some (dataRange args)
  | .revert args => some (dataRange args)
  | _ => none

def decodedBeneficiary? : Decoded → Option EvmWord
  | .selfdestruct beneficiary => some beneficiary
  | _ => none

def decodedStackArgumentCount (decoded : Decoded) : Nat :=
  stackArgumentCount (decodedKind decoded)

/--
Decode RETURN stack arguments from the top-of-stack list order:
`offset, size`.

Distinctive token: TerminatingArgsStackDecode.decodeReturnStack? #113.
-/
def decodeReturnStack? : List EvmWord → Option Args
  | offset :: size :: _ => some (returnArgs offset size)
  | _ => none

/--
Decode REVERT stack arguments from the top-of-stack list order:
`offset, size`.
-/
def decodeRevertStack? : List EvmWord → Option Args
  | offset :: size :: _ => some (revertArgs offset size)
  | _ => none

/--
Decode SELFDESTRUCT stack arguments from the top-of-stack list order:
`beneficiary`.
-/
def decodeSelfdestructStack? : List EvmWord → Option EvmWord
  | beneficiary :: _ => some beneficiary
  | _ => none

/--
Decode frame-terminating opcode stack arguments by opcode kind.

Distinctive token: TerminatingArgsStackDecode.decodeTerminatingStack? #113.
-/
def decodeTerminatingStack? : Kind → List EvmWord → Option Decoded
  | .stop, _ => some .stop
  | .return_, offset :: size :: _ => some (.return_ (returnArgs offset size))
  | .revert, offset :: size :: _ => some (.revert (revertArgs offset size))
  | .invalid, _ => some .invalid
  | .selfdestruct, beneficiary :: _ => some (.selfdestruct beneficiary)
  | _, _ => none

theorem decodeReturnStack?_cons
    (offset size : EvmWord) (rest : List EvmWord) :
    decodeReturnStack? (offset :: size :: rest) =
      some (returnArgs offset size) := rfl

theorem decodeRevertStack?_cons
    (offset size : EvmWord) (rest : List EvmWord) :
    decodeRevertStack? (offset :: size :: rest) =
      some (revertArgs offset size) := rfl

theorem decodeSelfdestructStack?_cons
    (beneficiary : EvmWord) (rest : List EvmWord) :
    decodeSelfdestructStack? (beneficiary :: rest) =
      some beneficiary := rfl

theorem decodeTerminatingStack?_stop (stack : List EvmWord) :
    decodeTerminatingStack? .stop stack = some .stop := rfl

theorem decodeTerminatingStack?_return
    (offset size : EvmWord) (rest : List EvmWord) :
    decodeTerminatingStack? .return_ (offset :: size :: rest) =
      some (.return_ (returnArgs offset size)) := rfl

theorem decodeTerminatingStack?_revert
    (offset size : EvmWord) (rest : List EvmWord) :
    decodeTerminatingStack? .revert (offset :: size :: rest) =
      some (.revert (revertArgs offset size)) := rfl

theorem decodeTerminatingStack?_invalid (stack : List EvmWord) :
    decodeTerminatingStack? .invalid stack = some .invalid := rfl

theorem decodeTerminatingStack?_selfdestruct
    (beneficiary : EvmWord) (rest : List EvmWord) :
    decodeTerminatingStack? .selfdestruct (beneficiary :: rest) =
      some (.selfdestruct beneficiary) := rfl

theorem decodeReturnStack?_eq_some_iff
    {stack : List EvmWord} {args : Args} :
    decodeReturnStack? stack = some args ↔
      ∃ offset size rest,
        stack = offset :: size :: rest ∧ args = returnArgs offset size := by
  constructor
  · cases stack with
    | nil => simp [decodeReturnStack?]
    | cons offset s1 =>
      cases s1 with
      | nil => simp [decodeReturnStack?]
      | cons size rest =>
        intro h
        injection h with h_args
        subst h_args
        exact ⟨offset, size, rest, rfl, rfl⟩
  · rintro ⟨offset, size, rest, rfl, rfl⟩
    rfl

theorem decodeRevertStack?_eq_some_iff
    {stack : List EvmWord} {args : Args} :
    decodeRevertStack? stack = some args ↔
      ∃ offset size rest,
        stack = offset :: size :: rest ∧ args = revertArgs offset size := by
  constructor
  · cases stack with
    | nil => simp [decodeRevertStack?]
    | cons offset s1 =>
      cases s1 with
      | nil => simp [decodeRevertStack?]
      | cons size rest =>
        intro h
        injection h with h_args
        subst h_args
        exact ⟨offset, size, rest, rfl, rfl⟩
  · rintro ⟨offset, size, rest, rfl, rfl⟩
    rfl

theorem decodeSelfdestructStack?_eq_some_iff
    {stack : List EvmWord} {beneficiary : EvmWord} :
    decodeSelfdestructStack? stack = some beneficiary ↔
      ∃ rest, stack = beneficiary :: rest := by
  constructor
  · cases stack with
    | nil => simp [decodeSelfdestructStack?]
    | cons head rest =>
      intro h
      injection h with h_eq
      subst h_eq
      exact ⟨rest, rfl⟩
  · rintro ⟨rest, rfl⟩
    rfl

theorem decodeTerminatingStack?_stop_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeTerminatingStack? .stop stack = some decoded ↔ decoded = .stop := by
  constructor
  · intro h_decode
    injection h_decode with h_decoded
    exact h_decoded.symm
  · intro h_decoded
    subst h_decoded
    rfl

theorem decodeTerminatingStack?_return_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeTerminatingStack? .return_ stack = some decoded ↔
      ∃ offset size rest,
        stack = offset :: size :: rest ∧
          decoded = .return_ (returnArgs offset size) := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨offset, _ | ⟨size, rest⟩⟩ <;>
      simp [decodeTerminatingStack?] at h_decode
    cases h_decode
    exact ⟨offset, size, rest, rfl, rfl⟩
  · rintro ⟨offset, size, rest, rfl, rfl⟩
    rfl

theorem decodeTerminatingStack?_revert_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeTerminatingStack? .revert stack = some decoded ↔
      ∃ offset size rest,
        stack = offset :: size :: rest ∧
          decoded = .revert (revertArgs offset size) := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨offset, _ | ⟨size, rest⟩⟩ <;>
      simp [decodeTerminatingStack?] at h_decode
    cases h_decode
    exact ⟨offset, size, rest, rfl, rfl⟩
  · rintro ⟨offset, size, rest, rfl, rfl⟩
    rfl

theorem decodeTerminatingStack?_invalid_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeTerminatingStack? .invalid stack = some decoded ↔ decoded = .invalid := by
  constructor
  · intro h_decode
    injection h_decode with h_decoded
    exact h_decoded.symm
  · intro h_decoded
    subst h_decoded
    rfl

theorem decodeTerminatingStack?_selfdestruct_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeTerminatingStack? .selfdestruct stack = some decoded ↔
      ∃ beneficiary rest,
        stack = beneficiary :: rest ∧
          decoded = .selfdestruct beneficiary := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨beneficiary, rest⟩ <;>
      simp [decodeTerminatingStack?] at h_decode
    cases h_decode
    exact ⟨beneficiary, rest, rfl, rfl⟩
  · rintro ⟨beneficiary, rest, rfl, rfl⟩
    rfl

theorem decodeTerminatingStack?_eq_some_iff
    (kind : Kind) (stack : List EvmWord) (decoded : Decoded) :
    decodeTerminatingStack? kind stack = some decoded ↔
      match kind with
      | .stop => decoded = .stop
      | .return_ =>
          ∃ offset size rest,
            stack = offset :: size :: rest ∧
              decoded = .return_ (returnArgs offset size)
      | .revert =>
          ∃ offset size rest,
            stack = offset :: size :: rest ∧
              decoded = .revert (revertArgs offset size)
      | .invalid => decoded = .invalid
      | .selfdestruct =>
          ∃ beneficiary rest,
            stack = beneficiary :: rest ∧
              decoded = .selfdestruct beneficiary := by
  cases kind with
  | stop => exact decodeTerminatingStack?_stop_eq_some_iff stack decoded
  | return_ => exact decodeTerminatingStack?_return_eq_some_iff stack decoded
  | revert => exact decodeTerminatingStack?_revert_eq_some_iff stack decoded
  | invalid => exact decodeTerminatingStack?_invalid_eq_some_iff stack decoded
  | selfdestruct =>
      exact decodeTerminatingStack?_selfdestruct_eq_some_iff stack decoded

/--
Failure characterization for `decodeReturnStack?`: the decoder returns `none`
exactly when the stack has fewer than 2 elements.

Distinctive token: TerminatingArgsStackDecode.decodeReturnStack?_eq_none_iff #113.
-/
theorem decodeReturnStack?_eq_none_iff (stack : List EvmWord) :
    decodeReturnStack? stack = none ↔ stack.length < 2 := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩
    · simp
    · simp
    · simp [decodeReturnStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩
    · rfl
    · rfl
    · simp at h_len
      omega

/--
Failure characterization for `decodeRevertStack?`: the decoder returns `none`
exactly when the stack has fewer than 2 elements.
-/
theorem decodeRevertStack?_eq_none_iff (stack : List EvmWord) :
    decodeRevertStack? stack = none ↔ stack.length < 2 := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩
    · simp
    · simp
    · simp [decodeRevertStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩
    · rfl
    · rfl
    · simp at h_len
      omega

/--
Failure characterization for `decodeSelfdestructStack?`: the decoder returns
`none` exactly when the stack is empty.
-/
theorem decodeSelfdestructStack?_eq_none_iff (stack : List EvmWord) :
    decodeSelfdestructStack? stack = none ↔ stack.length < 1 := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _⟩
    · simp
    · simp [decodeSelfdestructStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _⟩
    · rfl
    · simp at h_len

theorem decodeTerminatingStack?_stop_eq_none_iff (stack : List EvmWord) :
    decodeTerminatingStack? .stop stack = none ↔
      stack.length < stackArgumentCount .stop := by
  simp [decodeTerminatingStack?, stackArgumentCount]

theorem decodeTerminatingStack?_return_eq_none_iff (stack : List EvmWord) :
    decodeTerminatingStack? .return_ stack = none ↔
      stack.length < stackArgumentCount .return_ := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩
    · simp [stackArgumentCount]
    · simp [stackArgumentCount]
    · simp [decodeTerminatingStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩
    · rfl
    · rfl
    · simp [stackArgumentCount] at h_len
      omega

theorem decodeTerminatingStack?_revert_eq_none_iff (stack : List EvmWord) :
    decodeTerminatingStack? .revert stack = none ↔
      stack.length < stackArgumentCount .revert := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩
    · simp [stackArgumentCount]
    · simp [stackArgumentCount]
    · simp [decodeTerminatingStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩
    · rfl
    · rfl
    · simp [stackArgumentCount] at h_len
      omega

theorem decodeTerminatingStack?_invalid_eq_none_iff (stack : List EvmWord) :
    decodeTerminatingStack? .invalid stack = none ↔
      stack.length < stackArgumentCount .invalid := by
  simp [decodeTerminatingStack?, stackArgumentCount]

theorem decodeTerminatingStack?_selfdestruct_eq_none_iff (stack : List EvmWord) :
    decodeTerminatingStack? .selfdestruct stack = none ↔
      stack.length < stackArgumentCount .selfdestruct := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _⟩
    · simp [stackArgumentCount]
    · simp [decodeTerminatingStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _⟩
    · rfl
    · simp [stackArgumentCount] at h_len

theorem decodeTerminatingStack?_eq_none_iff (kind : Kind) (stack : List EvmWord) :
    decodeTerminatingStack? kind stack = none ↔
      stack.length < stackArgumentCount kind := by
  cases kind with
  | stop => exact decodeTerminatingStack?_stop_eq_none_iff stack
  | return_ => exact decodeTerminatingStack?_return_eq_none_iff stack
  | revert => exact decodeTerminatingStack?_revert_eq_none_iff stack
  | invalid => exact decodeTerminatingStack?_invalid_eq_none_iff stack
  | selfdestruct => exact decodeTerminatingStack?_selfdestruct_eq_none_iff stack

/--
`decodeReturnStack?` returns `none` on the empty stack.

Distinctive token: TerminatingArgsStackDecode.decodeReturnStack?_none_of_empty #113.
-/
theorem decodeReturnStack?_none_of_empty :
    decodeReturnStack? ([] : List EvmWord) = none := rfl

/--
`decodeReturnStack?` returns `none` when the stack has only one element
(RETURN consumes two: offset and size).
-/
theorem decodeReturnStack?_none_of_one (offset : EvmWord) :
    decodeReturnStack? [offset] = none := rfl

/--
`decodeRevertStack?` returns `none` on the empty stack.
-/
theorem decodeRevertStack?_none_of_empty :
    decodeRevertStack? ([] : List EvmWord) = none := rfl

/--
`decodeRevertStack?` returns `none` when the stack has only one element
(REVERT consumes two: offset and size).
-/
theorem decodeRevertStack?_none_of_one (offset : EvmWord) :
    decodeRevertStack? [offset] = none := rfl

/--
`decodeSelfdestructStack?` returns `none` on the empty stack
(SELFDESTRUCT consumes one: beneficiary).
-/
theorem decodeSelfdestructStack?_none_of_empty :
    decodeSelfdestructStack? ([] : List EvmWord) = none := rfl

theorem decodeReturnStack?_dataRange
    (offset size : EvmWord) (rest : List EvmWord) :
    dataRange (Option.getD
      (decodeReturnStack? (offset :: size :: rest))
      (returnArgs 0 0)) =
      { offset := offset, size := size } := rfl

theorem decodeRevertStack?_dataRange
    (offset size : EvmWord) (rest : List EvmWord) :
    dataRange (Option.getD
      (decodeRevertStack? (offset :: size :: rest))
      (revertArgs 0 0)) =
      { offset := offset, size := size } := rfl

theorem decodedKind_stop :
    decodedKind .stop = .stop := rfl

theorem decodedKind_return (offset size : EvmWord) :
    decodedKind (.return_ (returnArgs offset size)) = .return_ := rfl

theorem decodedKind_revert (offset size : EvmWord) :
    decodedKind (.revert (revertArgs offset size)) = .revert := rfl

theorem decodedKind_invalid :
    decodedKind .invalid = .invalid := rfl

theorem decodedKind_selfdestruct (beneficiary : EvmWord) :
    decodedKind (.selfdestruct beneficiary) = .selfdestruct := rfl

theorem decodedData?_stop :
    decodedData? .stop = none := rfl

theorem decodedData?_return (offset size : EvmWord) :
    decodedData? (.return_ (returnArgs offset size)) =
      some { offset := offset, size := size } := rfl

theorem decodedData?_revert (offset size : EvmWord) :
    decodedData? (.revert (revertArgs offset size)) =
      some { offset := offset, size := size } := rfl

theorem decodedData?_invalid :
    decodedData? .invalid = none := rfl

theorem decodedData?_selfdestruct (beneficiary : EvmWord) :
    decodedData? (.selfdestruct beneficiary) = none := rfl

theorem decodedBeneficiary?_selfdestruct (beneficiary : EvmWord) :
    decodedBeneficiary? (.selfdestruct beneficiary) = some beneficiary := rfl

theorem decodedBeneficiary?_return (offset size : EvmWord) :
    decodedBeneficiary? (.return_ (returnArgs offset size)) = none := rfl

theorem decodedStackArgumentCount_return (offset size : EvmWord) :
    decodedStackArgumentCount (.return_ (returnArgs offset size)) = 2 := rfl

theorem decodedStackArgumentCount_revert (offset size : EvmWord) :
    decodedStackArgumentCount (.revert (revertArgs offset size)) = 2 := rfl

theorem decodedStackArgumentCount_selfdestruct (beneficiary : EvmWord) :
    decodedStackArgumentCount (.selfdestruct beneficiary) = 1 := rfl

end TerminatingArgsStackDecode

end EvmAsm.Evm64
