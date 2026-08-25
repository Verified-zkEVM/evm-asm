/-
  EvmAsm.Evm64.CallArgsStackDecode

  Pure top-of-stack decoders for CALL-family argument records (GH #114).
-/

module

public import EvmAsm.Evm64.CallArgs

@[expose] public section

namespace EvmAsm.Evm64

namespace CallArgsStackDecode

open CallArgs

inductive Decoded where
  | call (args : Call)
  | staticcall (args : StaticCall)
  | delegatecall (args : DelegateCall)
  deriving Repr

def mkCall
    (gas to value inputOffset inputSize outputOffset outputSize : EvmWord) :
    Call :=
  { gas := gas
    to := to
    value := value
    input := { offset := inputOffset, size := inputSize }
    output := { offset := outputOffset, size := outputSize } }

def mkStaticCall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord) :
    StaticCall :=
  { gas := gas
    to := to
    input := { offset := inputOffset, size := inputSize }
    output := { offset := outputOffset, size := outputSize } }

def mkDelegateCall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord) :
    DelegateCall :=
  { gas := gas
    to := to
    input := { offset := inputOffset, size := inputSize }
    output := { offset := outputOffset, size := outputSize } }

def decodedKind : Decoded → Kind
  | .call _ => .call
  | .staticcall _ => .staticcall
  | .delegatecall _ => .delegatecall

def decodedInput : Decoded → MemoryRange
  | .call args => args.input
  | .staticcall args => args.input
  | .delegatecall args => args.input

def decodedOutput : Decoded → MemoryRange
  | .call args => args.output
  | .staticcall args => args.output
  | .delegatecall args => args.output

def decodedArgumentCount (decoded : Decoded) : Nat :=
  argumentCount (decodedKind decoded)

/--
Decode CALL stack arguments from the top-of-stack list order:
`gas, to, value, input_offset, input_size, output_offset, output_size`.

Distinctive token: CallArgsStackDecode.decodeCallStack? #114.
-/
def decodeCallStack? : List EvmWord → Option Call
  | gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
      outputSize :: _ =>
      some
        { gas := gas
          to := to
          value := value
          input := { offset := inputOffset, size := inputSize }
          output := { offset := outputOffset, size := outputSize } }
  | _ => none

/--
Decode STATICCALL stack arguments from the top-of-stack list order:
`gas, to, input_offset, input_size, output_offset, output_size`.
-/
def decodeStaticCallStack? : List EvmWord → Option StaticCall
  | gas :: to :: inputOffset :: inputSize :: outputOffset :: outputSize :: _ =>
      some
        { gas := gas
          to := to
          input := { offset := inputOffset, size := inputSize }
          output := { offset := outputOffset, size := outputSize } }
  | _ => none

/--
Decode DELEGATECALL stack arguments from the top-of-stack list order:
`gas, to, input_offset, input_size, output_offset, output_size`.
-/
def decodeDelegateCallStack? : List EvmWord → Option DelegateCall
  | gas :: to :: inputOffset :: inputSize :: outputOffset :: outputSize :: _ =>
      some
        (mkDelegateCall gas to inputOffset inputSize outputOffset outputSize)
  | _ => none

/--
Decode CALL-family stack arguments by opcode kind.

Distinctive token: CallArgsStackDecode.decodeCallFamilyStack? #114.
-/
def decodeCallFamilyStack? : Kind → List EvmWord → Option Decoded
  | .call, gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
      outputSize :: _ =>
      some (.call (mkCall gas to value inputOffset inputSize outputOffset outputSize))
  | .staticcall, gas :: to :: inputOffset :: inputSize :: outputOffset ::
      outputSize :: _ =>
      some (.staticcall
        (mkStaticCall gas to inputOffset inputSize outputOffset outputSize))
  | .delegatecall, gas :: to :: inputOffset :: inputSize :: outputOffset ::
      outputSize :: _ =>
      some (.delegatecall
        (mkDelegateCall gas to inputOffset inputSize outputOffset outputSize))
  | _, _ => none

theorem decodeCallStack?_cons
    (gas to value inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    decodeCallStack?
      (gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
        outputSize :: rest) =
      some
        { gas := gas
          to := to
          value := value
          input := { offset := inputOffset, size := inputSize }
          output := { offset := outputOffset, size := outputSize } } := rfl

theorem decodeStaticCallStack?_cons
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    decodeStaticCallStack?
      (gas :: to :: inputOffset :: inputSize :: outputOffset ::
        outputSize :: rest) =
      some
        { gas := gas
          to := to
          input := { offset := inputOffset, size := inputSize }
          output := { offset := outputOffset, size := outputSize } } := rfl

theorem decodeDelegateCallStack?_cons
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    decodeDelegateCallStack?
      (gas :: to :: inputOffset :: inputSize :: outputOffset ::
        outputSize :: rest) =
      some
        { gas := gas
          to := to
          input := { offset := inputOffset, size := inputSize }
          output := { offset := outputOffset, size := outputSize } } := rfl

theorem decodeCallFamilyStack?_call
    (gas to value inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    decodeCallFamilyStack? .call
      (gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
        outputSize :: rest) =
      some (.call
        (mkCall gas to value inputOffset inputSize outputOffset outputSize)) := rfl

theorem decodeCallFamilyStack?_staticcall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    decodeCallFamilyStack? .staticcall
      (gas :: to :: inputOffset :: inputSize :: outputOffset ::
        outputSize :: rest) =
      some (.staticcall
        (mkStaticCall gas to inputOffset inputSize outputOffset outputSize)) := rfl

theorem decodeCallFamilyStack?_delegatecall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    decodeCallFamilyStack? .delegatecall
      (gas :: to :: inputOffset :: inputSize :: outputOffset ::
        outputSize :: rest) =
      some (.delegatecall
        (mkDelegateCall gas to inputOffset inputSize outputOffset outputSize)) := rfl

theorem decodeCallFamilyStack?_input_call
    (gas to value inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    Option.map decodedInput
      (decodeCallFamilyStack? .call
        (gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
          outputSize :: rest)) =
      some { offset := inputOffset, size := inputSize } := rfl

theorem decodeCallFamilyStack?_input_staticcall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    Option.map decodedInput
      (decodeCallFamilyStack? .staticcall
        (gas :: to :: inputOffset :: inputSize :: outputOffset ::
          outputSize :: rest)) =
      some { offset := inputOffset, size := inputSize } := rfl

theorem decodeCallFamilyStack?_input_delegatecall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    Option.map decodedInput
      (decodeCallFamilyStack? .delegatecall
        (gas :: to :: inputOffset :: inputSize :: outputOffset ::
          outputSize :: rest)) =
      some { offset := inputOffset, size := inputSize } := rfl

theorem decodeCallFamilyStack?_output_call
    (gas to value inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    Option.map decodedOutput
      (decodeCallFamilyStack? .call
        (gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
          outputSize :: rest)) =
      some { offset := outputOffset, size := outputSize } := rfl

theorem decodeCallFamilyStack?_output_staticcall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    Option.map decodedOutput
      (decodeCallFamilyStack? .staticcall
        (gas :: to :: inputOffset :: inputSize :: outputOffset ::
          outputSize :: rest)) =
      some { offset := outputOffset, size := outputSize } := rfl

theorem decodeCallFamilyStack?_output_delegatecall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    Option.map decodedOutput
      (decodeCallFamilyStack? .delegatecall
        (gas :: to :: inputOffset :: inputSize :: outputOffset ::
          outputSize :: rest)) =
      some { offset := outputOffset, size := outputSize } := rfl

theorem decodeCallStack?_eq_some_iff {stack : List EvmWord} {args : Call} :
    decodeCallStack? stack = some args ↔
      ∃ gas to value inputOffset inputSize outputOffset outputSize rest,
        stack =
          gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
            outputSize :: rest ∧
        args =
          { gas := gas
            to := to
            value := value
            input := { offset := inputOffset, size := inputSize }
            output := { offset := outputOffset, size := outputSize } } := by
  constructor
  · cases stack with
    | nil => simp [decodeCallStack?]
    | cons gas s1 =>
      cases s1 with
      | nil => simp [decodeCallStack?]
      | cons to s2 =>
        cases s2 with
        | nil => simp [decodeCallStack?]
        | cons value s3 =>
          cases s3 with
          | nil => simp [decodeCallStack?]
          | cons inputOffset s4 =>
            cases s4 with
            | nil => simp [decodeCallStack?]
            | cons inputSize s5 =>
              cases s5 with
              | nil => simp [decodeCallStack?]
              | cons outputOffset s6 =>
                cases s6 with
                | nil => simp [decodeCallStack?]
                | cons outputSize rest =>
                  intro h
                  injection h with h_args
                  subst h_args
                  exact ⟨gas, to, value, inputOffset, inputSize, outputOffset,
                    outputSize, rest, rfl, rfl⟩
  · rintro ⟨gas, to, value, inputOffset, inputSize, outputOffset, outputSize,
      rest, rfl, rfl⟩
    rfl

theorem decodeStaticCallStack?_eq_some_iff
    {stack : List EvmWord} {args : StaticCall} :
    decodeStaticCallStack? stack = some args ↔
      ∃ gas to inputOffset inputSize outputOffset outputSize rest,
        stack =
          gas :: to :: inputOffset :: inputSize :: outputOffset ::
            outputSize :: rest ∧
        args =
          { gas := gas
            to := to
            input := { offset := inputOffset, size := inputSize }
            output := { offset := outputOffset, size := outputSize } } := by
  constructor
  · cases stack with
    | nil => simp [decodeStaticCallStack?]
    | cons gas s1 =>
      cases s1 with
      | nil => simp [decodeStaticCallStack?]
      | cons to s2 =>
        cases s2 with
        | nil => simp [decodeStaticCallStack?]
        | cons inputOffset s3 =>
          cases s3 with
          | nil => simp [decodeStaticCallStack?]
          | cons inputSize s4 =>
            cases s4 with
            | nil => simp [decodeStaticCallStack?]
            | cons outputOffset s5 =>
              cases s5 with
              | nil => simp [decodeStaticCallStack?]
              | cons outputSize rest =>
                intro h
                injection h with h_args
                subst h_args
                exact ⟨gas, to, inputOffset, inputSize, outputOffset,
                  outputSize, rest, rfl, rfl⟩
  · rintro ⟨gas, to, inputOffset, inputSize, outputOffset, outputSize, rest,
      rfl, rfl⟩
    rfl

theorem decodeDelegateCallStack?_eq_some_iff
    {stack : List EvmWord} {args : DelegateCall} :
    decodeDelegateCallStack? stack = some args ↔
      ∃ gas to inputOffset inputSize outputOffset outputSize rest,
        stack =
          gas :: to :: inputOffset :: inputSize :: outputOffset ::
            outputSize :: rest ∧
        args =
          { gas := gas
            to := to
            input := { offset := inputOffset, size := inputSize }
            output := { offset := outputOffset, size := outputSize } } := by
  constructor
  · cases stack with
    | nil => simp [decodeDelegateCallStack?]
    | cons gas s1 =>
      cases s1 with
      | nil => simp [decodeDelegateCallStack?]
      | cons to s2 =>
        cases s2 with
        | nil => simp [decodeDelegateCallStack?]
        | cons inputOffset s3 =>
          cases s3 with
          | nil => simp [decodeDelegateCallStack?]
          | cons inputSize s4 =>
            cases s4 with
            | nil => simp [decodeDelegateCallStack?]
            | cons outputOffset s5 =>
              cases s5 with
              | nil => simp [decodeDelegateCallStack?]
              | cons outputSize rest =>
                intro h
                injection h with h_args
                subst h_args
                exact ⟨gas, to, inputOffset, inputSize, outputOffset,
                  outputSize, rest, rfl, rfl⟩
  · rintro ⟨gas, to, inputOffset, inputSize, outputOffset, outputSize, rest,
      rfl, rfl⟩
    rfl

theorem decodeCallFamilyStack?_call_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeCallFamilyStack? .call stack = some decoded ↔
      ∃ gas to value inputOffset inputSize outputOffset outputSize rest,
        stack =
          gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
            outputSize :: rest ∧
        decoded =
          .call
            (mkCall gas to value inputOffset inputSize outputOffset outputSize) := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨gas, _ | ⟨to, _ | ⟨value, _ | ⟨inputOffset,
        _ | ⟨inputSize, _ | ⟨outputOffset, _ | ⟨outputSize, rest⟩⟩⟩⟩⟩⟩⟩ <;>
      simp [decodeCallFamilyStack?] at h_decode
    cases h_decode
    exact ⟨gas, to, value, inputOffset, inputSize, outputOffset,
      outputSize, rest, rfl, rfl⟩
  · rintro ⟨gas, to, value, inputOffset, inputSize, outputOffset, outputSize,
      rest, rfl, rfl⟩
    rfl

theorem decodeCallFamilyStack?_staticcall_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeCallFamilyStack? .staticcall stack = some decoded ↔
      ∃ gas to inputOffset inputSize outputOffset outputSize rest,
        stack =
          gas :: to :: inputOffset :: inputSize :: outputOffset ::
            outputSize :: rest ∧
        decoded =
          .staticcall
            (mkStaticCall gas to inputOffset inputSize outputOffset outputSize) := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨gas, _ | ⟨to, _ | ⟨inputOffset,
        _ | ⟨inputSize, _ | ⟨outputOffset, _ | ⟨outputSize, rest⟩⟩⟩⟩⟩⟩ <;>
      simp [decodeCallFamilyStack?] at h_decode
    cases h_decode
    exact ⟨gas, to, inputOffset, inputSize, outputOffset, outputSize,
      rest, rfl, rfl⟩
  · rintro ⟨gas, to, inputOffset, inputSize, outputOffset, outputSize, rest,
      rfl, rfl⟩
    rfl

theorem decodeCallFamilyStack?_delegatecall_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeCallFamilyStack? .delegatecall stack = some decoded ↔
      ∃ gas to inputOffset inputSize outputOffset outputSize rest,
        stack =
          gas :: to :: inputOffset :: inputSize :: outputOffset ::
            outputSize :: rest ∧
        decoded =
          .delegatecall
            (mkDelegateCall gas to inputOffset inputSize outputOffset outputSize) := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨gas, _ | ⟨to, _ | ⟨inputOffset,
        _ | ⟨inputSize, _ | ⟨outputOffset, _ | ⟨outputSize, rest⟩⟩⟩⟩⟩⟩ <;>
      simp [decodeCallFamilyStack?] at h_decode
    cases h_decode
    exact ⟨gas, to, inputOffset, inputSize, outputOffset, outputSize,
      rest, rfl, rfl⟩
  · rintro ⟨gas, to, inputOffset, inputSize, outputOffset, outputSize, rest,
      rfl, rfl⟩
    rfl

theorem decodeCallFamilyStack?_eq_some_iff
    (kind : Kind) (stack : List EvmWord) (decoded : Decoded) :
    decodeCallFamilyStack? kind stack = some decoded ↔
      match kind with
      | .call =>
          ∃ gas to value inputOffset inputSize outputOffset outputSize rest,
            stack =
              gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
                outputSize :: rest ∧
            decoded =
              .call
                (mkCall gas to value inputOffset inputSize outputOffset outputSize)
      | .staticcall =>
          ∃ gas to inputOffset inputSize outputOffset outputSize rest,
            stack =
              gas :: to :: inputOffset :: inputSize :: outputOffset ::
                outputSize :: rest ∧
            decoded =
              .staticcall
                (mkStaticCall gas to inputOffset inputSize outputOffset outputSize)
      | .delegatecall =>
          ∃ gas to inputOffset inputSize outputOffset outputSize rest,
            stack =
              gas :: to :: inputOffset :: inputSize :: outputOffset ::
                outputSize :: rest ∧
            decoded =
              .delegatecall
                (mkDelegateCall gas to inputOffset inputSize outputOffset outputSize) := by
  cases kind with
  | call => exact decodeCallFamilyStack?_call_eq_some_iff stack decoded
  | staticcall => exact decodeCallFamilyStack?_staticcall_eq_some_iff stack decoded
  | delegatecall => exact decodeCallFamilyStack?_delegatecall_eq_some_iff stack decoded

theorem decodeCallFamilyStack?_kind_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeCallFamilyStack? kind stack = some decoded) :
    decodedKind decoded = kind := by
  cases kind with
  | call =>
      rcases (decodeCallFamilyStack?_call_eq_some_iff stack decoded).mp h_decode with
        ⟨_, _, _, _, _, _, _, _, _, h_decoded⟩
      subst h_decoded
      rfl
  | staticcall =>
      rcases (decodeCallFamilyStack?_staticcall_eq_some_iff stack decoded).mp h_decode with
        ⟨_, _, _, _, _, _, _, _, h_decoded⟩
      subst h_decoded
      rfl
  | delegatecall =>
      rcases (decodeCallFamilyStack?_delegatecall_eq_some_iff stack decoded).mp h_decode with
        ⟨_, _, _, _, _, _, _, _, h_decoded⟩
      subst h_decoded
      rfl

theorem decodeCallFamilyStack?_argumentCount_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeCallFamilyStack? kind stack = some decoded) :
    decodedArgumentCount decoded = argumentCount kind := by
  rw [decodedArgumentCount, decodeCallFamilyStack?_kind_of_some h_decode]

theorem decodeCallStack?_eq_none_iff (stack : List EvmWord) :
    decodeCallStack? stack = none ↔ stack.length < 7 := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp [decodeCallStack?] at h_decode
  · intro h_len
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp at h_len
      omega

theorem decodeStaticCallStack?_eq_none_iff (stack : List EvmWord) :
    decodeStaticCallStack? stack = none ↔ stack.length < 6 := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp [decodeStaticCallStack?] at h_decode
  · intro h_len
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp at h_len
      omega

theorem decodeDelegateCallStack?_eq_none_iff (stack : List EvmWord) :
    decodeDelegateCallStack? stack = none ↔ stack.length < 6 := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp [decodeDelegateCallStack?] at h_decode
  · intro h_len
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp at h_len
      omega

theorem decodeCallFamilyStack?_call_eq_none_iff (stack : List EvmWord) :
    decodeCallFamilyStack? .call stack = none ↔ stack.length < argumentCount .call := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [decodeCallFamilyStack?] at h_decode
  · intro h_len
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [argumentCount] at h_len
      omega

theorem decodeCallFamilyStack?_staticcall_eq_none_iff (stack : List EvmWord) :
    decodeCallFamilyStack? .staticcall stack = none ↔
      stack.length < argumentCount .staticcall := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [decodeCallFamilyStack?] at h_decode
  · intro h_len
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [argumentCount] at h_len
      omega

theorem decodeCallFamilyStack?_delegatecall_eq_none_iff (stack : List EvmWord) :
    decodeCallFamilyStack? .delegatecall stack = none ↔
      stack.length < argumentCount .delegatecall := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [decodeCallFamilyStack?] at h_decode
  · intro h_len
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [argumentCount] at h_len
      omega

theorem decodeCallFamilyStack?_eq_none_iff (kind : Kind) (stack : List EvmWord) :
    decodeCallFamilyStack? kind stack = none ↔ stack.length < argumentCount kind := by
  cases kind with
  | call => exact decodeCallFamilyStack?_call_eq_none_iff stack
  | staticcall => exact decodeCallFamilyStack?_staticcall_eq_none_iff stack
  | delegatecall => exact decodeCallFamilyStack?_delegatecall_eq_none_iff stack

theorem decodeCallStack?_none_of_empty :
    decodeCallStack? [] = none := rfl

theorem decodeCallStack?_none_of_one
    (gas : EvmWord) :
    decodeCallStack? [gas] = none := rfl

theorem decodeCallStack?_none_of_two
    (gas to : EvmWord) :
    decodeCallStack? [gas, to] = none := rfl

theorem decodeCallStack?_none_of_three
    (gas to value : EvmWord) :
    decodeCallStack? [gas, to, value] = none := rfl

theorem decodeCallStack?_none_of_four
    (gas to value inputOffset : EvmWord) :
    decodeCallStack? [gas, to, value, inputOffset] = none := rfl

theorem decodeCallStack?_none_of_five
    (gas to value inputOffset inputSize : EvmWord) :
    decodeCallStack? [gas, to, value, inputOffset, inputSize] = none := rfl

theorem decodeCallStack?_none_of_six
    (gas to value inputOffset inputSize outputOffset : EvmWord) :
    decodeCallStack?
      [gas, to, value, inputOffset, inputSize, outputOffset] = none := rfl

theorem decodeStaticCallStack?_none_of_empty :
    decodeStaticCallStack? [] = none := rfl

theorem decodeStaticCallStack?_none_of_one
    (gas : EvmWord) :
    decodeStaticCallStack? [gas] = none := rfl

theorem decodeStaticCallStack?_none_of_two
    (gas to : EvmWord) :
    decodeStaticCallStack? [gas, to] = none := rfl

theorem decodeStaticCallStack?_none_of_three
    (gas to inputOffset : EvmWord) :
    decodeStaticCallStack? [gas, to, inputOffset] = none := rfl

theorem decodeStaticCallStack?_none_of_four
    (gas to inputOffset inputSize : EvmWord) :
    decodeStaticCallStack? [gas, to, inputOffset, inputSize] = none := rfl

theorem decodeStaticCallStack?_none_of_five
    (gas to inputOffset inputSize outputOffset : EvmWord) :
    decodeStaticCallStack?
      [gas, to, inputOffset, inputSize, outputOffset] = none := rfl

theorem decodeDelegateCallStack?_none_of_empty :
    decodeDelegateCallStack? [] = none := rfl

theorem decodeDelegateCallStack?_none_of_one
    (gas : EvmWord) :
    decodeDelegateCallStack? [gas] = none := rfl

theorem decodeDelegateCallStack?_none_of_two
    (gas to : EvmWord) :
    decodeDelegateCallStack? [gas, to] = none := rfl

theorem decodeDelegateCallStack?_none_of_three
    (gas to inputOffset : EvmWord) :
    decodeDelegateCallStack? [gas, to, inputOffset] = none := rfl

theorem decodeDelegateCallStack?_none_of_four
    (gas to inputOffset inputSize : EvmWord) :
    decodeDelegateCallStack? [gas, to, inputOffset, inputSize] = none := rfl

theorem decodeDelegateCallStack?_none_of_five
    (gas to inputOffset inputSize outputOffset : EvmWord) :
    decodeDelegateCallStack?
      [gas, to, inputOffset, inputSize, outputOffset] = none := rfl

theorem decodeCallFamilyStack?_call_none_of_empty :
    decodeCallFamilyStack? .call [] = none := rfl

theorem decodeCallFamilyStack?_call_none_of_one
    (gas : EvmWord) :
    decodeCallFamilyStack? .call [gas] = none := rfl

theorem decodeCallFamilyStack?_call_none_of_two
    (gas to : EvmWord) :
    decodeCallFamilyStack? .call [gas, to] = none := rfl

theorem decodeCallFamilyStack?_call_none_of_three
    (gas to value : EvmWord) :
    decodeCallFamilyStack? .call [gas, to, value] = none := rfl

theorem decodeCallFamilyStack?_call_none_of_four
    (gas to value inputOffset : EvmWord) :
    decodeCallFamilyStack? .call [gas, to, value, inputOffset] = none := rfl

theorem decodeCallFamilyStack?_call_none_of_five
    (gas to value inputOffset inputSize : EvmWord) :
    decodeCallFamilyStack? .call
      [gas, to, value, inputOffset, inputSize] = none := rfl

theorem decodeCallFamilyStack?_call_none_of_six
    (gas to value inputOffset inputSize outputOffset : EvmWord) :
    decodeCallFamilyStack? .call
      [gas, to, value, inputOffset, inputSize, outputOffset] = none := rfl

theorem decodeCallFamilyStack?_staticcall_none_of_empty :
    decodeCallFamilyStack? .staticcall [] = none := rfl

theorem decodeCallFamilyStack?_staticcall_none_of_one
    (gas : EvmWord) :
    decodeCallFamilyStack? .staticcall [gas] = none := rfl

theorem decodeCallFamilyStack?_staticcall_none_of_two
    (gas to : EvmWord) :
    decodeCallFamilyStack? .staticcall [gas, to] = none := rfl

theorem decodeCallFamilyStack?_staticcall_none_of_three
    (gas to inputOffset : EvmWord) :
    decodeCallFamilyStack? .staticcall [gas, to, inputOffset] = none := rfl

theorem decodeCallFamilyStack?_staticcall_none_of_four
    (gas to inputOffset inputSize : EvmWord) :
    decodeCallFamilyStack? .staticcall
      [gas, to, inputOffset, inputSize] = none := rfl

theorem decodeCallFamilyStack?_staticcall_none_of_five
    (gas to inputOffset inputSize outputOffset : EvmWord) :
    decodeCallFamilyStack? .staticcall
      [gas, to, inputOffset, inputSize, outputOffset] = none := rfl

theorem decodeCallFamilyStack?_delegatecall_none_of_empty :
    decodeCallFamilyStack? .delegatecall [] = none := rfl

theorem decodeCallFamilyStack?_delegatecall_none_of_one
    (gas : EvmWord) :
    decodeCallFamilyStack? .delegatecall [gas] = none := rfl

theorem decodeCallFamilyStack?_delegatecall_none_of_two
    (gas to : EvmWord) :
    decodeCallFamilyStack? .delegatecall [gas, to] = none := rfl

theorem decodeCallFamilyStack?_delegatecall_none_of_three
    (gas to inputOffset : EvmWord) :
    decodeCallFamilyStack? .delegatecall [gas, to, inputOffset] = none := rfl

theorem decodeCallFamilyStack?_delegatecall_none_of_four
    (gas to inputOffset inputSize : EvmWord) :
    decodeCallFamilyStack? .delegatecall
      [gas, to, inputOffset, inputSize] = none := rfl

theorem decodeCallFamilyStack?_delegatecall_none_of_five
    (gas to inputOffset inputSize outputOffset : EvmWord) :
    decodeCallFamilyStack? .delegatecall
      [gas, to, inputOffset, inputSize, outputOffset] = none := rfl

theorem decodedKind_call
    (gas to value inputOffset inputSize outputOffset outputSize : EvmWord) :
    decodedKind
      (.call (mkCall gas to value inputOffset inputSize outputOffset outputSize)) =
        .call := rfl

theorem decodedKind_staticcall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord) :
    decodedKind
      (.staticcall
        (mkStaticCall gas to inputOffset inputSize outputOffset outputSize)) =
        .staticcall := rfl

theorem decodedKind_delegatecall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord) :
    decodedKind
      (.delegatecall
        (mkDelegateCall gas to inputOffset inputSize outputOffset outputSize)) =
        .delegatecall := rfl

theorem decodedInput_call
    (gas to value inputOffset inputSize outputOffset outputSize : EvmWord) :
    decodedInput
      (.call (mkCall gas to value inputOffset inputSize outputOffset outputSize)) =
        { offset := inputOffset, size := inputSize } := rfl

theorem decodedInput_staticcall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord) :
    decodedInput
      (.staticcall
        (mkStaticCall gas to inputOffset inputSize outputOffset outputSize)) =
        { offset := inputOffset, size := inputSize } := rfl

theorem decodedInput_delegatecall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord) :
    decodedInput
      (.delegatecall
        (mkDelegateCall gas to inputOffset inputSize outputOffset outputSize)) =
        { offset := inputOffset, size := inputSize } := rfl

theorem decodedOutput_call
    (gas to value inputOffset inputSize outputOffset outputSize : EvmWord) :
    decodedOutput
      (.call (mkCall gas to value inputOffset inputSize outputOffset outputSize)) =
        { offset := outputOffset, size := outputSize } := rfl

theorem decodedOutput_staticcall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord) :
    decodedOutput
      (.staticcall
        (mkStaticCall gas to inputOffset inputSize outputOffset outputSize)) =
        { offset := outputOffset, size := outputSize } := rfl

theorem decodedOutput_delegatecall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord) :
    decodedOutput
      (.delegatecall
        (mkDelegateCall gas to inputOffset inputSize outputOffset outputSize)) =
        { offset := outputOffset, size := outputSize } := rfl

theorem decodedArgumentCount_call
    (gas to value inputOffset inputSize outputOffset outputSize : EvmWord) :
    decodedArgumentCount
      (.call (mkCall gas to value inputOffset inputSize outputOffset outputSize)) =
        7 := rfl

theorem decodedArgumentCount_staticcall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord) :
    decodedArgumentCount
      (.staticcall
        (mkStaticCall gas to inputOffset inputSize outputOffset outputSize)) =
        6 := rfl

theorem decodedArgumentCount_delegatecall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord) :
    decodedArgumentCount
      (.delegatecall
        (mkDelegateCall gas to inputOffset inputSize outputOffset outputSize)) =
        6 := rfl

end CallArgsStackDecode

end EvmAsm.Evm64
