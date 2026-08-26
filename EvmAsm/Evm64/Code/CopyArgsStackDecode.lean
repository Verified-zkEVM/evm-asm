/-
  EvmAsm.Evm64.Code.CopyArgsStackDecode

  Pure top-of-stack decoder for CODECOPY executable-spec bridges
  (GH #107 / GH #118).
-/

module

public import EvmAsm.Evm64.Code.CopyArgs

@[expose] public section

namespace EvmAsm.Evm64

namespace CodeCopyArgsStackDecode

/--
Decode CODECOPY stack arguments from the top-of-stack list order:
`destOffset, codeOffset, size`.

Distinctive token: CodeCopyArgsStackDecode.decodeCodeCopyStack? #107 #118.
-/
def decodeCodeCopyStack? : List EvmWord → Option CodeCopyArgs.Args
  | destOffset :: codeOffset :: size :: _ =>
      some (CodeCopyArgs.copyArgs destOffset codeOffset size)
  | _ => none

theorem decodeCodeCopyStack?_cons
    (destOffset codeOffset size : EvmWord) (rest : List EvmWord) :
    decodeCodeCopyStack? (destOffset :: codeOffset :: size :: rest) =
      some (CodeCopyArgs.copyArgs destOffset codeOffset size) := rfl

theorem decodeCodeCopyStack?_eq_some_iff
    {stack : List EvmWord} {args : CodeCopyArgs.Args} :
    decodeCodeCopyStack? stack = some args ↔
      ∃ destOffset codeOffset size rest,
        stack = destOffset :: codeOffset :: size :: rest ∧
          args = CodeCopyArgs.copyArgs destOffset codeOffset size := by
  constructor
  · cases stack with
    | nil => simp [decodeCodeCopyStack?]
    | cons destOffset s1 =>
      cases s1 with
      | nil => simp [decodeCodeCopyStack?]
      | cons codeOffset s2 =>
        cases s2 with
        | nil => simp [decodeCodeCopyStack?]
        | cons size rest =>
          intro h
          injection h with h_args
          subst h_args
          exact ⟨destOffset, codeOffset, size, rest, rfl, rfl⟩
  · rintro ⟨destOffset, codeOffset, size, rest, rfl, rfl⟩
    rfl

theorem decodeCodeCopyStack?_eq_none_iff (stack : List EvmWord) :
    decodeCodeCopyStack? stack = none ↔ stack.length < 3 := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
    · simp
    · simp
    · simp
    · simp [decodeCodeCopyStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · simp at h_len
      omega

theorem decodeCodeCopyStack?_none_of_empty :
    decodeCodeCopyStack? [] = none := rfl

theorem decodeCodeCopyStack?_none_of_one
    (destOffset : EvmWord) :
    decodeCodeCopyStack? [destOffset] = none := rfl

theorem decodeCodeCopyStack?_none_of_two
    (destOffset codeOffset : EvmWord) :
    decodeCodeCopyStack? [destOffset, codeOffset] = none := rfl

theorem decodeCodeCopyStack?_destOffset
    (destOffset codeOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.destOffset)
      (decodeCodeCopyStack? (destOffset :: codeOffset :: size :: rest)) =
      some destOffset := rfl

theorem decodeCodeCopyStack?_codeOffset
    (destOffset codeOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.codeOffset)
      (decodeCodeCopyStack? (destOffset :: codeOffset :: size :: rest)) =
      some codeOffset := rfl

theorem decodeCodeCopyStack?_size
    (destOffset codeOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.size)
      (decodeCodeCopyStack? (destOffset :: codeOffset :: size :: rest)) =
      some size := rfl

end CodeCopyArgsStackDecode

end EvmAsm.Evm64
