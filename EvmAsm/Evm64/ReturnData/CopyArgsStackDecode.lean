/-
  EvmAsm.Evm64.ReturnData.CopyArgsStackDecode

  Pure top-of-stack decoder for RETURNDATACOPY executable-spec bridges
  (GH #107 / GH #114).
-/

module

public import EvmAsm.Evm64.ReturnData.CopyArgs

@[expose] public section

namespace EvmAsm.Evm64

namespace ReturnDataCopyArgsStackDecode

/--
Decode RETURNDATACOPY stack arguments from the top-of-stack list order:
`destOffset, dataOffset, size`.

Distinctive token:
ReturnDataCopyArgsStackDecode.decodeReturnDataCopyStack? #107 #114.
-/
def decodeReturnDataCopyStack? : List EvmWord → Option ReturnDataCopyArgs.Args
  | destOffset :: dataOffset :: size :: _ =>
      some (ReturnDataCopyArgs.copyArgs destOffset dataOffset size)
  | _ => none

theorem decodeReturnDataCopyStack?_cons
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    decodeReturnDataCopyStack? (destOffset :: dataOffset :: size :: rest) =
      some (ReturnDataCopyArgs.copyArgs destOffset dataOffset size) := rfl

theorem decodeReturnDataCopyStack?_eq_some_iff
    {stack : List EvmWord} {args : ReturnDataCopyArgs.Args} :
    decodeReturnDataCopyStack? stack = some args ↔
      ∃ destOffset dataOffset size rest,
        stack = destOffset :: dataOffset :: size :: rest ∧
          args = ReturnDataCopyArgs.copyArgs destOffset dataOffset size := by
  constructor
  · cases stack with
    | nil => simp [decodeReturnDataCopyStack?]
    | cons destOffset s1 =>
      cases s1 with
      | nil => simp [decodeReturnDataCopyStack?]
      | cons dataOffset s2 =>
        cases s2 with
        | nil => simp [decodeReturnDataCopyStack?]
        | cons size rest =>
          intro h
          injection h with h_args
          subst h_args
          exact ⟨destOffset, dataOffset, size, rest, rfl, rfl⟩
  · rintro ⟨destOffset, dataOffset, size, rest, rfl, rfl⟩
    rfl

theorem decodeReturnDataCopyStack?_eq_none_iff (stack : List EvmWord) :
    decodeReturnDataCopyStack? stack = none ↔ stack.length < 3 := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
    · simp
    · simp
    · simp
    · simp [decodeReturnDataCopyStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · simp at h_len
      omega

theorem decodeReturnDataCopyStack?_none_of_empty :
    decodeReturnDataCopyStack? [] = none := rfl

theorem decodeReturnDataCopyStack?_none_of_one
    (destOffset : EvmWord) :
    decodeReturnDataCopyStack? [destOffset] = none := rfl

theorem decodeReturnDataCopyStack?_none_of_two
    (destOffset dataOffset : EvmWord) :
    decodeReturnDataCopyStack? [destOffset, dataOffset] = none := rfl

theorem decodeReturnDataCopyStack?_destOffset
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.destOffset)
      (decodeReturnDataCopyStack? (destOffset :: dataOffset :: size :: rest)) =
      some destOffset := rfl

theorem decodeReturnDataCopyStack?_dataOffset
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.dataOffset)
      (decodeReturnDataCopyStack? (destOffset :: dataOffset :: size :: rest)) =
      some dataOffset := rfl

theorem decodeReturnDataCopyStack?_size
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.size)
      (decodeReturnDataCopyStack? (destOffset :: dataOffset :: size :: rest)) =
      some size := rfl

end ReturnDataCopyArgsStackDecode

end EvmAsm.Evm64
