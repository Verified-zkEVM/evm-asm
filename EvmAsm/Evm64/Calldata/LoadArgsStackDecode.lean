/-
  EvmAsm.Evm64.Calldata.LoadArgsStackDecode

  Pure top-of-stack decoder for CALLDATALOAD executable-spec bridges
  (GH #104 / GH #107).
-/

module

public import EvmAsm.Evm64.Calldata.LoadArgs

@[expose] public section

namespace EvmAsm.Evm64

namespace CallDataLoadArgsStackDecode

/--
Decode CALLDATALOAD stack arguments from the top-of-stack list order:
`offset`.

Distinctive token:
CallDataLoadArgsStackDecode.decodeCallDataLoadStack? #104 #107.
-/
def decodeCallDataLoadStack? : List EvmWord → Option CallDataLoadArgs.Args
  | offset :: _ => some (CallDataLoadArgs.loadArgs offset)
  | _ => none

theorem decodeCallDataLoadStack?_cons
    (offset : EvmWord) (rest : List EvmWord) :
    decodeCallDataLoadStack? (offset :: rest) =
      some (CallDataLoadArgs.loadArgs offset) := rfl

theorem decodeCallDataLoadStack?_eq_some_iff
    {stack : List EvmWord} {args : CallDataLoadArgs.Args} :
    decodeCallDataLoadStack? stack = some args ↔
      ∃ offset rest,
        stack = offset :: rest ∧ args = CallDataLoadArgs.loadArgs offset := by
  constructor
  · cases stack with
    | nil => simp [decodeCallDataLoadStack?]
    | cons offset rest =>
      intro h
      injection h with h_args
      subst h_args
      exact ⟨offset, rest, rfl, rfl⟩
  · rintro ⟨offset, rest, rfl, rfl⟩
    rfl

theorem decodeCallDataLoadStack?_offset_of_some
    {stack : List EvmWord} {args : CallDataLoadArgs.Args}
    (h : decodeCallDataLoadStack? stack = some args) :
    ∃ rest, stack = args.offset :: rest := by
  obtain ⟨offset, rest, h_stack, h_args⟩ :=
    decodeCallDataLoadStack?_eq_some_iff.mp h
  subst h_args
  exact ⟨rest, h_stack⟩

theorem decodeCallDataLoadStack?_offsetNat_of_some
    {stack : List EvmWord} {args : CallDataLoadArgs.Args}
    (h : decodeCallDataLoadStack? stack = some args) :
    ∃ offset rest,
      stack = offset :: rest ∧ CallDataLoadArgs.offsetNat args = offset.toNat := by
  obtain ⟨offset, rest, h_stack, h_args⟩ :=
    decodeCallDataLoadStack?_eq_some_iff.mp h
  subst h_args
  exact ⟨offset, rest, h_stack, rfl⟩

/--
CALLDATALOAD stack decoding fails exactly when the stack is empty.

Distinctive token:
CallDataLoadArgsStackDecode.decodeCallDataLoadStack?_eq_none_iff #104 #107.
-/
theorem decodeCallDataLoadStack?_eq_none_iff
    (stack : List EvmWord) :
    decodeCallDataLoadStack? stack = none ↔ stack = [] := by
  cases stack with
  | nil => simp [decodeCallDataLoadStack?]
  | cons offset rest => simp [decodeCallDataLoadStack?]

theorem decodeCallDataLoadStack?_none_of_empty :
    decodeCallDataLoadStack? [] = none := rfl

theorem decodeCallDataLoadStack?_offset
    (offset : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.offset)
      (decodeCallDataLoadStack? (offset :: rest)) =
      some offset := rfl

end CallDataLoadArgsStackDecode

end EvmAsm.Evm64
