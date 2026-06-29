/-
  EvmAsm.Evm64.AddMod.ArgsStackDecode

  Pure top-of-stack decoder for ADDMOD executable-spec bridges (GH #91).
-/

import EvmAsm.Evm64.AddMod.Args

namespace EvmAsm.Evm64
namespace AddModArgsStackDecode

/--
Decode ADDMOD stack arguments from the top-of-stack list order: first addend,
second addend, modulus.
-/
def decodeAddModStack? : List EvmWord → Option AddModArgs.Args
  | a :: b :: N :: _ => some (AddModArgs.addmodArgs a b N)
  | _ => none

theorem decodeAddModStack?_cons
    (a b N : EvmWord) (rest : List EvmWord) :
    decodeAddModStack? (a :: b :: N :: rest) =
      some (AddModArgs.addmodArgs a b N) := rfl

theorem decodeAddModStack?_eq_some_iff
    {stack : List EvmWord} {args : AddModArgs.Args} :
    decodeAddModStack? stack = some args ↔
      ∃ a b N rest,
        stack = a :: b :: N :: rest ∧
          args = AddModArgs.addmodArgs a b N := by
  constructor
  · cases stack with
    | nil => simp [decodeAddModStack?]
    | cons a s1 =>
        cases s1 with
        | nil => simp [decodeAddModStack?]
        | cons b s2 =>
            cases s2 with
            | nil => simp [decodeAddModStack?]
            | cons N rest =>
                intro h
                injection h with h_args
                subst h_args
                exact ⟨a, b, N, rest, rfl, rfl⟩
  · rintro ⟨a, b, N, rest, rfl, rfl⟩
    rfl

theorem decodeAddModStack?_eq_none_iff
    {stack : List EvmWord} :
    decodeAddModStack? stack = none ↔
      stack = [] ∨ ∃ a, stack = [a] ∨ ∃ b, stack = [a, b] := by
  constructor
  · cases stack with
    | nil =>
        intro _h
        exact Or.inl rfl
    | cons a s1 =>
        cases s1 with
        | nil =>
            intro _h
            exact Or.inr ⟨a, Or.inl rfl⟩
        | cons b s2 =>
            cases s2 with
            | nil =>
                intro _h
                exact Or.inr ⟨a, Or.inr ⟨b, rfl⟩⟩
            | cons N rest =>
                simp [decodeAddModStack?]
  · rintro (rfl | ⟨a, rfl | ⟨b, rfl⟩⟩) <;> rfl

theorem decodeAddModStack?_none_of_empty :
    decodeAddModStack? [] = none := rfl

theorem decodeAddModStack?_none_of_one (a : EvmWord) :
    decodeAddModStack? [a] = none := rfl

theorem decodeAddModStack?_none_of_two (a b : EvmWord) :
    decodeAddModStack? [a, b] = none := rfl

theorem decodeAddModStack?_a
    (a b N : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.a)
      (decodeAddModStack? (a :: b :: N :: rest)) =
      some a := rfl

theorem decodeAddModStack?_b
    (a b N : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.b)
      (decodeAddModStack? (a :: b :: N :: rest)) =
      some b := rfl

theorem decodeAddModStack?_N
    (a b N : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.N)
      (decodeAddModStack? (a :: b :: N :: rest)) =
      some N := rfl

end AddModArgsStackDecode
end EvmAsm.Evm64
