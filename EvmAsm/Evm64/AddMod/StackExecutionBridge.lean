/-
  EvmAsm.Evm64.AddMod.StackExecutionBridge

  Pure stack-execution bridge for ADDMOD (GH #91).
-/

import EvmAsm.Evm64.AddMod.ArgsStackDecode

namespace EvmAsm.Evm64
namespace AddModStackExecutionBridge

/-- Caller-visible stack effects of ADDMOD at the executable-spec layer. -/
structure AddModVisibleEffects where
  stackWords : List EvmWord
  deriving Repr

structure AddModStackState where
  stack : List EvmWord
  deriving Repr

structure AddModStackResult where
  effects : AddModVisibleEffects
  stack : List EvmWord
  deriving Repr

def argumentCount : Nat := AddModArgs.stackArgumentCount

def resultCount : Nat := AddModArgs.resultCount

def stackRestAfterAddMod? : List EvmWord → Option (List EvmWord)
  | _a :: _b :: _N :: rest => some rest
  | _ => none

/-- Execute the ADDMOD stack transition using the pure argument decoder. -/
def runAddModStack? (state : AddModStackState) : Option AddModStackResult := do
  let args ← AddModArgsStackDecode.decodeAddModStack? state.stack
  let rest ← stackRestAfterAddMod? state.stack
  some
    { effects := { stackWords := [AddModArgs.addmodResultFromArgs args] }
      stack := rest }

theorem stackRestAfterAddMod?_cons
    (a b N : EvmWord) (rest : List EvmWord) :
    stackRestAfterAddMod? (a :: b :: N :: rest) = some rest := rfl

theorem runAddModStack?_cons
    (a b N : EvmWord) (rest : List EvmWord) :
    runAddModStack? { stack := a :: b :: N :: rest } =
      some
        { effects :=
            { stackWords := [AddModArgs.addmodResultFromArgs
                (AddModArgs.addmodArgs a b N)] }
          stack := rest } := rfl

theorem runAddModStack?_semantic_cons
    (a b N : EvmWord) (rest : List EvmWord) :
    runAddModStack? { stack := a :: b :: N :: rest } =
      some
        { effects := { stackWords := [EvmWord.addmod a b N] }
          stack := rest } := rfl

theorem runAddModStack?_underflow_nil :
    runAddModStack? { stack := [] } = none := rfl

theorem runAddModStack?_underflow_one (a : EvmWord) :
    runAddModStack? { stack := [a] } = none := rfl

theorem runAddModStack?_underflow_two (a b : EvmWord) :
    runAddModStack? { stack := [a, b] } = none := rfl

theorem stackRestAfterAddMod?_none_of_empty :
    stackRestAfterAddMod? [] = none := rfl

theorem stackRestAfterAddMod?_none_of_one (a : EvmWord) :
    stackRestAfterAddMod? [a] = none := rfl

theorem stackRestAfterAddMod?_none_of_two (a b : EvmWord) :
    stackRestAfterAddMod? [a, b] = none := rfl

theorem stackRestAfterAddMod?_eq_none_iff
    {stack : List EvmWord} :
    stackRestAfterAddMod? stack = none ↔
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
                simp [stackRestAfterAddMod?]
  · rintro (rfl | ⟨a, rfl | ⟨b, rfl⟩⟩) <;> rfl

theorem runAddModStack?_eq_none_iff
    {state : AddModStackState} :
    runAddModStack? state = none ↔
      state.stack = [] ∨ ∃ a, state.stack = [a] ∨ ∃ b, state.stack = [a, b] := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
            stackRestAfterAddMod?, Option.bind]
      | cons a s1 =>
          cases s1 with
          | nil =>
              simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
                stackRestAfterAddMod?, Option.bind]
          | cons b s2 =>
              cases s2 with
              | nil =>
                  simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
                    stackRestAfterAddMod?, Option.bind]
              | cons N rest =>
                  simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
                    stackRestAfterAddMod?, Option.bind]

theorem runAddModStack?_eq_some_iff
    {state : AddModStackState} {out : AddModStackResult} :
    runAddModStack? state = some out ↔
      ∃ a b N rest,
        state.stack = a :: b :: N :: rest ∧
          out =
            { effects :=
                { stackWords := [AddModArgs.addmodResultFromArgs
                    (AddModArgs.addmodArgs a b N)] }
              stack := rest } := by
  constructor
  · cases state with
    | mk stack =>
        cases stack with
        | nil =>
            simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
              stackRestAfterAddMod?, Option.bind]
        | cons a s1 =>
            cases s1 with
            | nil =>
                simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
                  stackRestAfterAddMod?, Option.bind]
            | cons b s2 =>
                cases s2 with
                | nil =>
                    simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
                      stackRestAfterAddMod?, Option.bind]
                | cons N rest =>
                    intro h_run
                    simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?,
                      stackRestAfterAddMod?, Option.bind] at h_run
                    cases h_run
                    exact ⟨a, b, N, rest, rfl, rfl⟩
  · rintro ⟨a, b, N, rest, h_stack, h_out⟩
    cases state with
    | mk stack =>
        simp at h_stack
        subst h_stack
        subst h_out
        exact runAddModStack?_cons a b N rest

theorem runAddModStack?_stack_length
    {state : AddModStackState} {out : AddModStackResult}
    (h_run : runAddModStack? state = some out) :
    out.stack.length + out.effects.stackWords.length + argumentCount =
      state.stack.length + resultCount := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runAddModStack?, AddModArgsStackDecode.decodeAddModStack?] at h_run
      | cons a s1 =>
          cases s1 with
          | nil => simp [runAddModStack?, stackRestAfterAddMod?] at h_run
          | cons b s2 =>
              cases s2 with
              | nil => simp [runAddModStack?, stackRestAfterAddMod?] at h_run
              | cons N rest =>
                  simp [runAddModStack?, stackRestAfterAddMod?] at h_run
                  cases h_run
                  simp [argumentCount, resultCount, AddModArgs.stackArgumentCount,
                    AddModArgs.resultCount]

theorem runAddModStack?_head?
    (a b N : EvmWord) (rest : List EvmWord) :
    (runAddModStack? { stack := a :: b :: N :: rest }).map
      (fun out => out.effects.stackWords.head?) =
      some (some (AddModArgs.addmodResultFromArgs
        (AddModArgs.addmodArgs a b N))) := rfl

theorem runAddModStack?_semantic_stack_after
    (a b N : EvmWord) (rest : List EvmWord) :
    (runAddModStack? { stack := a :: b :: N :: rest }).map
      (fun out => out.effects.stackWords ++ out.stack) =
      some (EvmWord.addmod a b N :: rest) := rfl

theorem runAddModStack?_zero_modulus
    (a b : EvmWord) (rest : List EvmWord) :
    runAddModStack? { stack := a :: b :: 0 :: rest } =
      some { effects := { stackWords := [0] }, stack := rest } := by
  rw [runAddModStack?_cons]
  rw [AddModArgs.addmodResultFromArgs_zero_modulus]

end AddModStackExecutionBridge
end EvmAsm.Evm64
