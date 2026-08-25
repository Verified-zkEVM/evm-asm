/-
  EvmAsm.Evm64.SDiv.StackExecutionBridge

  Pure stack-execution bridge for SDIV (GH #90).
-/

module

public import EvmAsm.Evm64.SDiv.ArgsStackDecode

@[expose] public section

namespace EvmAsm.Evm64
namespace SDivStackExecutionBridge

/-- Caller-visible stack effects of SDIV at the executable-spec layer. -/
structure SDivVisibleEffects where
  stackWords : List EvmWord
  deriving Repr

structure SDivStackState where
  stack : List EvmWord
  deriving Repr

structure SDivStackResult where
  effects : SDivVisibleEffects
  stack : List EvmWord
  deriving Repr

def argumentCount : Nat := SDivArgs.stackArgumentCount

def resultCount : Nat := SDivArgs.resultCount

def stackRestAfterSDiv? : List EvmWord → Option (List EvmWord)
  | _dividend :: _divisor :: rest => some rest
  | _ => none

/-- Execute the SDIV stack transition using the pure argument decoder. -/
def runSDivStack? (state : SDivStackState) : Option SDivStackResult := do
  let args ← SDivArgsStackDecode.decodeSDivStack? state.stack
  let rest ← stackRestAfterSDiv? state.stack
  some
    { effects := { stackWords := [SDivArgs.sdivResultFromArgs args] }
      stack := rest }

theorem stackRestAfterSDiv?_cons
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    stackRestAfterSDiv? (dividend :: divisor :: rest) = some rest := rfl

theorem runSDivStack?_cons
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    runSDivStack? { stack := dividend :: divisor :: rest } =
      some
        { effects :=
            { stackWords := [SDivArgs.sdivResultFromArgs
                (SDivArgs.sdivArgs dividend divisor)] }
          stack := rest } := rfl

theorem runSDivStack?_underflow_nil :
    runSDivStack? { stack := [] } = none := rfl

theorem runSDivStack?_underflow_one (dividend : EvmWord) :
    runSDivStack? { stack := [dividend] } = none := rfl

theorem stackRestAfterSDiv?_none_of_empty :
    stackRestAfterSDiv? [] = none := rfl

theorem stackRestAfterSDiv?_none_of_one
    (dividend : EvmWord) :
    stackRestAfterSDiv? [dividend] = none := rfl

theorem stackRestAfterSDiv?_eq_none_iff
    {stack : List EvmWord} :
    stackRestAfterSDiv? stack = none ↔
      stack = [] ∨ ∃ dividend, stack = [dividend] := by
  constructor
  · cases stack with
    | nil =>
        intro _h
        exact Or.inl rfl
    | cons dividend tail =>
        cases tail with
        | nil =>
            intro _h
            exact Or.inr ⟨dividend, rfl⟩
        | cons divisor rest =>
            simp [stackRestAfterSDiv?]
  · rintro (rfl | ⟨dividend, rfl⟩) <;> rfl

theorem runSDivStack?_eq_none_iff
    {state : SDivStackState} :
    runSDivStack? state = none ↔
      state.stack = [] ∨ ∃ dividend, state.stack = [dividend] := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runSDivStack?, SDivArgsStackDecode.decodeSDivStack?,
            stackRestAfterSDiv?, Option.bind]
      | cons dividend tail =>
          cases tail with
          | nil =>
              simp [runSDivStack?, SDivArgsStackDecode.decodeSDivStack?,
                stackRestAfterSDiv?, Option.bind]
          | cons divisor rest =>
              simp [runSDivStack?, SDivArgsStackDecode.decodeSDivStack?,
                stackRestAfterSDiv?, Option.bind]

theorem runSDivStack?_eq_some_iff
    {state : SDivStackState} {out : SDivStackResult} :
    runSDivStack? state = some out ↔
      ∃ dividend divisor rest,
        state.stack = dividend :: divisor :: rest ∧
          out =
            { effects :=
                { stackWords := [SDivArgs.sdivResultFromArgs
                    (SDivArgs.sdivArgs dividend divisor)] }
              stack := rest } := by
  constructor
  · cases state with
    | mk stack =>
        cases stack with
        | nil =>
            simp [runSDivStack?, SDivArgsStackDecode.decodeSDivStack?,
              stackRestAfterSDiv?, Option.bind]
        | cons dividend tail =>
            cases tail with
            | nil =>
                simp [runSDivStack?, SDivArgsStackDecode.decodeSDivStack?,
                  stackRestAfterSDiv?, Option.bind]
            | cons divisor rest =>
                intro h_run
                simp [runSDivStack?, SDivArgsStackDecode.decodeSDivStack?,
                  stackRestAfterSDiv?, Option.bind] at h_run
                cases h_run
                exact ⟨dividend, divisor, rest, rfl, rfl⟩
  · rintro ⟨dividend, divisor, rest, h_stack, h_out⟩
    cases state with
    | mk stack =>
        simp at h_stack
        subst h_stack
        subst h_out
        exact runSDivStack?_cons dividend divisor rest

theorem runSDivStack?_stack_length
    {state : SDivStackState} {out : SDivStackResult}
    (h_run : runSDivStack? state = some out) :
    out.stack.length + out.effects.stackWords.length + argumentCount =
      state.stack.length + resultCount := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runSDivStack?, SDivArgsStackDecode.decodeSDivStack?] at h_run
      | cons dividend tail =>
          cases tail with
          | nil => simp [runSDivStack?, stackRestAfterSDiv?] at h_run
          | cons divisor rest =>
              simp [runSDivStack?, stackRestAfterSDiv?] at h_run
              cases h_run
              simp [argumentCount, resultCount, SDivArgs.stackArgumentCount,
                SDivArgs.resultCount]

theorem runSDivStack?_head?
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    (runSDivStack? { stack := dividend :: divisor :: rest }).map
      (fun out => out.effects.stackWords.head?) =
      some (some (SDivArgs.sdivResultFromArgs
        (SDivArgs.sdivArgs dividend divisor))) := rfl

theorem runSDivStack?_zero_divisor
    (dividend : EvmWord) (rest : List EvmWord) :
    runSDivStack? { stack := dividend :: 0 :: rest } =
      some { effects := { stackWords := [0] }, stack := rest } := by
  rw [runSDivStack?_cons]
  rw [SDivArgs.sdivResultFromArgs_zero_divisor]

theorem runSDivStack?_intMin_neg_one
    (rest : List EvmWord) :
    runSDivStack? { stack := BitVec.intMin 256 :: (-1 : EvmWord) :: rest } =
      some { effects := { stackWords := [BitVec.intMin 256] }, stack := rest } := by
  rw [runSDivStack?_cons]
  rw [SDivArgs.sdivResultFromArgs_intMin_neg_one]

theorem runSDivStack?_neg_one_two
    (rest : List EvmWord) :
    runSDivStack? { stack := (-1 : EvmWord) :: 2 :: rest } =
      some { effects := { stackWords := [0] }, stack := rest } := by
  rw [runSDivStack?_cons]
  rw [SDivArgs.sdivResultFromArgs_neg_one_two]

theorem runSDivStack?_pos_neg_trunc
    (rest : List EvmWord) :
    runSDivStack? { stack := (7 : EvmWord) :: (-2 : EvmWord) :: rest } =
      some { effects := { stackWords := [(-3 : EvmWord)] }, stack := rest } := by
  rw [runSDivStack?_cons]
  rw [SDivArgs.sdivResultFromArgs_pos_neg_trunc]

theorem runSDivStack?_neg_pos_trunc
    (rest : List EvmWord) :
    runSDivStack? { stack := (-7 : EvmWord) :: 2 :: rest } =
      some { effects := { stackWords := [(-3 : EvmWord)] }, stack := rest } := by
  rw [runSDivStack?_cons]
  rw [SDivArgs.sdivResultFromArgs_neg_pos_trunc]

end SDivStackExecutionBridge
end EvmAsm.Evm64
