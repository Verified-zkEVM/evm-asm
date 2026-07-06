/-
  EvmAsm.Evm64.Exp.StackExecutionBridge

  Pure stack-execution bridge for EXP (GH #92).
-/

import EvmAsm.Evm64.Exp.ArgsStackDecode

namespace EvmAsm.Evm64

namespace ExpStackExecutionBridge

/-- Caller-visible effects of EXP at the executable-spec layer. -/
structure ExpVisibleEffects where
  stackWords : List EvmWord
  dynamicGas : Nat
  totalGas : Nat
  deriving Repr

structure ExpStackState where
  stack : List EvmWord
  deriving Repr

structure ExpStackResult where
  effects : ExpVisibleEffects
  stack : List EvmWord
  deriving Repr

def argumentCount : Nat := ExpArgs.stackArgumentCount

def resultCount : Nat := ExpArgs.resultCount

def stackRestAfterExp? : List EvmWord → Option (List EvmWord)
  | _base :: _exponent :: rest => some rest
  | _ => none

/--
Execute the EXP stack transition using the pure EXP argument decoder and
the existing word-level EXP result/gas bridge.

Distinctive token: ExpStackExecutionBridge.runExpStack? #92.
-/
def runExpStack? (state : ExpStackState) : Option ExpStackResult := do
  let args ← ExpArgsStackDecode.decodeExpStack? state.stack
  let rest ← stackRestAfterExp? state.stack
  some
    { effects :=
        { stackWords := [ExpArgs.expResultFromArgs args]
          dynamicGas := ExpArgs.expDynamicCostFromArgs args
          totalGas := ExpArgs.expTotalGasFromArgs args }
      stack := rest }

theorem stackRestAfterExp?_cons
    (base exponent : EvmWord) (rest : List EvmWord) :
    stackRestAfterExp? (base :: exponent :: rest) = some rest := rfl

theorem runExpStack?_cons
    (base exponent : EvmWord) (rest : List EvmWord) :
    runExpStack? { stack := base :: exponent :: rest } =
      some
        { effects :=
            { stackWords := [ExpArgs.expResultFromArgs
                (ExpArgs.expArgs base exponent)]
              dynamicGas := ExpArgs.expDynamicCostFromArgs
                (ExpArgs.expArgs base exponent)
              totalGas := ExpArgs.expTotalGasFromArgs
                (ExpArgs.expArgs base exponent) }
          stack := rest } := rfl

theorem runExpStack?_underflow_nil :
    runExpStack? { stack := [] } = none := rfl

theorem runExpStack?_underflow_one (base : EvmWord) :
    runExpStack? { stack := [base] } = none := rfl

theorem stackRestAfterExp?_none_of_empty :
    stackRestAfterExp? [] = none := rfl

theorem stackRestAfterExp?_none_of_one
    (base : EvmWord) :
    stackRestAfterExp? [base] = none := rfl

theorem stackRestAfterExp?_eq_none_iff
    {stack : List EvmWord} :
    stackRestAfterExp? stack = none ↔
      stack = [] ∨ ∃ base, stack = [base] := by
  constructor
  · cases stack with
    | nil =>
        intro _h
        exact Or.inl rfl
    | cons base tail =>
        cases tail with
        | nil =>
            intro _h
            exact Or.inr ⟨base, rfl⟩
        | cons exponent rest =>
            simp [stackRestAfterExp?]
  · rintro (rfl | ⟨base, rfl⟩) <;> rfl

theorem runExpStack?_eq_none_iff
    {state : ExpStackState} :
    runExpStack? state = none ↔
      state.stack = [] ∨ ∃ base, state.stack = [base] := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?,
            stackRestAfterExp?, Option.bind]
      | cons base tail =>
          cases tail with
          | nil =>
              simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?,
                stackRestAfterExp?, Option.bind]
          | cons exponent rest =>
              simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?,
                stackRestAfterExp?, Option.bind]

/--
EXP stack execution succeeds exactly on a stack with at least two words, and
the output is the decoded EXP result/effects plus the remaining stack tail.

Distinctive token: ExpStackExecutionBridge.runExpStack?_eq_some_iff #92.
-/
theorem runExpStack?_eq_some_iff
    {state : ExpStackState} {out : ExpStackResult} :
    runExpStack? state = some out ↔
      ∃ base exponent rest,
        state.stack = base :: exponent :: rest ∧
          out =
            { effects :=
                { stackWords := [ExpArgs.expResultFromArgs
                    (ExpArgs.expArgs base exponent)]
                  dynamicGas := ExpArgs.expDynamicCostFromArgs
                    (ExpArgs.expArgs base exponent)
                  totalGas := ExpArgs.expTotalGasFromArgs
                    (ExpArgs.expArgs base exponent) }
              stack := rest } := by
  constructor
  · cases state with
    | mk stack =>
        cases stack with
        | nil =>
            simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?,
              stackRestAfterExp?, Option.bind]
        | cons base tail =>
            cases tail with
            | nil =>
                simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?,
                  stackRestAfterExp?, Option.bind]
            | cons exponent rest =>
                intro h_run
                simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?,
                  stackRestAfterExp?, Option.bind] at h_run
                cases h_run
                exact ⟨base, exponent, rest, rfl, rfl⟩
  · rintro ⟨base, exponent, rest, h_stack, h_out⟩
    cases state with
    | mk stack =>
        simp at h_stack
        subst h_stack
        subst h_out
        exact runExpStack?_cons base exponent rest

theorem runExpStack?_effects_stackWords_length
    {state : ExpStackState} {out : ExpStackResult}
    (h_run : runExpStack? state = some out) :
    out.effects.stackWords.length = resultCount := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?] at h_run
      | cons base tail =>
          cases tail with
          | nil => simp [runExpStack?, stackRestAfterExp?] at h_run
          | cons exponent rest =>
              simp [runExpStack?, stackRestAfterExp?] at h_run
              cases h_run
              simp [resultCount, ExpArgs.resultCount]

theorem runExpStack?_effects_stackWords_ne_nil
    {state : ExpStackState} {out : ExpStackResult}
    (h_run : runExpStack? state = some out) :
    out.effects.stackWords ≠ [] := by
  have h_len := runExpStack?_effects_stackWords_length h_run
  intro h_nil
  rw [h_nil] at h_len
  simp [resultCount, ExpArgs.resultCount] at h_len

theorem runExpStack?_stack_length
    {state : ExpStackState} {out : ExpStackResult}
    (h_run : runExpStack? state = some out) :
    out.stack.length + out.effects.stackWords.length + argumentCount =
      state.stack.length + resultCount := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?] at h_run
      | cons base tail =>
          cases tail with
          | nil => simp [runExpStack?, stackRestAfterExp?] at h_run
          | cons exponent rest =>
              simp [runExpStack?, stackRestAfterExp?] at h_run
              cases h_run
              simp [argumentCount, resultCount, ExpArgs.stackArgumentCount,
                ExpArgs.resultCount]

theorem runExpStack?_head?
    (base exponent : EvmWord) (rest : List EvmWord) :
    (runExpStack? { stack := base :: exponent :: rest }).map
      (fun out => out.effects.stackWords.head?) =
      some (some (ExpArgs.expResultFromArgs
        (ExpArgs.expArgs base exponent))) := rfl

theorem runExpStack?_head?_of_some
    {base exponent : EvmWord} {rest : List EvmWord} {out : ExpStackResult}
    (h_run : runExpStack? { stack := base :: exponent :: rest } = some out) :
    out.effects.stackWords.head? =
      some (ExpArgs.expResultFromArgs (ExpArgs.expArgs base exponent)) := by
  rw [runExpStack?_cons] at h_run
  injection h_run with h_out
  subst h_out
  rfl

theorem runExpStack?_stackWords_of_some
    {base exponent : EvmWord} {rest : List EvmWord} {out : ExpStackResult}
    (h_run : runExpStack? { stack := base :: exponent :: rest } = some out) :
    out.effects.stackWords =
      [ExpArgs.expResultFromArgs (ExpArgs.expArgs base exponent)] := by
  rw [runExpStack?_cons] at h_run
  injection h_run with h_out
  subst h_out
  rfl

theorem runExpStack?_tail_of_some
    {base exponent : EvmWord} {rest : List EvmWord} {out : ExpStackResult}
    (h_run : runExpStack? { stack := base :: exponent :: rest } = some out) :
    out.stack = rest := by
  rw [runExpStack?_cons] at h_run
  injection h_run with h_out
  subst h_out
  rfl

theorem runExpStack?_stackAfterExp
    (base exponent : EvmWord) (rest : List EvmWord) :
    (runExpStack? { stack := base :: exponent :: rest }).map
      (fun out => out.effects.stackWords ++ out.stack) =
      some (ExpArgs.stackAfterExp (ExpArgs.expArgs base exponent) rest) := rfl

/-- Semantic stack result for EXP: the executable stack bridge replaces the
    two operands with `EvmWord.exp base exponent`. -/
theorem runExpStack?_semantic_stack_after
    (base exponent : EvmWord) (rest : List EvmWord) :
    (runExpStack? { stack := base :: exponent :: rest }).map
      (fun out => out.effects.stackWords ++ out.stack) =
      some (EvmWord.exp base exponent :: rest) := by
  rw [runExpStack?_stackAfterExp]
  rfl

/-- Semantic success form for EXP on a stack with two operands. -/
theorem runExpStack?_semantic_cons
    (base exponent : EvmWord) (rest : List EvmWord) :
    runExpStack? { stack := base :: exponent :: rest } =
      some
        { effects :=
            { stackWords := [EvmWord.exp base exponent]
              dynamicGas := ExpArgs.expDynamicCostFromArgs
                (ExpArgs.expArgs base exponent)
              totalGas := ExpArgs.expTotalGasFromArgs
                (ExpArgs.expArgs base exponent) }
          stack := rest } := by
  rw [runExpStack?_cons]
  rfl

theorem runExpStack?_gas
    (base exponent : EvmWord) (rest : List EvmWord) :
    (runExpStack? { stack := base :: exponent :: rest }).map
      (fun out => (out.effects.dynamicGas, out.effects.totalGas)) =
      some
        ( ExpArgs.expDynamicCostFromArgs (ExpArgs.expArgs base exponent)
        , ExpArgs.expTotalGasFromArgs (ExpArgs.expArgs base exponent)) := rfl

theorem runExpStack?_dynamicGas_of_some
    {base exponent : EvmWord} {rest : List EvmWord} {out : ExpStackResult}
    (h_run : runExpStack? { stack := base :: exponent :: rest } = some out) :
    out.effects.dynamicGas =
      ExpArgs.expDynamicCostFromArgs (ExpArgs.expArgs base exponent) := by
  rw [runExpStack?_cons] at h_run
  injection h_run with h_out
  subst h_out
  rfl

theorem runExpStack?_totalGas_of_some
    {base exponent : EvmWord} {rest : List EvmWord} {out : ExpStackResult}
    (h_run : runExpStack? { stack := base :: exponent :: rest } = some out) :
    out.effects.totalGas =
      ExpArgs.expTotalGasFromArgs (ExpArgs.expArgs base exponent) := by
  rw [runExpStack?_cons] at h_run
  injection h_run with h_out
  subst h_out
  rfl

theorem runExpStack?_totalGas_eq_dynamicGas_add_static
    {state : ExpStackState} {out : ExpStackResult}
    (h_run : runExpStack? state = some out) :
    out.effects.totalGas =
      out.effects.dynamicGas + EvmOpcode.staticGasCost .EXP := by
  rcases runExpStack?_eq_some_iff.mp h_run with
    ⟨base, exponent, rest, h_stack, h_out⟩
  subst h_out
  simp [ExpArgs.expTotalGasFromArgs, ExpArgs.expDynamicCostFromArgs,
    ExpGas.expTotalGasFromExponent, Nat.add_comm]

theorem runExpStack?_zero_exponent
    (base : EvmWord) (rest : List EvmWord) :
    runExpStack? { stack := base :: 0 :: rest } =
      some
        { effects := { stackWords := [1], dynamicGas := 0, totalGas := 10 }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_zero_right]
  rw [ExpArgs.expDynamicCostFromArgs_zero_exponent]
  rw [ExpArgs.expTotalGasFromArgs_zero_exponent]

theorem runExpStack?_zero_zero
    (rest : List EvmWord) :
    runExpStack? { stack := (0 : EvmWord) :: 0 :: rest } =
      some
        { effects := { stackWords := [1], dynamicGas := 0, totalGas := 10 }
          stack := rest } := by
  exact runExpStack?_zero_exponent 0 rest

theorem runExpStack?_max_zero_exponent
    (rest : List EvmWord) :
    runExpStack? { stack := (-1 : EvmWord) :: 0 :: rest } =
      some
        { effects := { stackWords := [1], dynamicGas := 0, totalGas := 10 }
          stack := rest } := by
  exact runExpStack?_zero_exponent (-1 : EvmWord) rest

theorem runExpStack?_one_exponent
    (base : EvmWord) (rest : List EvmWord) :
    runExpStack? { stack := base :: 1 :: rest } =
      some
        { effects := { stackWords := [base], dynamicGas := 50, totalGas := 60 }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_one_right]
  rw [ExpArgs.expDynamicCostFromArgs_one_exponent]
  rw [ExpArgs.expTotalGasFromArgs_one_exponent]

theorem runExpStack?_two_one
    (rest : List EvmWord) :
    runExpStack? { stack := (2 : EvmWord) :: 1 :: rest } =
      some
        { effects := { stackWords := [2], dynamicGas := 50, totalGas := 60 }
          stack := rest } := by
  exact runExpStack?_one_exponent 2 rest

theorem runExpStack?_zero_one
    (rest : List EvmWord) :
    runExpStack? { stack := (0 : EvmWord) :: 1 :: rest } =
      some
        { effects := { stackWords := [0], dynamicGas := 50, totalGas := 60 }
          stack := rest } := by
  exact runExpStack?_one_exponent 0 rest

theorem runExpStack?_max_one_exponent
    (rest : List EvmWord) :
    runExpStack? { stack := (-1 : EvmWord) :: 1 :: rest } =
      some
        { effects := { stackWords := [(-1 : EvmWord)], dynamicGas := 50, totalGas := 60 }
          stack := rest } := by
  exact runExpStack?_one_exponent (-1 : EvmWord) rest

theorem runExpStack?_one_left
    (exponent : EvmWord) (rest : List EvmWord) :
    runExpStack? { stack := (1 : EvmWord) :: exponent :: rest } =
      some
        { effects :=
            { stackWords := [1]
              dynamicGas := ExpArgs.expDynamicCostFromArgs
                (ExpArgs.expArgs 1 exponent)
              totalGas := ExpArgs.expTotalGasFromArgs
                (ExpArgs.expArgs 1 exponent) }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_one_left]

theorem runExpStack?_zero_left_of_ne_zero
    (exponent : EvmWord) (h_ne : exponent ≠ 0)
    (rest : List EvmWord) :
    runExpStack? { stack := (0 : EvmWord) :: exponent :: rest } =
      some
        { effects :=
            { stackWords := [0]
              dynamicGas := ExpArgs.expDynamicCostFromArgs
                (ExpArgs.expArgs 0 exponent)
              totalGas := ExpArgs.expTotalGasFromArgs
                (ExpArgs.expArgs 0 exponent) }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_zero_left_of_ne_zero exponent h_ne]

theorem runExpStack?_zero_left_of_toNat_pos
    (exponent : EvmWord) (h_pos : 0 < exponent.toNat)
    (rest : List EvmWord) :
    runExpStack? { stack := (0 : EvmWord) :: exponent :: rest } =
      some
        { effects :=
            { stackWords := [0]
              dynamicGas := ExpArgs.expDynamicCostFromArgs
                (ExpArgs.expArgs 0 exponent)
              totalGas := ExpArgs.expTotalGasFromArgs
                (ExpArgs.expArgs 0 exponent) }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_zero_left_of_toNat_pos exponent h_pos]

theorem runExpStack?_two_64
    (rest : List EvmWord) :
    runExpStack? { stack := (2 : EvmWord) :: 64 :: rest } =
      some
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^64)]
              dynamicGas := 50
              totalGas := 60 }
          stack := rest } := by
  rw [runExpStack?_cons]
  simp only [ExpArgs.expResultFromArgs, ExpArgs.expArgs,
    ExpArgs.expDynamicCostFromArgs, ExpArgs.expTotalGasFromArgs]
  rw [EvmWord.exp_two_64]
  rw [ExpGas.expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)]
  rw [ExpGas.expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)]

theorem runExpStack?_two_256
    (rest : List EvmWord) :
    runExpStack? { stack := (2 : EvmWord) :: 256 :: rest } =
      some
        { effects := { stackWords := [0], dynamicGas := 100, totalGas := 110 }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_two_256]
  rw [ExpArgs.expDynamicCostFromArgs_256_exponent]
  rw [ExpArgs.expTotalGasFromArgs_256_exponent]

theorem runExpStack?_two_128
    (rest : List EvmWord) :
    runExpStack? { stack := (2 : EvmWord) :: 128 :: rest } =
      some
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^128)]
              dynamicGas := 50
              totalGas := 60 }
          stack := rest } := by
  rw [runExpStack?_cons]
  simp only [ExpArgs.expResultFromArgs, ExpArgs.expArgs,
    ExpArgs.expDynamicCostFromArgs, ExpArgs.expTotalGasFromArgs]
  rw [EvmWord.exp_two_128]
  rw [ExpGas.expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)]
  rw [ExpGas.expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)]

theorem runExpStack?_two_255
    (rest : List EvmWord) :
    runExpStack? { stack := (2 : EvmWord) :: 255 :: rest } =
      some
        { effects :=
            { stackWords := [BitVec.ofNat 256 (2^255)]
              dynamicGas := 50
              totalGas := 60 }
          stack := rest } := by
  rw [runExpStack?_cons]
  simp only [ExpArgs.expResultFromArgs, ExpArgs.expArgs,
    ExpArgs.expDynamicCostFromArgs, ExpArgs.expTotalGasFromArgs]
  rw [EvmWord.exp_two_255]
  rw [ExpGas.expDynamicCostFromExponent_of_pos_lt_256 (by decide) (by decide)]
  rw [ExpGas.expTotalGasFromExponent_of_pos_lt_256 (by decide) (by decide)]

theorem runExpStack?_max_exponent_gas
    (base : EvmWord) (rest : List EvmWord) :
    (runExpStack? { stack := base :: (-1 : EvmWord) :: rest }).map
      (fun out => (out.effects.dynamicGas, out.effects.totalGas)) =
      some (1600, 1610) := by
  rw [runExpStack?_gas]
  rw [ExpArgs.expDynamicCostFromArgs_max_exponent]
  rw [ExpArgs.expTotalGasFromArgs_max_exponent]

theorem runExpStack?_zero_max_exponent
    (rest : List EvmWord) :
    runExpStack? { stack := (0 : EvmWord) :: (-1 : EvmWord) :: rest } =
      some
        { effects := { stackWords := [0], dynamicGas := 1600, totalGas := 1610 }
          stack := rest } := by
  rw [runExpStack?_cons]
  rw [ExpArgs.expResultFromArgs_zero_left_of_ne_zero]
  rw [ExpArgs.expDynamicCostFromArgs_max_exponent]
  rw [ExpArgs.expTotalGasFromArgs_max_exponent]
  decide

end ExpStackExecutionBridge

end EvmAsm.Evm64
