/-
  EvmAsm.Evm64.SDiv.HandlerBridge

  Connects the pure SDIV opcode handler to the SDIV stack-execution bridge.
-/

module

public import EvmAsm.Evm64.ArithmeticHandlers
public import EvmAsm.Evm64.SDiv.StackExecutionBridge

@[expose] public section

namespace EvmAsm.Evm64
namespace SDivStackExecutionBridge

theorem sdivHandler_pc
    (state : EvmState) :
    (ArithmeticHandlers.sdivHandler state).pc = state.pc := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.sdiv state.stack <;>
    simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem sdivHandler_gas
    (state : EvmState) :
    (ArithmeticHandlers.sdivHandler state).gas = state.gas := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.sdiv state.stack <;>
    simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem sdivHandler_memoryCells
    (state : EvmState) :
    (ArithmeticHandlers.sdivHandler state).memoryCells =
      state.memoryCells := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.sdiv state.stack <;>
    simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem sdivHandler_memory
    (state : EvmState) :
    (ArithmeticHandlers.sdivHandler state).memory = state.memory := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.sdiv state.stack <;>
    simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem sdivHandler_memSize
    (state : EvmState) :
    (ArithmeticHandlers.sdivHandler state).memSize = state.memSize := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.sdiv state.stack <;>
    simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem sdivHandler_code
    (state : EvmState) :
    (ArithmeticHandlers.sdivHandler state).code = state.code := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.sdiv state.stack <;>
    simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem sdivHandler_codeLen
    (state : EvmState) :
    (ArithmeticHandlers.sdivHandler state).codeLen = state.codeLen := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.sdiv state.stack <;>
    simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem sdivHandler_env
    (state : EvmState) :
    (ArithmeticHandlers.sdivHandler state).env = state.env := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.sdiv state.stack <;>
    simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem sdivHandler_codeLenMatches
    (state : EvmState) (h_codeLen : state.codeLenMatches) :
    (ArithmeticHandlers.sdivHandler state).codeLenMatches := by
  unfold EvmState.codeLenMatches at h_codeLen ⊢
  rw [sdivHandler_codeLen, sdivHandler_code]
  exact h_codeLen

theorem sdivHandler_stack_of_runSDivStack?_some
    {state : EvmState} {out : SDivStackResult}
    (h_run : runSDivStack? { stack := state.stack } = some out) :
    (ArithmeticHandlers.sdivHandler state).stack =
      out.effects.stackWords ++ out.stack := by
  rw [runSDivStack?_eq_some_iff] at h_run
  rcases h_run with ⟨dividend, divisor, rest, h_stack, h_out⟩
  simp at h_stack
  subst h_out
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
    SDivArgs.sdivResultFromArgs_eq, SDivArgs.sdivArgs, h_stack]

theorem sdivHandler_status_of_runSDivStack?_some
    {state : EvmState} {out : SDivStackResult}
    (h_run : runSDivStack? { stack := state.stack } = some out) :
    (ArithmeticHandlers.sdivHandler state).status = state.status := by
  rw [runSDivStack?_eq_some_iff] at h_run
  rcases h_run with ⟨dividend, divisor, rest, h_stack, h_out⟩
  simp at h_stack
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
    EvmState.withStack, h_stack]

theorem sdivHandler_status_of_runSDivStack?_none
    {state : EvmState}
    (h_run : runSDivStack? { stack := state.stack } = none) :
    (ArithmeticHandlers.sdivHandler state).status = .error := by
  cases h_stack : state.stack with
  | nil =>
      simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
        h_stack]
  | cons dividend tail =>
      cases h_tail : tail with
      | nil =>
          simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
            h_stack, h_tail]
      | cons divisor rest =>
          simp [runSDivStack?, SDivArgsStackDecode.decodeSDivStack?,
            stackRestAfterSDiv?, Option.bind, h_stack, h_tail] at h_run

theorem sdivHandler_status_empty_stack
    (state : EvmState) :
    (ArithmeticHandlers.sdivHandler { state with stack := [] }).status =
      .error := by
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler]

theorem sdivHandler_status_singleton_stack
    (state : EvmState) (dividend : EvmWord) :
    (ArithmeticHandlers.sdivHandler
      { state with stack := [dividend] }).status = .error := by
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler]

theorem sdivHandler_stack_zero_divisor
    (state : EvmState) (dividend : EvmWord) (rest : List EvmWord) :
    (ArithmeticHandlers.sdivHandler
      { state with stack := dividend :: 0 :: rest }).stack =
        0 :: rest := by
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.sdiv_zero_right

theorem sdivHandler_stack_intMin_neg_one
    (state : EvmState) (rest : List EvmWord) :
    (ArithmeticHandlers.sdivHandler
      { state with stack := BitVec.intMin 256 :: (-1 : EvmWord) :: rest }).stack =
        BitVec.intMin 256 :: rest := by
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.sdiv_intMin_neg_one

theorem sdivHandler_stack_neg_one_two
    (state : EvmState) (rest : List EvmWord) :
    (ArithmeticHandlers.sdivHandler
      { state with stack := (-1 : EvmWord) :: 2 :: rest }).stack =
        0 :: rest := by
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.sdiv_neg_one_two

theorem sdivHandler_stack_pos_neg_trunc
    (state : EvmState) (rest : List EvmWord) :
    (ArithmeticHandlers.sdivHandler
      { state with stack := (7 : EvmWord) :: (-2 : EvmWord) :: rest }).stack =
        (-3 : EvmWord) :: rest := by
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.sdiv_pos_neg_trunc

end SDivStackExecutionBridge
end EvmAsm.Evm64
