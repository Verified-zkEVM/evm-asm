/-
  EvmAsm.Evm64.SMod.HandlerBridge

  Connects the pure SMOD opcode handler to the SMOD stack-execution bridge.
-/

module

public import EvmAsm.Evm64.ArithmeticHandlers
public import EvmAsm.Evm64.SMod.StackExecutionBridge

public section

namespace EvmAsm.Evm64
namespace SModStackExecutionBridge

theorem smodHandler_pc
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).pc = state.pc := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem smodHandler_gas
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).gas = state.gas := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem smodHandler_memoryCells
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).memoryCells =
      state.memoryCells := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem smodHandler_memory
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).memory = state.memory := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem smodHandler_memSize
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).memSize = state.memSize := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem smodHandler_code
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).code = state.code := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem smodHandler_codeLen
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).codeLen = state.codeLen := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem smodHandler_env
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).env = state.env := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]

theorem smodHandler_codeLenMatches
    (state : EvmState) (h_codeLen : state.codeLenMatches) :
    (ArithmeticHandlers.smodHandler state).codeLenMatches := by
  unfold EvmState.codeLenMatches at h_codeLen ⊢
  rw [smodHandler_codeLen, smodHandler_code]
  exact h_codeLen

theorem smodHandler_stack_of_runSModStack?_some
    {state : EvmState} {out : SModStackResult}
    (h_run : runSModStack? { stack := state.stack } = some out) :
    (ArithmeticHandlers.smodHandler state).stack =
      out.effects.stackWords ++ out.stack := by
  rw [runSModStack?_eq_some_iff] at h_run
  rcases h_run with ⟨dividend, divisor, rest, h_stack, h_out⟩
  simp at h_stack
  subst h_out
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
    SModArgs.smodResultFromArgs_eq, SModArgs.smodArgs, h_stack]

theorem smodHandler_status_of_runSModStack?_some
    {state : EvmState} {out : SModStackResult}
    (h_run : runSModStack? { stack := state.stack } = some out) :
    (ArithmeticHandlers.smodHandler state).status = state.status := by
  rw [runSModStack?_eq_some_iff] at h_run
  rcases h_run with ⟨dividend, divisor, rest, h_stack, h_out⟩
  simp at h_stack
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
    EvmState.withStack, h_stack]

theorem smodHandler_status_of_runSModStack?_none
    {state : EvmState}
    (h_run : runSModStack? { stack := state.stack } = none) :
    (ArithmeticHandlers.smodHandler state).status = .error := by
  cases h_stack : state.stack with
  | nil =>
      simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
        h_stack]
  | cons dividend tail =>
      cases h_tail : tail with
      | nil =>
          simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
            h_stack, h_tail]
      | cons divisor rest =>
          simp [runSModStack?, SModArgsStackDecode.decodeSModStack?,
            stackRestAfterSMod?, Option.bind, h_stack, h_tail] at h_run

theorem smodHandler_status_empty_stack
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler { state with stack := [] }).status =
      .error := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]

theorem smodHandler_status_singleton_stack
    (state : EvmState) (dividend : EvmWord) :
    (ArithmeticHandlers.smodHandler
      { state with stack := [dividend] }).status = .error := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]

theorem smodHandler_stack_zero_divisor
    (state : EvmState) (dividend : EvmWord) (rest : List EvmWord) :
    (ArithmeticHandlers.smodHandler
      { state with stack := dividend :: 0 :: rest }).stack =
        0 :: rest := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.smod_zero_right

theorem smodHandler_stack_intMin_neg_one
    (state : EvmState) (rest : List EvmWord) :
    (ArithmeticHandlers.smodHandler
      { state with stack := BitVec.intMin 256 :: (-1 : EvmWord) :: rest }).stack =
        0 :: rest := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.smod_intMin_neg_one

theorem smodHandler_stack_neg_pos_sign
    (state : EvmState) (rest : List EvmWord) :
    (ArithmeticHandlers.smodHandler
      { state with stack := (-3 : EvmWord) :: 2 :: rest }).stack =
        (-1 : EvmWord) :: rest := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.smod_neg_pos_sign

theorem smodHandler_stack_pos_neg_sign
    (state : EvmState) (rest : List EvmWord) :
    (ArithmeticHandlers.smodHandler
      { state with stack := (3 : EvmWord) :: (-2 : EvmWord) :: rest }).stack =
        (1 : EvmWord) :: rest := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.smod_pos_neg_sign

theorem smodHandler_stack_neg_neg_sign
    (state : EvmState) (rest : List EvmWord) :
    (ArithmeticHandlers.smodHandler
      { state with stack := (-3 : EvmWord) :: (-2 : EvmWord) :: rest }).stack =
        (-1 : EvmWord) :: rest := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.smod_neg_neg_sign

end SModStackExecutionBridge
end EvmAsm.Evm64
