/-
  EvmAsm.Evm64.SupportedLoopBridge

  Concrete adapter from the supported pure handler table to the interpreter
  loop (GH #107 / GH #108).
-/

module

public import EvmAsm.Evm64.HandlerLoopBridge
public import EvmAsm.Evm64.SupportedHandlers
public import EvmAsm.Evm64.SDiv.HandlerBridge
public import EvmAsm.Evm64.SMod.HandlerBridge

@[expose] public section

namespace EvmAsm.Evm64

namespace SupportedLoopBridge

/--
Interpreter-loop handler backed by every pure opcode handler currently wired
into `SupportedHandlers.supportedHandlerTable`.

Distinctive token: SupportedLoopBridge.supportedLoopHandler #107 #108.
-/
def supportedLoopHandler : InterpreterLoop.Handler :=
  HandlerLoopBridge.toLoopHandler SupportedHandlers.supportedHandlerTable

@[simp] theorem supportedLoopHandler_apply
    (opcode : EvmOpcode) (state : EvmState) :
    supportedLoopHandler opcode state =
      HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable opcode state := rfl

theorem stepWithSupportedHandler_of_decode
    {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state =
      HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable opcode state := by
  exact HandlerLoopBridge.stepWithTableHandler_of_decode
    SupportedHandlers.supportedHandlerTable h_decode

theorem stepWithSupportedHandler_of_decode_status
    {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      (HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable opcode state).status := by
  rw [stepWithSupportedHandler_of_decode h_decode]

theorem stepWithSupportedHandler_of_lookup
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state = handler state := by
  rw [stepWithSupportedHandler_of_decode h_decode]
  exact SupportedHandlers.dispatchOpcode_of_lookup h_lookup state

theorem stepWithSupportedHandler_of_lookup_status
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      (handler state).status := by
  rw [stepWithSupportedHandler_of_lookup h_decode h_lookup]

theorem stepWithSupportedHandler_of_lookup_pc
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).pc =
      (handler state).pc := by
  rw [stepWithSupportedHandler_of_lookup h_decode h_lookup]

theorem stepWithSupportedHandler_of_lookup_gas
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).gas =
      (handler state).gas := by
  rw [stepWithSupportedHandler_of_lookup h_decode h_lookup]

theorem stepWithSupportedHandler_of_lookup_stack
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).stack =
      (handler state).stack := by
  rw [stepWithSupportedHandler_of_lookup h_decode h_lookup]

theorem stepWithSupportedHandler_of_lookup_memoryCells
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).memoryCells =
      (handler state).memoryCells := by
  rw [stepWithSupportedHandler_of_lookup h_decode h_lookup]

theorem stepWithSupportedHandler_of_lookup_memory
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler)
    (addr : Nat) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).memory addr =
      (handler state).memory addr := by
  rw [stepWithSupportedHandler_of_lookup h_decode h_lookup]

theorem stepWithSupportedHandler_of_lookup_memSize
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).memSize =
      (handler state).memSize := by
  rw [stepWithSupportedHandler_of_lookup h_decode h_lookup]

theorem stepWithSupportedHandler_of_lookup_code
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).code =
      (handler state).code := by
  rw [stepWithSupportedHandler_of_lookup h_decode h_lookup]

theorem stepWithSupportedHandler_of_lookup_codeLen
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).codeLen =
      (handler state).codeLen := by
  rw [stepWithSupportedHandler_of_lookup h_decode h_lookup]

theorem stepWithSupportedHandler_of_lookup_preserves_codeLenMatches
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler)
    (h_codeLen : ∀ state : EvmState,
      state.codeLenMatches → (handler state).codeLenMatches)
    (h_state : state.codeLenMatches) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).codeLenMatches := by
  rw [stepWithSupportedHandler_of_lookup h_decode h_lookup]
  exact h_codeLen state h_state

theorem stepWithSupportedHandler_of_lookup_env
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).env =
      (handler state).env := by
  rw [stepWithSupportedHandler_of_lookup h_decode h_lookup]

/--
When the supported interpreter loop decodes a valid PUSH opcode, the one-step
handler has the same bundled PC and stack effect as the executable PUSH bridge.

Distinctive token:
SupportedLoopBridge.stepWithSupportedHandler_PUSH_effectFromCode
#101 #107 #108.
-/
theorem stepWithSupportedHandler_PUSH_effectFromCode
    {state : EvmState} {n : Nat}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state =
      some (EvmOpcode.PUSH n))
    (h_valid : EvmOpcode.validPushWidth n = true) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).pc =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).pc ∧
      (InterpreterLoop.stepWithHandler supportedLoopHandler state).stack =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).stack := by
  rw [stepWithSupportedHandler_of_decode h_decode]
  exact SupportedHandlers.dispatchOpcode_supportedHandlerTable_PUSH_effectFromCode
    h_valid state

theorem stepWithSupportedHandler_PUSH_status
    {state : EvmState} {n : Nat}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state =
      some (EvmOpcode.PUSH n))
    (h_valid : EvmOpcode.validPushWidth n = true) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      state.status := by
  rw [stepWithSupportedHandler_of_decode h_decode]
  exact SupportedHandlers.dispatchOpcode_supportedHandlerTable_PUSH_of_valid_status
    h_valid state

theorem stepWithSupportedHandler_DUP_status_of_some
    {state : EvmState} {n : Nat} {stack' : List EvmWord}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state =
      some (EvmOpcode.DUP n))
    (h_valid : EvmOpcode.validDupIndex n = true)
    (h_stack : DupSwapHandlers.dupStack? n state.stack = some stack') :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      state.status := by
  rw [stepWithSupportedHandler_of_decode h_decode]
  exact SupportedHandlers.dispatchOpcode_supportedHandlerTable_DUP_of_valid_status_of_some
    h_valid h_stack

theorem stepWithSupportedHandler_SWAP_status_of_some
    {state : EvmState} {n : Nat} {stack' : List EvmWord}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state =
      some (EvmOpcode.SWAP n))
    (h_valid : EvmOpcode.validSwapIndex n = true)
    (h_stack : DupSwapHandlers.swapStack? n state.stack = some stack') :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      state.status := by
  rw [stepWithSupportedHandler_of_decode h_decode]
  exact SupportedHandlers.dispatchOpcode_supportedHandlerTable_SWAP_of_valid_status_of_some
    h_valid h_stack

theorem stepWithSupportedHandler_SDIV
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state =
      ArithmeticHandlers.sdivHandler state := by
  exact stepWithSupportedHandler_of_lookup h_decode
    SupportedHandlers.supportedHandlerTable_SDIV

theorem stepWithSupportedHandler_SMOD
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state =
      ArithmeticHandlers.smodHandler state := by
  exact stepWithSupportedHandler_of_lookup h_decode
    SupportedHandlers.supportedHandlerTable_SMOD

theorem stepWithSupportedHandler_SDIV_pc
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).pc =
      state.pc := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_pc state

theorem stepWithSupportedHandler_SMOD_pc
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).pc =
      state.pc := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_pc state

theorem stepWithSupportedHandler_SDIV_gas
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).gas =
      state.gas := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_gas state

theorem stepWithSupportedHandler_SMOD_gas
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).gas =
      state.gas := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_gas state

theorem stepWithSupportedHandler_SDIV_code
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).code =
      state.code := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_code state

theorem stepWithSupportedHandler_SMOD_code
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).code =
      state.code := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_code state

theorem stepWithSupportedHandler_SDIV_codeLen
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).codeLen =
      state.codeLen := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_codeLen state

theorem stepWithSupportedHandler_SMOD_codeLen
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).codeLen =
      state.codeLen := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_codeLen state

theorem stepWithSupportedHandler_SDIV_env
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).env =
      state.env := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_env state

theorem stepWithSupportedHandler_SMOD_env
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).env =
      state.env := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_env state

theorem stepWithSupportedHandler_SDIV_codeLenMatches
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV)
    (h_codeLen : state.codeLenMatches) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).codeLenMatches := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_codeLenMatches state h_codeLen

theorem stepWithSupportedHandler_SMOD_codeLenMatches
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD)
    (h_codeLen : state.codeLenMatches) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).codeLenMatches := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_codeLenMatches state h_codeLen

theorem stepWithSupportedHandler_SDIV_memoryCells
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).memoryCells =
      state.memoryCells := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_memoryCells state

theorem stepWithSupportedHandler_SDIV_memory
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).memory =
      state.memory := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_memory state

theorem stepWithSupportedHandler_SDIV_memSize
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).memSize =
      state.memSize := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_memSize state

theorem stepWithSupportedHandler_SMOD_memoryCells
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).memoryCells =
      state.memoryCells := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_memoryCells state

theorem stepWithSupportedHandler_SMOD_memory
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).memory =
      state.memory := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_memory state

theorem stepWithSupportedHandler_SMOD_memSize
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).memSize =
      state.memSize := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_memSize state

theorem stepWithSupportedHandler_SDIV_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV)
    (h_stack : ArithmeticHandlers.binaryStack? EvmWord.sdiv state.stack =
      some stack') :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      state.status := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
    h_stack, EvmState.withStack]

theorem stepWithSupportedHandler_SMOD_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD)
    (h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack =
      some stack') :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      state.status := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
    h_stack, EvmState.withStack]

theorem stepWithSupportedHandler_SDIV_stack_of_runSDivStack?_some
    {state : EvmState} {out : SDivStackExecutionBridge.SDivStackResult}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV)
    (h_run :
      SDivStackExecutionBridge.runSDivStack? { stack := state.stack } =
        some out) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).stack =
      out.effects.stackWords ++ out.stack := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_stack_of_runSDivStack?_some
    h_run

theorem stepWithSupportedHandler_SMOD_stack_of_runSModStack?_some
    {state : EvmState} {out : SModStackExecutionBridge.SModStackResult}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD)
    (h_run :
      SModStackExecutionBridge.runSModStack? { stack := state.stack } =
        some out) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).stack =
      out.effects.stackWords ++ out.stack := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_stack_of_runSModStack?_some
    h_run

theorem stepWithSupportedHandler_SDIV_status_empty_stack
    {state : EvmState}
    (h_decode :
      InterpreterLoop.decodeCurrentOpcode? { state with stack := [] } =
        some .SDIV) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler
      { state with stack := [] }).status = .error := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_status_empty_stack state

theorem stepWithSupportedHandler_SDIV_status_singleton_stack
    {state : EvmState} (dividend : EvmWord)
    (h_decode :
      InterpreterLoop.decodeCurrentOpcode?
        { state with stack := [dividend] } = some .SDIV) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler
      { state with stack := [dividend] }).status = .error := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_status_singleton_stack
    state dividend

theorem stepWithSupportedHandler_SMOD_status_empty_stack
    {state : EvmState}
    (h_decode :
      InterpreterLoop.decodeCurrentOpcode? { state with stack := [] } =
        some .SMOD) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler
      { state with stack := [] }).status = .error := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_status_empty_stack state

theorem stepWithSupportedHandler_SMOD_status_singleton_stack
    {state : EvmState} (dividend : EvmWord)
    (h_decode :
      InterpreterLoop.decodeCurrentOpcode?
        { state with stack := [dividend] } = some .SMOD) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler
      { state with stack := [dividend] }).status = .error := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_status_singleton_stack
    state dividend

theorem stepWithSupportedHandler_SDIV_status_of_runSDivStack?_none
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV)
    (h_run :
      SDivStackExecutionBridge.runSDivStack? { stack := state.stack } =
        none) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      .error := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_status_of_runSDivStack?_none
    h_run

theorem stepWithSupportedHandler_SMOD_status_of_runSModStack?_none
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD)
    (h_run :
      SModStackExecutionBridge.runSModStack? { stack := state.stack } =
        none) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      .error := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_status_of_runSModStack?_none
    h_run

theorem stepWithSupportedHandler_SDIV_status_of_runSDivStack?_some
    {state : EvmState} {out : SDivStackExecutionBridge.SDivStackResult}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV)
    (h_run :
      SDivStackExecutionBridge.runSDivStack? { stack := state.stack } =
        some out) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      state.status := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_status_of_runSDivStack?_some
    h_run

theorem stepWithSupportedHandler_SMOD_status_of_runSModStack?_some
    {state : EvmState} {out : SModStackExecutionBridge.SModStackResult}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD)
    (h_run :
      SModStackExecutionBridge.runSModStack? { stack := state.stack } =
        some out) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      state.status := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_status_of_runSModStack?_some
    h_run

theorem stepWithSupportedHandler_SDIV_stack_zero_divisor
    {state : EvmState} (dividend : EvmWord) (rest : List EvmWord)
    (h_decode :
      InterpreterLoop.decodeCurrentOpcode?
        { state with stack := dividend :: 0 :: rest } = some .SDIV)
    :
    (InterpreterLoop.stepWithHandler supportedLoopHandler
      { state with stack := dividend :: 0 :: rest }).stack =
        0 :: rest := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_stack_zero_divisor state
    dividend rest

theorem stepWithSupportedHandler_SDIV_stack_intMin_neg_one
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode?
      { state with stack := BitVec.intMin 256 :: (-1 : EvmWord) :: state.stack } =
        some .SDIV) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler
      { state with stack := BitVec.intMin 256 :: (-1 : EvmWord) :: state.stack }).stack =
        BitVec.intMin 256 :: state.stack := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_stack_intMin_neg_one state
    state.stack

theorem stepWithSupportedHandler_SDIV_stack_neg_one_two
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode?
      { state with stack := (-1 : EvmWord) :: 2 :: state.stack } = some .SDIV) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler
      { state with stack := (-1 : EvmWord) :: 2 :: state.stack }).stack =
        0 :: state.stack := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_stack_neg_one_two state
    state.stack

theorem stepWithSupportedHandler_SDIV_stack_pos_neg_trunc
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode?
      { state with stack := (7 : EvmWord) :: (-2 : EvmWord) :: state.stack } =
        some .SDIV) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler
      { state with stack := (7 : EvmWord) :: (-2 : EvmWord) :: state.stack }).stack =
        (-3 : EvmWord) :: state.stack := by
  rw [stepWithSupportedHandler_SDIV h_decode]
  exact SDivStackExecutionBridge.sdivHandler_stack_pos_neg_trunc state
    state.stack

theorem stepWithSupportedHandler_SMOD_stack_zero_divisor
    {state : EvmState} (dividend : EvmWord) (rest : List EvmWord)
    (h_decode :
      InterpreterLoop.decodeCurrentOpcode?
        { state with stack := dividend :: 0 :: rest } = some .SMOD)
    :
    (InterpreterLoop.stepWithHandler supportedLoopHandler
      { state with stack := dividend :: 0 :: rest }).stack =
        0 :: rest := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_stack_zero_divisor state
    dividend rest

theorem stepWithSupportedHandler_SMOD_stack_neg_pos_sign
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode?
      { state with stack := (-3 : EvmWord) :: 2 :: state.stack } = some .SMOD) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler
      { state with stack := (-3 : EvmWord) :: 2 :: state.stack }).stack =
        (-1 : EvmWord) :: state.stack := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_stack_neg_pos_sign state
    state.stack

theorem stepWithSupportedHandler_SMOD_stack_pos_neg_sign
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode?
      { state with stack := (3 : EvmWord) :: (-2 : EvmWord) :: state.stack } =
        some .SMOD) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler
      { state with stack := (3 : EvmWord) :: (-2 : EvmWord) :: state.stack }).stack =
        (1 : EvmWord) :: state.stack := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_stack_pos_neg_sign state
    state.stack

theorem stepWithSupportedHandler_SMOD_stack_neg_neg_sign
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode?
      { state with stack := (-3 : EvmWord) :: (-2 : EvmWord) :: state.stack } =
        some .SMOD) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler
      { state with stack := (-3 : EvmWord) :: (-2 : EvmWord) :: state.stack }).stack =
        (-1 : EvmWord) :: state.stack := by
  rw [stepWithSupportedHandler_SMOD h_decode]
  exact SModStackExecutionBridge.smodHandler_stack_neg_neg_sign state
    state.stack

/--
When the combined supported loop decodes STOP, one interpreter step terminates
successfully.

Distinctive token: SupportedLoopBridge.stepWithSupportedHandler_STOP #107 #108 #113.
-/
theorem stepWithSupportedHandler_STOP
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .STOP) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state = state.stop := by
  exact stepWithSupportedHandler_of_lookup h_decode
    SupportedHandlers.supportedHandlerTable_STOP

theorem stepWithSupportedHandler_STOP_status
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .STOP) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      .stopped := by
  rw [stepWithSupportedHandler_STOP h_decode]
  exact EvmState.stop_status state

/--
When the combined supported loop decodes INVALID, one interpreter step enters
the invalid/error state.

Distinctive token: SupportedLoopBridge.stepWithSupportedHandler_INVALID #107 #108 #113.
-/
theorem stepWithSupportedHandler_INVALID
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .INVALID) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state = state.invalid := by
  exact stepWithSupportedHandler_of_lookup h_decode
    SupportedHandlers.supportedHandlerTable_INVALID

theorem stepWithSupportedHandler_INVALID_status
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .INVALID) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      .error := by
  rw [stepWithSupportedHandler_INVALID h_decode]
  exact EvmState.invalid_status state

theorem stepWithSupportedHandler_missing_invalid
    {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = none) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state = state.invalid := by
  exact HandlerLoopBridge.stepWithTableHandler_missing_invalid h_decode h_lookup

theorem stepWithSupportedHandler_missing_invalid_status
    {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = none) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      .error := by
  rw [stepWithSupportedHandler_missing_invalid h_decode h_lookup]
  exact EvmState.invalid_status state

theorem loopFuel_supported_succ_running_decode
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps
        (HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable opcode state) := by
  exact HandlerLoopBridge.loopFuel_succ_running_decode
    SupportedHandlers.supportedHandlerTable nSteps h_status h_decode

theorem loopFuel_supported_succ_running_decode_status
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    (InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state).status =
      (InterpreterLoop.loopFuel supportedLoopHandler nSteps
        (HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable opcode state)).status := by
  rw [loopFuel_supported_succ_running_decode nSteps h_status h_decode]

theorem loopFuel_supported_succ_running_lookup
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps (handler state) := by
  rw [loopFuel_supported_succ_running_decode nSteps h_status h_decode]
  rw [SupportedHandlers.dispatchOpcode_of_lookup h_lookup state]

theorem loopFuel_supported_succ_running_lookup_status
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    (InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state).status =
      (InterpreterLoop.loopFuel supportedLoopHandler nSteps (handler state)).status := by
  rw [loopFuel_supported_succ_running_lookup nSteps h_status h_decode h_lookup]

theorem loopFuel_supported_succ_running_STOP
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .STOP) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.stop := by
  exact loopFuel_supported_succ_running_lookup nSteps h_status h_decode
    SupportedHandlers.supportedHandlerTable_STOP

theorem loopFuel_supported_stop_fixed :
    ∀ (nSteps : Nat) (state : EvmState),
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.stop = state.stop
  | 0, _ => rfl
  | nSteps + 1, state => by
      simp [InterpreterLoop.loopFuel]

theorem loopFuel_supported_stop_fixed_status
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel supportedLoopHandler nSteps state.stop).status =
      .stopped := by
  rw [loopFuel_supported_stop_fixed nSteps state]
  exact EvmState.stop_status state

theorem loopFuel_supported_succ_running_STOP_status
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .STOP) :
    (InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state).status =
      .stopped := by
  rw [loopFuel_supported_succ_running_STOP nSteps h_status h_decode]
  exact loopFuel_supported_stop_fixed_status nSteps state

theorem loopFuel_supported_succ_running_INVALID
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .INVALID) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.invalid := by
  exact loopFuel_supported_succ_running_lookup nSteps h_status h_decode
    SupportedHandlers.supportedHandlerTable_INVALID

theorem loopFuel_supported_invalid_fixed :
    ∀ (nSteps : Nat) (state : EvmState),
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.invalid = state.invalid
  | 0, _ => rfl
  | nSteps + 1, state => by
      simp [InterpreterLoop.loopFuel]

theorem loopFuel_supported_invalid_fixed_status
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel supportedLoopHandler nSteps state.invalid).status =
      .error := by
  rw [loopFuel_supported_invalid_fixed nSteps state]
  exact EvmState.invalid_status state

theorem loopFuel_supported_succ_running_INVALID_status
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .INVALID) :
    (InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state).status =
      .error := by
  rw [loopFuel_supported_succ_running_INVALID nSteps h_status h_decode]
  exact loopFuel_supported_invalid_fixed_status nSteps state

theorem loopFuel_supported_succ_running_SDIV
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SDIV) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps
        (ArithmeticHandlers.sdivHandler state) := by
  exact loopFuel_supported_succ_running_lookup nSteps h_status h_decode
    SupportedHandlers.supportedHandlerTable_SDIV

theorem loopFuel_supported_succ_running_SMOD
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .SMOD) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps
        (ArithmeticHandlers.smodHandler state) := by
  exact loopFuel_supported_succ_running_lookup nSteps h_status h_decode
    SupportedHandlers.supportedHandlerTable_SMOD

theorem loopFuel_supported_missing_invalid
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = none) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.invalid := by
  rw [loopFuel_supported_succ_running_decode nSteps h_status h_decode]
  exact congrArg (InterpreterLoop.loopFuel supportedLoopHandler nSteps)
    (HandlerTable.dispatchOpcode_none h_lookup state)

theorem loopFuel_supported_missing_invalid_status
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = none) :
    (InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state).status =
      .error := by
  rw [loopFuel_supported_missing_invalid nSteps h_status h_decode h_lookup]
  exact loopFuel_supported_invalid_fixed_status nSteps state

theorem loopFuel_supported_succ_running_unsupported_invalid
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.invalid :=
  HandlerLoopBridge.loopFuel_succ_running_unsupported_invalid
    SupportedHandlers.supportedHandlerTable nSteps h_status h_decode

theorem loopFuel_supported_succ_running_unsupported_status
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    (InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state).status =
      .error := by
  rw [loopFuel_supported_succ_running_unsupported_invalid nSteps h_status h_decode]
  exact loopFuel_supported_invalid_fixed_status nSteps state

end SupportedLoopBridge

end EvmAsm.Evm64
