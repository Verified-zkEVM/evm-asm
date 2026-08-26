/-
  EvmAsm.Evm64.SupportedHandlerByte

  Raw-byte dispatch bridge for the combined supported interpreter handler
  table (GH #106 / GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTableByte
public import EvmAsm.Evm64.SDiv.HandlerBridge
public import EvmAsm.Evm64.SMod.HandlerBridge
public import EvmAsm.Evm64.SupportedHandlers

public section

namespace EvmAsm.Evm64
namespace SupportedHandlerByte

theorem dispatchByte_supported_of_lookup
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      handler state := by
  rw [HandlerTable.dispatchByte_decoded
    SupportedHandlers.supportedHandlerTable b opcode state h_decode]
  exact SupportedHandlers.dispatchOpcode_of_lookup h_lookup state

theorem dispatchByte_supported_of_lookup_status
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      (handler state).status := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]

theorem dispatchByte_supported_of_lookup_pc
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).pc =
      (handler state).pc := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]

theorem dispatchByte_supported_of_lookup_gas
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).gas =
      (handler state).gas := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]

theorem dispatchByte_supported_of_lookup_stack
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).stack =
      (handler state).stack := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]

theorem dispatchByte_supported_of_lookup_memoryCells
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).memoryCells =
      (handler state).memoryCells := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]

theorem dispatchByte_supported_of_lookup_memory
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) (addr : Nat) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).memory addr =
      (handler state).memory addr := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]

theorem dispatchByte_supported_of_lookup_memSize
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).memSize =
      (handler state).memSize := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]

theorem dispatchByte_supported_of_lookup_code
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).code =
      (handler state).code := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]

theorem dispatchByte_supported_of_lookup_codeLen
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).codeLen =
      (handler state).codeLen := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]

theorem dispatchByte_supported_of_lookup_env
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).env =
      (handler state).env := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]

/--
Decoded byte dispatch through the supported table preserves status whenever the
looked-up handler does.

Distinctive token: supportedByteLookupPreservesStatus #107.
-/
theorem dispatchByte_supported_of_lookup_preserves_status
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (h_status : ∀ state : EvmState, (handler state).status = state.status)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      state.status := by
  rw [dispatchByte_supported_of_lookup_status h_decode h_lookup state]
  exact h_status state

/--
Decoded byte dispatch through the supported table preserves `codeLenMatches`
whenever the looked-up handler does.

Distinctive token: supportedByteLookupPreservesCodeLenMatches #107.
-/
theorem dispatchByte_supported_of_lookup_preserves_codeLenMatches
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (h_codeLen : ∀ state : EvmState,
      state.codeLenMatches → (handler state).codeLenMatches)
    (state : EvmState) (h_state : state.codeLenMatches) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).codeLenMatches := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]
  exact h_codeLen state h_state

theorem dispatchByte_supported_of_decode
    {b : Fin 256} {opcode : EvmOpcode}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable
        opcode state := by
  exact HandlerTable.dispatchByte_decoded
    SupportedHandlers.supportedHandlerTable b opcode state h_decode

theorem dispatchByte_supported_of_decode_status
    {b : Fin 256} {opcode : EvmOpcode}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      (HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable
        opcode state).status := by
  rw [dispatchByte_supported_of_decode h_decode state]

/--
Byte-level dispatch of a decoded valid PUSH opcode through the combined
supported-handler table has the same program-counter and stack effect as the
executable PUSH bridge.

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_PUSH_effectFromCode #101 #107.
-/
theorem dispatchByte_supported_PUSH_effectFromCode
    {b : Fin 256} {n : Nat}
    (h_decode : EvmOpcode.decodeByte? b.val = some (EvmOpcode.PUSH n))
    (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).pc =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).pc ∧
      (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).stack =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).stack := by
  rw [dispatchByte_supported_of_decode h_decode state]
  exact SupportedHandlers.dispatchOpcode_supportedHandlerTable_PUSH_effectFromCode
    h_valid state

/--
Status projection for byte-level dispatch of a decoded valid PUSH opcode
through the combined supported-handler table.

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_PUSH_status #101 #107.
-/
theorem dispatchByte_supported_PUSH_status
    {b : Fin 256} {n : Nat}
    (h_decode : EvmOpcode.decodeByte? b.val = some (EvmOpcode.PUSH n))
    (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      state.status := by
  rw [dispatchByte_supported_of_decode h_decode state]
  rw [HandlerTable.dispatchOpcode_some
    (SupportedHandlers.supportedHandlerTable_PUSH_of_valid h_valid) state]
  exact PushHandlers.pushHandler_status n state

/--
Concrete STOP byte dispatch through the combined supported-handler table
terminates the state successfully.

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_STOP_byte #106 #107 #113.
-/
theorem dispatchByte_supported_STOP_byte
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x00, by decide⟩ : Fin 256) state = state.stop := by
  exact dispatchByte_supported_of_lookup EvmOpcode.decodeByte?_STOP
    SupportedHandlers.supportedHandlerTable_STOP state

@[simp] theorem dispatchByte_supported_STOP_byte_status
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x00, by decide⟩ : Fin 256) state).status = .stopped := by
  rw [dispatchByte_supported_STOP_byte]
  exact EvmState.stop_status state

theorem dispatchByte_supported_INVALID_byte
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0xfe, by decide⟩ : Fin 256) state = state.invalid := by
  exact dispatchByte_supported_of_lookup EvmOpcode.decodeByte?_INVALID
    SupportedHandlers.supportedHandlerTable_INVALID state

@[simp] theorem dispatchByte_supported_INVALID_byte_status
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0xfe, by decide⟩ : Fin 256) state).status = .error := by
  rw [dispatchByte_supported_INVALID_byte]
  exact EvmState.invalid_status state

theorem dispatchByte_supported_SDIV_byte
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state =
        ArithmeticHandlers.sdivHandler state := by
  exact dispatchByte_supported_of_lookup rfl
    SupportedHandlers.supportedHandlerTable_SDIV state

theorem dispatchByte_supported_SMOD_byte
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state =
        ArithmeticHandlers.smodHandler state := by
  exact dispatchByte_supported_of_lookup rfl
    SupportedHandlers.supportedHandlerTable_SMOD state

theorem dispatchByte_supported_SDIV_byte_pc
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).pc = state.pc := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_pc state

theorem dispatchByte_supported_SMOD_byte_pc
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).pc = state.pc := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_pc state

theorem dispatchByte_supported_SDIV_byte_gas
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).gas = state.gas := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_gas state

theorem dispatchByte_supported_SMOD_byte_gas
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).gas = state.gas := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_gas state

theorem dispatchByte_supported_SDIV_byte_code
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).code = state.code := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_code state

theorem dispatchByte_supported_SMOD_byte_code
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).code = state.code := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_code state

theorem dispatchByte_supported_SDIV_byte_codeLen
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).codeLen =
        state.codeLen := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_codeLen state

theorem dispatchByte_supported_SMOD_byte_codeLen
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).codeLen =
        state.codeLen := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_codeLen state

theorem dispatchByte_supported_SDIV_byte_env
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).env = state.env := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_env state

theorem dispatchByte_supported_SMOD_byte_env
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).env = state.env := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_env state

theorem dispatchByte_supported_SDIV_byte_codeLenMatches
    (state : EvmState) (h_codeLen : state.codeLenMatches) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).codeLenMatches := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_codeLenMatches state h_codeLen

theorem dispatchByte_supported_SMOD_byte_codeLenMatches
    (state : EvmState) (h_codeLen : state.codeLenMatches) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).codeLenMatches := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_codeLenMatches state h_codeLen

theorem dispatchByte_supported_SDIV_byte_memoryCells
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).memoryCells =
        state.memoryCells := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_memoryCells state

theorem dispatchByte_supported_SDIV_byte_memory
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).memory = state.memory := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_memory state

theorem dispatchByte_supported_SDIV_byte_memSize
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).memSize =
        state.memSize := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_memSize state

theorem dispatchByte_supported_SMOD_byte_memoryCells
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).memoryCells =
        state.memoryCells := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_memoryCells state

theorem dispatchByte_supported_SMOD_byte_memory
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).memory = state.memory := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_memory state

theorem dispatchByte_supported_SMOD_byte_memSize
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).memSize =
        state.memSize := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_memSize state

theorem dispatchByte_supported_SDIV_byte_stack_zero_divisor
    (state : EvmState) (dividend : EvmWord) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256)
      { state with stack := dividend :: 0 :: rest }).stack =
        0 :: rest := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_stack_zero_divisor
    state dividend rest

theorem dispatchByte_supported_SDIV_byte_stack_intMin_neg_one
    (state : EvmState) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256)
      { state with stack := BitVec.intMin 256 :: (-1 : EvmWord) :: rest }).stack =
        BitVec.intMin 256 :: rest := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_stack_intMin_neg_one state rest

theorem dispatchByte_supported_SDIV_byte_stack_neg_one_two
    (state : EvmState) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256)
      { state with stack := (-1 : EvmWord) :: 2 :: rest }).stack =
        0 :: rest := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_stack_neg_one_two state rest

theorem dispatchByte_supported_SDIV_byte_stack_pos_neg_trunc
    (state : EvmState) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256)
      { state with stack := (7 : EvmWord) :: (-2 : EvmWord) :: rest }).stack =
        (-3 : EvmWord) :: rest := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_stack_pos_neg_trunc state rest

theorem dispatchByte_supported_SMOD_byte_stack_zero_divisor
    (state : EvmState) (dividend : EvmWord) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256)
      { state with stack := dividend :: 0 :: rest }).stack =
        0 :: rest := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_stack_zero_divisor
    state dividend rest

theorem dispatchByte_supported_SMOD_byte_stack_neg_pos_sign
    (state : EvmState) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256)
      { state with stack := (-3 : EvmWord) :: 2 :: rest }).stack =
        (-1 : EvmWord) :: rest := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_stack_neg_pos_sign state rest

theorem dispatchByte_supported_SMOD_byte_stack_pos_neg_sign
    (state : EvmState) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256)
      { state with stack := (3 : EvmWord) :: (-2 : EvmWord) :: rest }).stack =
        (1 : EvmWord) :: rest := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_stack_pos_neg_sign state rest

theorem dispatchByte_supported_SMOD_byte_stack_neg_neg_sign
    (state : EvmState) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256)
      { state with stack := (-3 : EvmWord) :: (-2 : EvmWord) :: rest }).stack =
        (-1 : EvmWord) :: rest := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_stack_neg_neg_sign state rest

theorem dispatchByte_supported_SDIV_byte_stack_of_runSDivStack?_some
    {state : EvmState} {out : SDivStackExecutionBridge.SDivStackResult}
    (h_run :
      SDivStackExecutionBridge.runSDivStack? { stack := state.stack } =
        some out) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).stack =
        out.effects.stackWords ++ out.stack := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_stack_of_runSDivStack?_some
    h_run

theorem dispatchByte_supported_SMOD_byte_stack_of_runSModStack?_some
    {state : EvmState} {out : SModStackExecutionBridge.SModStackResult}
    (h_run :
      SModStackExecutionBridge.runSModStack? { stack := state.stack } =
        some out) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).stack =
        out.effects.stackWords ++ out.stack := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_stack_of_runSModStack?_some
    h_run

theorem dispatchByte_supported_SDIV_byte_status_of_runSDivStack?_some
    {state : EvmState} {out : SDivStackExecutionBridge.SDivStackResult}
    (h_run :
      SDivStackExecutionBridge.runSDivStack? { stack := state.stack } =
        some out) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).status =
        state.status := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_status_of_runSDivStack?_some
    h_run

theorem dispatchByte_supported_SMOD_byte_status_of_runSModStack?_some
    {state : EvmState} {out : SModStackExecutionBridge.SModStackResult}
    (h_run :
      SModStackExecutionBridge.runSModStack? { stack := state.stack } =
        some out) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).status =
        state.status := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_status_of_runSModStack?_some
    h_run

theorem dispatchByte_supported_SDIV_byte_status_empty_stack
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256)
      { state with stack := [] }).status = .error := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_status_empty_stack state

theorem dispatchByte_supported_SDIV_byte_status_singleton_stack
    (state : EvmState) (dividend : EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256)
      { state with stack := [dividend] }).status = .error := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_status_singleton_stack
    state dividend

theorem dispatchByte_supported_SMOD_byte_status_empty_stack
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256)
      { state with stack := [] }).status = .error := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_status_empty_stack state

theorem dispatchByte_supported_SMOD_byte_status_singleton_stack
    (state : EvmState) (dividend : EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256)
      { state with stack := [dividend] }).status = .error := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_status_singleton_stack
    state dividend

theorem dispatchByte_supported_SDIV_byte_status_of_runSDivStack?_none
    {state : EvmState}
    (h_run :
      SDivStackExecutionBridge.runSDivStack? { stack := state.stack } =
        none) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).status = .error := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_status_of_runSDivStack?_none
    h_run

theorem dispatchByte_supported_SMOD_byte_status_of_runSModStack?_none
    {state : EvmState}
    (h_run :
      SModStackExecutionBridge.runSModStack? { stack := state.stack } =
        none) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).status = .error := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_status_of_runSModStack?_none
    h_run

@[simp] theorem dispatchByte_supported_SDIV_byte_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : ArithmeticHandlers.binaryStack? EvmWord.sdiv state.stack =
      some stack') :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).status = state.status := by
  rw [dispatchByte_supported_SDIV_byte]
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
    h_stack, EvmState.withStack]

@[simp] theorem dispatchByte_supported_SMOD_byte_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack =
      some stack') :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).status = state.status := by
  rw [dispatchByte_supported_SMOD_byte]
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
    h_stack, EvmState.withStack]

theorem dispatchByte_supported_undecoded
    {b : Fin 256} (h_decode : EvmOpcode.decodeByte? b.val = none)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      state.invalid := by
  exact HandlerTable.dispatchByte_undecoded
    SupportedHandlers.supportedHandlerTable b state h_decode

theorem dispatchByte_supported_undecoded_status
    {b : Fin 256} (h_decode : EvmOpcode.decodeByte? b.val = none)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      .error := by
  exact HandlerTable.dispatchByte_undecoded_status
    SupportedHandlers.supportedHandlerTable b state h_decode

/--
Byte-level dispatch of any byte that decodes to STOP through the combined
supported-handler table executes the `state.stop` step. Generalises the
concrete `dispatchByte_supported_STOP_byte` (which is the `b = 0x00` instance).

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_STOP_of_decode #106 #107 #113.
-/
theorem dispatchByte_supported_STOP_of_decode
    {b : Fin 256}
    (h_decode : EvmOpcode.decodeByte? b.val = some .STOP)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      state.stop := by
  rw [dispatchByte_supported_of_lookup h_decode
    SupportedHandlers.supportedHandlerTable_STOP state]
  rfl

/-- Status projection of `dispatchByte_supported_STOP_of_decode`. -/
theorem dispatchByte_supported_STOP_of_decode_status
    {b : Fin 256}
    (h_decode : EvmOpcode.decodeByte? b.val = some .STOP)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      .stopped := by
  rw [dispatchByte_supported_STOP_of_decode h_decode state]
  exact EvmState.stop_status state

/--
Byte-level dispatch of any byte that decodes to INVALID through the combined
supported-handler table executes the `state.invalid` step. Generalises the
concrete `dispatchByte_supported_INVALID_byte` (which is the `b = 0xfe`
instance).

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_INVALID_of_decode #106 #107 #113.
-/
theorem dispatchByte_supported_INVALID_of_decode
    {b : Fin 256}
    (h_decode : EvmOpcode.decodeByte? b.val = some .INVALID)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      state.invalid := by
  rw [dispatchByte_supported_of_lookup h_decode
    SupportedHandlers.supportedHandlerTable_INVALID state]
  rfl

/-- Status projection of `dispatchByte_supported_INVALID_of_decode`. -/
theorem dispatchByte_supported_INVALID_of_decode_status
    {b : Fin 256}
    (h_decode : EvmOpcode.decodeByte? b.val = some .INVALID)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      .error := by
  rw [dispatchByte_supported_INVALID_of_decode h_decode state]
  exact EvmState.invalid_status state

end SupportedHandlerByte
end EvmAsm.Evm64
