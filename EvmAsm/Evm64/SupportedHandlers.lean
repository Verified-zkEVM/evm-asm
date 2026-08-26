/-
  EvmAsm.Evm64.SupportedHandlers

  Combined pure handler table for the currently shipped interpreter handler
  families (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTableCompose
public import EvmAsm.Evm64.TerminatingHandlers
public import EvmAsm.Evm64.StackHandlers
public import EvmAsm.Evm64.PushHandlers
public import EvmAsm.Evm64.ControlHandlers
public import EvmAsm.Evm64.EnvHandlers
public import EvmAsm.Evm64.ReturnDataHandlers
public import EvmAsm.Evm64.CodeHandlers
public import EvmAsm.Evm64.MemoryHandlers
public import EvmAsm.Evm64.ArithmeticHandlers
public import EvmAsm.Evm64.BitwiseHandlers
public import EvmAsm.Evm64.ComparisonHandlers
public import EvmAsm.Evm64.ShiftHandlers
public import EvmAsm.Evm64.CalldataHandlers
public import EvmAsm.Evm64.DupSwapHandlers

@[expose] public section

namespace EvmAsm.Evm64

namespace SupportedHandlers

/--
One left-biased table containing every pure handler family currently modeled
on `main` for the interpreter.

Distinctive token: SupportedHandlers.supportedHandlerTable #107.
-/
def supportedHandlerTable : HandlerTable :=
  HandlerTable.orElse TerminatingHandlers.terminatingHandlerTable <|
  HandlerTable.orElse StackHandlers.stackHandlerTable <|
  HandlerTable.orElse PushHandlers.pushHandlerTable <|
  HandlerTable.orElse ControlHandlers.controlHandlerTable <|
  HandlerTable.orElse EnvHandlers.simpleEnvHandlerTable <|
  HandlerTable.orElse ReturnDataHandlers.returnDataSizeHandlerTable <|
  HandlerTable.orElse CodeHandlers.codeHandlerTable <|
  HandlerTable.orElse MemoryHandlers.msizeHandlerTable <|
  HandlerTable.orElse ArithmeticHandlers.arithmeticHandlerTable <|
  HandlerTable.orElse BitwiseHandlers.bitwiseHandlerTable <|
  HandlerTable.orElse ComparisonHandlers.comparisonHandlerTable
    (HandlerTable.orElse ShiftHandlers.shiftHandlerTable
      (HandlerTable.orElse CalldataHandlers.calldataHandlerTable
        DupSwapHandlers.dupSwapHandlerTable))

theorem lookup_of_terminating
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup :
      TerminatingHandlers.terminatingHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_stack
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_lookup : StackHandlers.stackHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_control
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_lookup : ControlHandlers.controlHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_push
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_lookup : PushHandlers.pushHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_env
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_lookup : EnvHandlers.simpleEnvHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_arithmetic
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_returnData : ReturnDataHandlers.returnDataSizeHandlerTable opcode = none)
    (h_code : CodeHandlers.codeHandlerTable opcode = none)
    (h_memory : MemoryHandlers.msizeHandlerTable opcode = none)
    (h_lookup : ArithmeticHandlers.arithmeticHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  rw [HandlerTable.orElse_left_none h_returnData]
  rw [HandlerTable.orElse_left_none h_code]
  rw [HandlerTable.orElse_left_none h_memory]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_returnData
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_lookup : ReturnDataHandlers.returnDataSizeHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_code
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_returnData : ReturnDataHandlers.returnDataSizeHandlerTable opcode = none)
    (h_lookup : CodeHandlers.codeHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  rw [HandlerTable.orElse_left_none h_returnData]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_memory
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_returnData : ReturnDataHandlers.returnDataSizeHandlerTable opcode = none)
    (h_code : CodeHandlers.codeHandlerTable opcode = none)
    (h_lookup : MemoryHandlers.msizeHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  rw [HandlerTable.orElse_left_none h_returnData]
  rw [HandlerTable.orElse_left_none h_code]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_bitwise
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_returnData : ReturnDataHandlers.returnDataSizeHandlerTable opcode = none)
    (h_code : CodeHandlers.codeHandlerTable opcode = none)
    (h_memory : MemoryHandlers.msizeHandlerTable opcode = none)
    (h_arithmetic : ArithmeticHandlers.arithmeticHandlerTable opcode = none)
    (h_lookup : BitwiseHandlers.bitwiseHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  rw [HandlerTable.orElse_left_none h_returnData]
  rw [HandlerTable.orElse_left_none h_code]
  rw [HandlerTable.orElse_left_none h_memory]
  rw [HandlerTable.orElse_left_none h_arithmetic]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_comparison
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_returnData : ReturnDataHandlers.returnDataSizeHandlerTable opcode = none)
    (h_code : CodeHandlers.codeHandlerTable opcode = none)
    (h_memory : MemoryHandlers.msizeHandlerTable opcode = none)
    (h_arithmetic : ArithmeticHandlers.arithmeticHandlerTable opcode = none)
    (h_bitwise : BitwiseHandlers.bitwiseHandlerTable opcode = none)
    (h_lookup : ComparisonHandlers.comparisonHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  rw [HandlerTable.orElse_left_none h_returnData]
  rw [HandlerTable.orElse_left_none h_code]
  rw [HandlerTable.orElse_left_none h_memory]
  rw [HandlerTable.orElse_left_none h_arithmetic]
  rw [HandlerTable.orElse_left_none h_bitwise]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_shift
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_returnData : ReturnDataHandlers.returnDataSizeHandlerTable opcode = none)
    (h_code : CodeHandlers.codeHandlerTable opcode = none)
    (h_memory : MemoryHandlers.msizeHandlerTable opcode = none)
    (h_arithmetic : ArithmeticHandlers.arithmeticHandlerTable opcode = none)
    (h_bitwise : BitwiseHandlers.bitwiseHandlerTable opcode = none)
    (h_comparison : ComparisonHandlers.comparisonHandlerTable opcode = none)
    (h_lookup : ShiftHandlers.shiftHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  rw [HandlerTable.orElse_left_none h_returnData]
  rw [HandlerTable.orElse_left_none h_code]
  rw [HandlerTable.orElse_left_none h_memory]
  rw [HandlerTable.orElse_left_none h_arithmetic]
  rw [HandlerTable.orElse_left_none h_bitwise]
  rw [HandlerTable.orElse_left_none h_comparison]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_dupSwap
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_returnData : ReturnDataHandlers.returnDataSizeHandlerTable opcode = none)
    (h_code : CodeHandlers.codeHandlerTable opcode = none)
    (h_memory : MemoryHandlers.msizeHandlerTable opcode = none)
    (h_arithmetic : ArithmeticHandlers.arithmeticHandlerTable opcode = none)
    (h_bitwise : BitwiseHandlers.bitwiseHandlerTable opcode = none)
    (h_comparison : ComparisonHandlers.comparisonHandlerTable opcode = none)
    (h_shift : ShiftHandlers.shiftHandlerTable opcode = none)
    (h_calldata : CalldataHandlers.calldataHandlerTable opcode = none)
    (h_lookup : DupSwapHandlers.dupSwapHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  rw [HandlerTable.orElse_left_none h_returnData]
  rw [HandlerTable.orElse_left_none h_code]
  rw [HandlerTable.orElse_left_none h_memory]
  rw [HandlerTable.orElse_left_none h_arithmetic]
  rw [HandlerTable.orElse_left_none h_bitwise]
  rw [HandlerTable.orElse_left_none h_comparison]
  rw [HandlerTable.orElse_left_none h_shift]
  rw [HandlerTable.orElse_left_none h_calldata]
  exact h_lookup

theorem lookup_of_calldata
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_returnData : ReturnDataHandlers.returnDataSizeHandlerTable opcode = none)
    (h_code : CodeHandlers.codeHandlerTable opcode = none)
    (h_memory : MemoryHandlers.msizeHandlerTable opcode = none)
    (h_arithmetic : ArithmeticHandlers.arithmeticHandlerTable opcode = none)
    (h_bitwise : BitwiseHandlers.bitwiseHandlerTable opcode = none)
    (h_comparison : ComparisonHandlers.comparisonHandlerTable opcode = none)
    (h_shift : ShiftHandlers.shiftHandlerTable opcode = none)
    (h_lookup : CalldataHandlers.calldataHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  rw [HandlerTable.orElse_left_none h_returnData]
  rw [HandlerTable.orElse_left_none h_code]
  rw [HandlerTable.orElse_left_none h_memory]
  rw [HandlerTable.orElse_left_none h_arithmetic]
  rw [HandlerTable.orElse_left_none h_bitwise]
  rw [HandlerTable.orElse_left_none h_comparison]
  rw [HandlerTable.orElse_left_none h_shift]
  exact HandlerTable.orElse_left_some h_lookup

theorem dispatchOpcode?_of_lookup
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    HandlerTable.dispatchOpcode? supportedHandlerTable opcode state =
      some (handler state) :=
  HandlerTable.dispatchOpcode?_some h_lookup state

theorem dispatchOpcode_of_lookup
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    HandlerTable.dispatchOpcode supportedHandlerTable opcode state =
      handler state :=
  HandlerTable.dispatchOpcode_some h_lookup state

theorem dispatchOpcode_of_lookup_status
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchOpcode supportedHandlerTable opcode state).status =
      (handler state).status := by
  rw [dispatchOpcode_of_lookup h_lookup state]

theorem dispatchOpcode_of_lookup_pc
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchOpcode supportedHandlerTable opcode state).pc =
      (handler state).pc := by
  rw [dispatchOpcode_of_lookup h_lookup state]

theorem dispatchOpcode_of_lookup_gas
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchOpcode supportedHandlerTable opcode state).gas =
      (handler state).gas := by
  rw [dispatchOpcode_of_lookup h_lookup state]

theorem dispatchOpcode_of_lookup_stack
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchOpcode supportedHandlerTable opcode state).stack =
      (handler state).stack := by
  rw [dispatchOpcode_of_lookup h_lookup state]

theorem dispatchOpcode_of_lookup_memoryCells
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchOpcode supportedHandlerTable opcode state).memoryCells =
      (handler state).memoryCells := by
  rw [dispatchOpcode_of_lookup h_lookup state]

theorem dispatchOpcode_of_lookup_memory
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) (addr : Nat) :
    (HandlerTable.dispatchOpcode supportedHandlerTable opcode state).memory addr =
      (handler state).memory addr := by
  rw [dispatchOpcode_of_lookup h_lookup state]

theorem dispatchOpcode_of_lookup_memSize
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchOpcode supportedHandlerTable opcode state).memSize =
      (handler state).memSize := by
  rw [dispatchOpcode_of_lookup h_lookup state]

theorem dispatchOpcode_of_lookup_code
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchOpcode supportedHandlerTable opcode state).code =
      (handler state).code := by
  rw [dispatchOpcode_of_lookup h_lookup state]

theorem dispatchOpcode_of_lookup_codeLen
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchOpcode supportedHandlerTable opcode state).codeLen =
      (handler state).codeLen := by
  rw [dispatchOpcode_of_lookup h_lookup state]

theorem dispatchOpcode_of_lookup_preserves_codeLenMatches
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (h_codeLen : ∀ state : EvmState,
      state.codeLenMatches → (handler state).codeLenMatches)
    (state : EvmState) (h_state : state.codeLenMatches) :
    (HandlerTable.dispatchOpcode supportedHandlerTable opcode state).codeLenMatches := by
  rw [dispatchOpcode_of_lookup h_lookup state]
  exact h_codeLen state h_state

theorem dispatchOpcode_of_lookup_env
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchOpcode supportedHandlerTable opcode state).env =
      (handler state).env := by
  rw [dispatchOpcode_of_lookup h_lookup state]

@[simp] theorem supportedHandlerTable_STOP :
    supportedHandlerTable .STOP =
      some TerminatingHandlers.stopHandler := by
  exact lookup_of_terminating TerminatingHandlers.terminatingHandlerTable_STOP

@[simp] theorem supportedHandlerTable_INVALID :
    supportedHandlerTable .INVALID =
      some TerminatingHandlers.invalidHandler := by
  exact lookup_of_terminating TerminatingHandlers.terminatingHandlerTable_INVALID

@[simp] theorem supportedHandlerTable_PUSH0 :
    supportedHandlerTable .PUSH0 =
      some StackHandlers.push0Handler := by
  exact lookup_of_stack
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    StackHandlers.stackHandlerTable_PUSH0

@[simp] theorem supportedHandlerTable_POP :
    supportedHandlerTable .POP =
      some StackHandlers.popHandler := by
  exact lookup_of_stack
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    StackHandlers.stackHandlerTable_POP

@[simp] theorem supportedHandlerTable_PC :
    supportedHandlerTable .PC =
      some ControlHandlers.pcHandler := by
  exact lookup_of_control
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    ControlHandlers.controlHandlerTable_PC

@[simp] theorem supportedHandlerTable_GAS :
    supportedHandlerTable .GAS =
      some ControlHandlers.gasHandler := by
  exact lookup_of_control
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    ControlHandlers.controlHandlerTable_GAS

@[simp] theorem supportedHandlerTable_JUMPDEST :
    supportedHandlerTable .JUMPDEST =
      some ControlHandlers.jumpdestHandler := by
  exact lookup_of_control
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    ControlHandlers.controlHandlerTable_JUMPDEST

@[simp] theorem supportedHandlerTable_RETURNDATASIZE :
    supportedHandlerTable .RETURNDATASIZE =
      some ReturnDataHandlers.returnDataSizeHandler := by
  exact lookup_of_returnData
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    (by simp [ControlHandlers.controlHandlerTable, ControlHandlers.controlHandler?])
    (by rfl)
    ReturnDataHandlers.returnDataSizeHandlerTable_RETURNDATASIZE

@[simp] theorem supportedHandlerTable_CODESIZE :
    supportedHandlerTable .CODESIZE =
      some CodeHandlers.codeSizeHandler := by
  exact lookup_of_code
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    (by simp [ControlHandlers.controlHandlerTable, ControlHandlers.controlHandler?])
    (by rfl)
    (by simp [ReturnDataHandlers.returnDataSizeHandlerTable,
      ReturnDataHandlers.returnDataHandler?])
    CodeHandlers.codeHandlerTable_CODESIZE

@[simp] theorem supportedHandlerTable_MSIZE :
    supportedHandlerTable .MSIZE =
      some MemoryHandlers.msizeHandler := by
  exact lookup_of_memory
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    (by simp [ControlHandlers.controlHandlerTable, ControlHandlers.controlHandler?])
    (by rfl)
    (by simp [ReturnDataHandlers.returnDataSizeHandlerTable,
      ReturnDataHandlers.returnDataHandler?])
    (by simp [CodeHandlers.codeHandlerTable, CodeHandlers.codeHandler?])
    MemoryHandlers.msizeHandlerTable_MSIZE

@[simp] theorem supportedHandlerTable_SDIV :
    supportedHandlerTable .SDIV =
      some ArithmeticHandlers.sdivHandler := by
  exact lookup_of_arithmetic
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    (by simp [ControlHandlers.controlHandlerTable, ControlHandlers.controlHandler?])
    (by rfl)
    (by simp [ReturnDataHandlers.returnDataSizeHandlerTable,
      ReturnDataHandlers.returnDataHandler?])
    (by simp [CodeHandlers.codeHandlerTable, CodeHandlers.codeHandler?])
    (by simp [MemoryHandlers.msizeHandlerTable, MemoryHandlers.memoryHandler?])
    ArithmeticHandlers.arithmeticHandler?_SDIV

@[simp] theorem supportedHandlerTable_SMOD :
    supportedHandlerTable .SMOD =
      some ArithmeticHandlers.smodHandler := by
  exact lookup_of_arithmetic
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    (by simp [ControlHandlers.controlHandlerTable, ControlHandlers.controlHandler?])
    (by rfl)
    (by simp [ReturnDataHandlers.returnDataSizeHandlerTable,
      ReturnDataHandlers.returnDataHandler?])
    (by simp [CodeHandlers.codeHandlerTable, CodeHandlers.codeHandler?])
    (by simp [MemoryHandlers.msizeHandlerTable, MemoryHandlers.memoryHandler?])
    ArithmeticHandlers.arithmeticHandler?_SMOD

@[simp] theorem supportedHandlerTable_CALLDATASIZE :
    supportedHandlerTable .CALLDATASIZE =
      some CalldataHandlers.callDataSizeHandler := by
  exact lookup_of_calldata
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    (by simp [ControlHandlers.controlHandlerTable, ControlHandlers.controlHandler?])
    (by rfl)
    (by simp [ReturnDataHandlers.returnDataSizeHandlerTable,
      ReturnDataHandlers.returnDataHandler?])
    (by simp [CodeHandlers.codeHandlerTable, CodeHandlers.codeHandler?])
    (by simp [MemoryHandlers.msizeHandlerTable, MemoryHandlers.memoryHandler?])
    (by simp [ArithmeticHandlers.arithmeticHandlerTable,
      ArithmeticHandlers.arithmeticHandler?])
    (by simp [BitwiseHandlers.bitwiseHandlerTable, BitwiseHandlers.bitwiseHandler?])
    (by simp [ComparisonHandlers.comparisonHandlerTable,
      ComparisonHandlers.comparisonHandler?])
    (by simp [ShiftHandlers.shiftHandlerTable, ShiftHandlers.shiftHandler?])
    CalldataHandlers.calldataHandlerTable_CALLDATASIZE

theorem supportedHandlerTable_PUSH_of_valid
    {n : Nat} (h_valid : EvmOpcode.validPushWidth n = true) :
    supportedHandlerTable (.PUSH n) =
      some (PushHandlers.pushHandler n) := by
  exact lookup_of_push
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (PushHandlers.pushHandler?_PUSH_of_valid h_valid)

/--
Dispatching a valid PUSH opcode through the combined supported-handler table
has the same program-counter and stack effect as the executable PUSH bridge.

Distinctive token:
SupportedHandlers.dispatchOpcode_supportedHandlerTable_PUSH_effectFromCode
#101 #107.
-/
theorem dispatchOpcode_supportedHandlerTable_PUSH_effectFromCode
    {n : Nat} (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    (HandlerTable.dispatchOpcode supportedHandlerTable (.PUSH n) state).pc =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).pc ∧
      (HandlerTable.dispatchOpcode supportedHandlerTable (.PUSH n) state).stack =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).stack := by
  rw [HandlerTable.dispatchOpcode_some
    (supportedHandlerTable_PUSH_of_valid h_valid) state]
  exact PushHandlers.pushHandler_eq_effectFromCode n state

theorem dispatchOpcode_supportedHandlerTable_PUSH_of_valid_status
    {n : Nat} (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    (HandlerTable.dispatchOpcode supportedHandlerTable (.PUSH n) state).status =
      state.status := by
  rw [HandlerTable.dispatchOpcode_some
    (supportedHandlerTable_PUSH_of_valid h_valid) state]
  exact PushHandlers.pushHandler_status n state

theorem supportedHandlerTable_DUP_of_valid
    {n : Nat} (h_valid : EvmOpcode.validDupIndex n = true) :
    supportedHandlerTable (.DUP n) =
      some (DupSwapHandlers.dupHandler n) := by
  exact lookup_of_dupSwap
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    (by simp [ControlHandlers.controlHandlerTable, ControlHandlers.controlHandler?])
    (by rfl)
    (by simp [ReturnDataHandlers.returnDataSizeHandlerTable,
      ReturnDataHandlers.returnDataHandler?])
    (by simp [CodeHandlers.codeHandlerTable, CodeHandlers.codeHandler?])
    (by simp [MemoryHandlers.msizeHandlerTable, MemoryHandlers.memoryHandler?])
    (by simp [ArithmeticHandlers.arithmeticHandlerTable,
      ArithmeticHandlers.arithmeticHandler?])
    (by simp [BitwiseHandlers.bitwiseHandlerTable, BitwiseHandlers.bitwiseHandler?])
    (by simp [ComparisonHandlers.comparisonHandlerTable,
      ComparisonHandlers.comparisonHandler?])
    (by simp [ShiftHandlers.shiftHandlerTable, ShiftHandlers.shiftHandler?])
    (by simp [CalldataHandlers.calldataHandlerTable,
      CalldataHandlers.calldataHandler?])
    (DupSwapHandlers.dupSwapHandler?_DUP_of_valid h_valid)

theorem supportedHandlerTable_SWAP_of_valid
    {n : Nat} (h_valid : EvmOpcode.validSwapIndex n = true) :
    supportedHandlerTable (.SWAP n) =
      some (DupSwapHandlers.swapHandler n) := by
  exact lookup_of_dupSwap
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    (by simp [ControlHandlers.controlHandlerTable, ControlHandlers.controlHandler?])
    (by rfl)
    (by simp [ReturnDataHandlers.returnDataSizeHandlerTable,
      ReturnDataHandlers.returnDataHandler?])
    (by simp [CodeHandlers.codeHandlerTable, CodeHandlers.codeHandler?])
    (by simp [MemoryHandlers.msizeHandlerTable, MemoryHandlers.memoryHandler?])
    (by simp [ArithmeticHandlers.arithmeticHandlerTable,
      ArithmeticHandlers.arithmeticHandler?])
    (by simp [BitwiseHandlers.bitwiseHandlerTable, BitwiseHandlers.bitwiseHandler?])
    (by simp [ComparisonHandlers.comparisonHandlerTable,
      ComparisonHandlers.comparisonHandler?])
    (by simp [ShiftHandlers.shiftHandlerTable, ShiftHandlers.shiftHandler?])
    (by simp [CalldataHandlers.calldataHandlerTable,
      CalldataHandlers.calldataHandler?])
    (DupSwapHandlers.dupSwapHandler?_SWAP_of_valid h_valid)

theorem dispatchOpcode_supportedHandlerTable_DUP_of_valid_status_of_some
    {n : Nat} (h_valid : EvmOpcode.validDupIndex n = true)
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : DupSwapHandlers.dupStack? n state.stack = some stack') :
    (HandlerTable.dispatchOpcode supportedHandlerTable (.DUP n) state).status =
      state.status := by
  rw [HandlerTable.dispatchOpcode_some
    (supportedHandlerTable_DUP_of_valid h_valid) state]
  simp [DupSwapHandlers.dupHandler, h_stack, EvmState.withStack]

theorem dispatchOpcode_supportedHandlerTable_SWAP_of_valid_status_of_some
    {n : Nat} (h_valid : EvmOpcode.validSwapIndex n = true)
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : DupSwapHandlers.swapStack? n state.stack = some stack') :
    (HandlerTable.dispatchOpcode supportedHandlerTable (.SWAP n) state).status =
      state.status := by
  rw [HandlerTable.dispatchOpcode_some
    (supportedHandlerTable_SWAP_of_valid h_valid) state]
  simp [DupSwapHandlers.swapHandler, h_stack, EvmState.withStack]

end SupportedHandlers

end EvmAsm.Evm64
