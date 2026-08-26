/-
  EvmAsm.Evm64.TerminatingHandlers

  Pure handler-table entries for terminating opcodes (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable

@[expose] public section

namespace EvmAsm.Evm64
namespace TerminatingHandlers

/-- STOP handler: terminate successfully without returndata. -/
def stopHandler : OpcodeHandler :=
  fun state => state.stop

/-- INVALID handler: terminate with an error status. -/
def invalidHandler : OpcodeHandler :=
  fun state => state.invalid

/-- Lookup surface for terminating opcodes that already need no additional
    stack or memory arguments. RETURN/REVERT/SELFDESTRUCT need separate
    argument bridges, so this first table only installs STOP and INVALID. -/
def terminatingHandler? : EvmOpcode → Option OpcodeHandler
  | .STOP => some stopHandler
  | .INVALID => some invalidHandler
  | _ => none

/-- Handler table containing the currently argument-free terminating handlers. -/
def terminatingHandlerTable : HandlerTable :=
  HandlerTable.setHandler
    (HandlerTable.setHandler HandlerTable.empty .STOP stopHandler)
    .INVALID invalidHandler

@[simp] theorem terminatingHandler?_STOP :
    terminatingHandler? .STOP = some stopHandler := rfl

@[simp] theorem terminatingHandler?_INVALID :
    terminatingHandler? .INVALID = some invalidHandler := rfl

@[simp] theorem eq_stopHandler_iff (handler : OpcodeHandler) :
    stopHandler = handler ↔ handler = stopHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm

@[simp] theorem eq_invalidHandler_iff (handler : OpcodeHandler) :
    invalidHandler = handler ↔ handler = invalidHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm

theorem terminatingHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    terminatingHandler? opcode = some handler ↔
      (opcode = .STOP ∧ handler = stopHandler) ∨
        (opcode = .INVALID ∧ handler = invalidHandler) := by
  cases opcode <;> simp [terminatingHandler?]

theorem terminatingHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    terminatingHandler? opcode = none ↔
      opcode ≠ .STOP ∧ opcode ≠ .INVALID := by
  cases opcode <;> simp [terminatingHandler?]

@[simp] theorem stopHandler_status (state : EvmState) :
    (stopHandler state).status = .stopped := rfl

@[simp] theorem invalidHandler_status (state : EvmState) :
    (invalidHandler state).status = .error := rfl

@[simp] theorem terminatingHandlerTable_STOP :
    terminatingHandlerTable .STOP = some stopHandler := by
  simp [terminatingHandlerTable, HandlerTable.setHandler]

@[simp] theorem terminatingHandlerTable_INVALID :
    terminatingHandlerTable .INVALID = some invalidHandler := by
  simp [terminatingHandlerTable, HandlerTable.setHandler]

@[simp] theorem dispatchOpcode?_terminatingHandlerTable_STOP
    (state : EvmState) :
    HandlerTable.dispatchOpcode? terminatingHandlerTable .STOP state =
      some (state.stop) := by
  simp [HandlerTable.dispatchOpcode?, stopHandler]

@[simp] theorem dispatchOpcode_terminatingHandlerTable_STOP
    (state : EvmState) :
    HandlerTable.dispatchOpcode terminatingHandlerTable .STOP state =
      state.stop := by
  simp [HandlerTable.dispatchOpcode]

@[simp] theorem dispatchOpcode?_terminatingHandlerTable_INVALID
    (state : EvmState) :
    HandlerTable.dispatchOpcode? terminatingHandlerTable .INVALID state =
      some (state.invalid) := by
  simp [HandlerTable.dispatchOpcode?, invalidHandler]

@[simp] theorem dispatchOpcode_terminatingHandlerTable_INVALID
    (state : EvmState) :
    HandlerTable.dispatchOpcode terminatingHandlerTable .INVALID state =
      state.invalid := by
  simp [HandlerTable.dispatchOpcode]

@[simp] theorem dispatchOpcode_terminatingHandlerTable_STOP_status
    (state : EvmState) :
    (HandlerTable.dispatchOpcode terminatingHandlerTable .STOP state).status =
      .stopped := by
  simp

@[simp] theorem dispatchOpcode_terminatingHandlerTable_INVALID_status
    (state : EvmState) :
    (HandlerTable.dispatchOpcode terminatingHandlerTable .INVALID state).status =
      .error := by
  simp

end TerminatingHandlers
end EvmAsm.Evm64
