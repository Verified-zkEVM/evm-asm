/-
  EvmAsm.Evm64.ReturnDataHandlers

  Pure RETURNDATASIZE handler-table entry for the interpreter handler layer
  (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable

@[expose] public section

namespace EvmAsm.Evm64

namespace ReturnDataHandlers

/-- EVM word pushed by RETURNDATASIZE for the current abstract state. -/
def returnDataSizeWord (state : EvmState) : EvmWord :=
  BitVec.ofNat 256 state.env.returnDataSize.toNat

/-- RETURNDATASIZE pushes the current returndata buffer length in bytes. -/
def returnDataSizeHandler : OpcodeHandler :=
  fun state => state.withStack (returnDataSizeWord state :: state.stack)

/-- Lookup just the returndata handler introduced in this slice. -/
def returnDataHandler? : EvmOpcode → Option OpcodeHandler
  | .RETURNDATASIZE => some returnDataSizeHandler
  | _ => none

/-- Handler table fragment containing the RETURNDATASIZE entry.
    Distinctive token: ReturnDataHandlers.returnDataSizeHandlerTable #107. -/
def returnDataSizeHandlerTable : HandlerTable :=
  returnDataHandler?

@[simp] theorem returnDataHandler?_RETURNDATASIZE :
    returnDataHandler? .RETURNDATASIZE = some returnDataSizeHandler := rfl

@[simp] theorem eq_returnDataSizeHandler_iff (handler : OpcodeHandler) :
    returnDataSizeHandler = handler ↔ handler = returnDataSizeHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm

theorem returnDataHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    returnDataHandler? opcode = some handler ↔
      opcode = .RETURNDATASIZE ∧ handler = returnDataSizeHandler := by
  cases opcode <;> simp [returnDataHandler?]

theorem returnDataHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    returnDataHandler? opcode = none ↔ opcode ≠ .RETURNDATASIZE := by
  cases opcode <;> simp [returnDataHandler?]

@[simp] theorem returnDataSizeHandler_stack (state : EvmState) :
    (returnDataSizeHandler state).stack =
      returnDataSizeWord state :: state.stack := rfl

@[simp] theorem returnDataSizeHandler_status (state : EvmState) :
    (returnDataSizeHandler state).status = state.status := rfl

@[simp] theorem returnDataSizeHandler_env (state : EvmState) :
    (returnDataSizeHandler state).env = state.env := rfl

@[simp] theorem returnDataSizeHandlerTable_RETURNDATASIZE :
    returnDataSizeHandlerTable .RETURNDATASIZE =
      some returnDataSizeHandler := rfl

@[simp] theorem dispatchOpcode?_returnDataSizeHandlerTable_RETURNDATASIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode? returnDataSizeHandlerTable .RETURNDATASIZE state =
      some (returnDataSizeHandler state) := by
  simp [HandlerTable.dispatchOpcode?]

@[simp] theorem dispatchOpcode_returnDataSizeHandlerTable_RETURNDATASIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode returnDataSizeHandlerTable .RETURNDATASIZE state =
      returnDataSizeHandler state := by
  simp [HandlerTable.dispatchOpcode]

theorem dispatchOpcode_returnDataSizeHandlerTable_RETURNDATASIZE_status
    (state : EvmState) :
    (HandlerTable.dispatchOpcode returnDataSizeHandlerTable .RETURNDATASIZE state).status =
      state.status := by
  rw [dispatchOpcode_returnDataSizeHandlerTable_RETURNDATASIZE state]
  exact returnDataSizeHandler_status state

end ReturnDataHandlers

end EvmAsm.Evm64
