/-
  EvmAsm.Evm64.CalldataHandlers

  Pure handler-table entries for calldata opcodes currently exposed by
  `EvmState` (GH #104 / GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable
public import EvmAsm.Evm64.Calldata.Size

@[expose] public section

namespace EvmAsm.Evm64
namespace CalldataHandlers

/-- Pure CALLDATASIZE handler. The interpreter state already carries the
    calldata length in `env.callDataLen`; gas and PC charging belong to later
    wrapper layers. -/
def callDataSizeHandler : OpcodeHandler :=
  fun state =>
    state.withStack
      (Calldata.callDataSizeWord state.env.callDataLen.toNat :: state.stack)

/-- Lookup surface for calldata opcode handlers currently supported at the
    pure `EvmState` level. Distinctive token:
    CalldataHandlers.callDataSizeHandlerTable #104 #107. -/
def calldataHandler? : EvmOpcode → Option OpcodeHandler
  | .CALLDATASIZE => some callDataSizeHandler
  | _ => none

/-- Handler table containing currently supported calldata opcode entries. -/
def calldataHandlerTable : HandlerTable :=
  calldataHandler?

@[simp] theorem callDataSizeHandler_stack (state : EvmState) :
    (callDataSizeHandler state).stack =
      Calldata.callDataSizeWord state.env.callDataLen.toNat :: state.stack := rfl

@[simp] theorem callDataSizeHandler_status (state : EvmState) :
    (callDataSizeHandler state).status = state.status := rfl

@[simp] theorem callDataSizeHandler_env (state : EvmState) :
    (callDataSizeHandler state).env = state.env := rfl

@[simp] theorem calldataHandlerTable_eq :
    calldataHandlerTable = calldataHandler? := rfl

@[simp] theorem calldataHandler?_CALLDATASIZE :
    calldataHandler? .CALLDATASIZE = some callDataSizeHandler := rfl

@[simp] theorem eq_callDataSizeHandler_iff (handler : OpcodeHandler) :
    callDataSizeHandler = handler ↔ handler = callDataSizeHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm

theorem calldataHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    calldataHandler? opcode = some handler ↔
      opcode = .CALLDATASIZE ∧ handler = callDataSizeHandler := by
  cases opcode <;> simp [calldataHandler?]

theorem calldataHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    calldataHandler? opcode = none ↔ opcode ≠ .CALLDATASIZE := by
  cases opcode <;> simp [calldataHandler?]

@[simp] theorem calldataHandlerTable_CALLDATASIZE :
    calldataHandlerTable .CALLDATASIZE = some callDataSizeHandler := rfl

theorem dispatchOpcode?_calldataHandlerTable_CALLDATASIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode? calldataHandlerTable .CALLDATASIZE state =
      some (callDataSizeHandler state) := by
  exact HandlerTable.dispatchOpcode?_some
    calldataHandlerTable_CALLDATASIZE state

theorem dispatchOpcode_calldataHandlerTable_CALLDATASIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode calldataHandlerTable .CALLDATASIZE state =
      callDataSizeHandler state := by
  exact HandlerTable.dispatchOpcode_some
    calldataHandlerTable_CALLDATASIZE state

theorem dispatchOpcode_calldataHandlerTable_CALLDATASIZE_status
    (state : EvmState) :
    (HandlerTable.dispatchOpcode calldataHandlerTable .CALLDATASIZE state).status =
      state.status := by
  rw [dispatchOpcode_calldataHandlerTable_CALLDATASIZE state]
  exact callDataSizeHandler_status state

end CalldataHandlers
end EvmAsm.Evm64
