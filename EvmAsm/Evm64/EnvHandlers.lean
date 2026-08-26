/-
  EvmAsm.Evm64.EnvHandlers

  Generic pure handler-table entries for simple environment opcodes (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable
public import EvmAsm.Evm64.Env.Gas

@[expose] public section

namespace EvmAsm.Evm64
namespace EnvHandlers

abbrev SimpleEnvField := Env.SimpleEnvField

/-- Decode handler-table opcodes back to the simple environment field surface. -/
def fieldOfOpcode? : EvmOpcode → Option SimpleEnvField
  | .ADDRESS => some .address
  | .ORIGIN => some .origin
  | .CALLER => some .caller
  | .CALLVALUE => some .callValue
  | .GASPRICE => some .gasPrice
  | .COINBASE => some .coinbase
  | .TIMESTAMP => some .timestamp
  | .NUMBER => some .number
  | .PREVRANDAO => some .prevrandao
  | .GASLIMIT => some .gasLimit
  | .CHAINID => some .chainId
  | .SELFBALANCE => some .selfBalance
  | .BASEFEE => some .baseFee
  | _ => none

/-- Pure simple-environment handler. It pushes the field value exposed by the
    executable environment spec; gas/pc charging belongs to later wrappers. -/
def simpleEnvHandler (field : SimpleEnvField) : OpcodeHandler :=
  fun state => state.withStack (field.value state.env :: state.stack)

/-- Lookup surface for simple environment opcode handlers. -/
def simpleEnvHandler? (opcode : EvmOpcode) : Option OpcodeHandler :=
  match fieldOfOpcode? opcode with
  | some field => some (simpleEnvHandler field)
  | none => none

theorem simpleEnvHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    simpleEnvHandler? opcode = some handler ↔
      ∃ field, fieldOfOpcode? opcode = some field ∧
        handler = simpleEnvHandler field := by
  constructor
  · intro h_handler
    unfold simpleEnvHandler? at h_handler
    cases h_field : fieldOfOpcode? opcode with
    | none =>
        simp [h_field] at h_handler
    | some field =>
        simp [h_field] at h_handler
        exact ⟨field, rfl, h_handler.symm⟩
  · rintro ⟨field, h_field, rfl⟩
    simp [simpleEnvHandler?, h_field]

theorem simpleEnvHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    simpleEnvHandler? opcode = none ↔ fieldOfOpcode? opcode = none := by
  unfold simpleEnvHandler?
  cases h_field : fieldOfOpcode? opcode with
  | none =>
      simp
  | some field =>
      simp

/-- Handler table containing the generic simple environment opcode entries.
    Distinctive token: EnvHandlers.simpleEnvHandlerTable #107. -/
def simpleEnvHandlerTable : HandlerTable :=
  simpleEnvHandler?

@[simp] theorem simpleEnvHandler_stack
    (field : SimpleEnvField) (state : EvmState) :
    (simpleEnvHandler field state).stack =
      field.value state.env :: state.stack := rfl

@[simp] theorem simpleEnvHandler_status
    (field : SimpleEnvField) (state : EvmState) :
    (simpleEnvHandler field state).status = state.status := rfl

@[simp] theorem simpleEnvHandler_env
    (field : SimpleEnvField) (state : EvmState) :
    (simpleEnvHandler field state).env = state.env := rfl

@[simp] theorem simpleEnvHandlerTable_eq :
    simpleEnvHandlerTable = simpleEnvHandler? := rfl

theorem fieldOfOpcode?_of_field (field : SimpleEnvField) :
    fieldOfOpcode? field.opcode = some field := by
  cases field <;> rfl

theorem simpleEnvHandler?_of_field (field : SimpleEnvField) :
    simpleEnvHandler? field.opcode = some (simpleEnvHandler field) := by
  simp [simpleEnvHandler?, fieldOfOpcode?_of_field]

theorem dispatchOpcode?_simpleEnvHandlerTable_of_field
    (field : SimpleEnvField) (state : EvmState) :
    HandlerTable.dispatchOpcode? simpleEnvHandlerTable field.opcode state =
      some (simpleEnvHandler field state) := by
  exact HandlerTable.dispatchOpcode?_some
    (simpleEnvHandler?_of_field field) state

theorem dispatchOpcode_simpleEnvHandlerTable_of_field
    (field : SimpleEnvField) (state : EvmState) :
    HandlerTable.dispatchOpcode simpleEnvHandlerTable field.opcode state =
      simpleEnvHandler field state := by
  exact HandlerTable.dispatchOpcode_some
    (simpleEnvHandler?_of_field field) state

theorem dispatchOpcode_simpleEnvHandlerTable_of_field_status
    (field : SimpleEnvField) (state : EvmState) :
    (HandlerTable.dispatchOpcode simpleEnvHandlerTable field.opcode state).status =
      state.status := by
  rw [dispatchOpcode_simpleEnvHandlerTable_of_field field state]
  exact simpleEnvHandler_status field state

@[simp] theorem fieldOfOpcode?_ADDRESS :
    fieldOfOpcode? .ADDRESS = some .address := rfl

@[simp] theorem fieldOfOpcode?_ORIGIN :
    fieldOfOpcode? .ORIGIN = some .origin := rfl

@[simp] theorem fieldOfOpcode?_CALLER :
    fieldOfOpcode? .CALLER = some .caller := rfl

@[simp] theorem fieldOfOpcode?_CALLVALUE :
    fieldOfOpcode? .CALLVALUE = some .callValue := rfl

@[simp] theorem fieldOfOpcode?_SELFBALANCE :
    fieldOfOpcode? .SELFBALANCE = some .selfBalance := rfl

theorem dispatchOpcode_simpleEnvHandlerTable_ADDRESS
    (state : EvmState) :
    HandlerTable.dispatchOpcode simpleEnvHandlerTable .ADDRESS state =
      simpleEnvHandler .address state :=
  dispatchOpcode_simpleEnvHandlerTable_of_field .address state

theorem dispatchOpcode_simpleEnvHandlerTable_ORIGIN
    (state : EvmState) :
    HandlerTable.dispatchOpcode simpleEnvHandlerTable .ORIGIN state =
      simpleEnvHandler .origin state :=
  dispatchOpcode_simpleEnvHandlerTable_of_field .origin state

theorem dispatchOpcode_simpleEnvHandlerTable_CALLER
    (state : EvmState) :
    HandlerTable.dispatchOpcode simpleEnvHandlerTable .CALLER state =
      simpleEnvHandler .caller state :=
  dispatchOpcode_simpleEnvHandlerTable_of_field .caller state

theorem dispatchOpcode_simpleEnvHandlerTable_CALLVALUE
    (state : EvmState) :
    HandlerTable.dispatchOpcode simpleEnvHandlerTable .CALLVALUE state =
      simpleEnvHandler .callValue state :=
  dispatchOpcode_simpleEnvHandlerTable_of_field .callValue state

end EnvHandlers
end EvmAsm.Evm64
