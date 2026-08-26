/-
  EvmAsm.Evm64.HandlerLoopBridge

  Adapter from handler tables to the pure interpreter loop (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable
public import EvmAsm.Evm64.InterpreterSimulation

@[expose] public section

namespace EvmAsm.Evm64

namespace HandlerLoopBridge

/--
Adapt a partial opcode handler table to the total handler expected by
`InterpreterLoop.stepWithHandler`.

Distinctive token: HandlerLoopBridge.toLoopHandler #107.
-/
def toLoopHandler (table : HandlerTable) : InterpreterLoop.Handler :=
  fun opcode state => HandlerTable.dispatchOpcode table opcode state

@[simp] theorem toLoopHandler_apply
    (table : HandlerTable) (opcode : EvmOpcode) (state : EvmState) :
    toLoopHandler table opcode state =
      HandlerTable.dispatchOpcode table opcode state := rfl

theorem stepWithTableHandler_of_decode
    (table : HandlerTable) {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    InterpreterLoop.stepWithHandler (toLoopHandler table) state =
      HandlerTable.dispatchOpcode table opcode state := by
  simp [InterpreterLoop.stepWithHandler, h_decode, toLoopHandler]

theorem stepWithTableHandler_of_lookup
    {table : HandlerTable} {state : EvmState} {opcode : EvmOpcode}
    {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : table opcode = some handler) :
    InterpreterLoop.stepWithHandler (toLoopHandler table) state = handler state := by
  rw [stepWithTableHandler_of_decode table h_decode]
  exact HandlerTable.dispatchOpcode_some h_lookup state

theorem stepWithTableHandler_of_decode_status
    (table : HandlerTable) {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    (InterpreterLoop.stepWithHandler (toLoopHandler table) state).status =
      (HandlerTable.dispatchOpcode table opcode state).status := by
  rw [stepWithTableHandler_of_decode table h_decode]

theorem stepWithTableHandler_of_lookup_status
    {table : HandlerTable} {state : EvmState} {opcode : EvmOpcode}
    {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : table opcode = some handler) :
    (InterpreterLoop.stepWithHandler (toLoopHandler table) state).status =
      (handler state).status := by
  rw [stepWithTableHandler_of_lookup h_decode h_lookup]

theorem stepWithTableHandler_of_lookup_preserves_status
    {table : HandlerTable} {state : EvmState} {opcode : EvmOpcode}
    {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : table opcode = some handler)
    (h_status : ∀ state : EvmState, (handler state).status = state.status) :
    (InterpreterLoop.stepWithHandler (toLoopHandler table) state).status =
      state.status := by
  rw [stepWithTableHandler_of_lookup_status h_decode h_lookup]
  exact h_status state

theorem stepWithTableHandler_of_lookup_preserves_codeLenMatches
    {table : HandlerTable} {state : EvmState} {opcode : EvmOpcode}
    {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : table opcode = some handler)
    (h_codeLen : ∀ state : EvmState,
      state.codeLenMatches → (handler state).codeLenMatches)
    (h_state : state.codeLenMatches) :
    (InterpreterLoop.stepWithHandler (toLoopHandler table) state).codeLenMatches := by
  rw [stepWithTableHandler_of_lookup h_decode h_lookup]
  exact h_codeLen state h_state

theorem stepWithTableHandler_missing_invalid
    {table : HandlerTable} {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : table opcode = none) :
    InterpreterLoop.stepWithHandler (toLoopHandler table) state = state.invalid := by
  rw [stepWithTableHandler_of_decode table h_decode]
  exact HandlerTable.dispatchOpcode_none h_lookup state

theorem stepWithTableHandler_missing_invalid_status
    {table : HandlerTable} {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : table opcode = none) :
    (InterpreterLoop.stepWithHandler (toLoopHandler table) state).status =
      .error := by
  rw [stepWithTableHandler_missing_invalid h_decode h_lookup]
  exact EvmState.invalid_status state

theorem stepWithTableHandler_empty_of_decode
    {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    InterpreterLoop.stepWithHandler (toLoopHandler HandlerTable.empty) state =
      state.invalid := by
  exact stepWithTableHandler_missing_invalid h_decode (HandlerTable.empty_apply opcode)

theorem stepWithTableHandler_empty_of_decode_status
    {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    (InterpreterLoop.stepWithHandler (toLoopHandler HandlerTable.empty) state).status =
      .error := by
  rw [stepWithTableHandler_empty_of_decode h_decode]
  exact EvmState.invalid_status state

theorem stepWithTableHandler_eof_invalid
    (table : HandlerTable) {state : EvmState}
    (h_pc : state.code.length ≤ state.pc) :
    InterpreterLoop.stepWithHandler (toLoopHandler table) state = state.invalid := by
  exact InterpreterLoop.stepWithHandler_eof_invalid (toLoopHandler table) h_pc

theorem stepWithTableHandler_eof_invalid_status
    (table : HandlerTable) {state : EvmState}
    (h_pc : state.code.length ≤ state.pc) :
    (InterpreterLoop.stepWithHandler (toLoopHandler table) state).status = .error := by
  rw [stepWithTableHandler_eof_invalid table h_pc]
  exact EvmState.invalid_status state

theorem loopFuel_succ_running_decode
    (table : HandlerTable) (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    InterpreterLoop.loopFuel (toLoopHandler table) (nSteps + 1) state =
      InterpreterLoop.loopFuel (toLoopHandler table) nSteps
        (HandlerTable.dispatchOpcode table opcode state) := by
  rw [InterpreterLoop.loopFuel_succ_running (toLoopHandler table) nSteps state h_status]
  rw [stepWithTableHandler_of_decode table h_decode]

theorem loopFuel_succ_running_decode_status
    (table : HandlerTable) (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    (InterpreterLoop.loopFuel (toLoopHandler table) (nSteps + 1) state).status =
      (InterpreterLoop.loopFuel (toLoopHandler table) nSteps
        (HandlerTable.dispatchOpcode table opcode state)).status := by
  rw [loopFuel_succ_running_decode table nSteps h_status h_decode]

theorem loopFuel_succ_running_lookup
    {table : HandlerTable} (nSteps : Nat) {state : EvmState}
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : table opcode = some handler) :
    InterpreterLoop.loopFuel (toLoopHandler table) (nSteps + 1) state =
      InterpreterLoop.loopFuel (toLoopHandler table) nSteps (handler state) := by
  rw [loopFuel_succ_running_decode table nSteps h_status h_decode]
  rw [HandlerTable.dispatchOpcode_some h_lookup state]

theorem loopFuel_succ_running_lookup_status
    {table : HandlerTable} (nSteps : Nat) {state : EvmState}
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : table opcode = some handler) :
    (InterpreterLoop.loopFuel (toLoopHandler table) (nSteps + 1) state).status =
      (InterpreterLoop.loopFuel (toLoopHandler table) nSteps (handler state)).status := by
  rw [loopFuel_succ_running_lookup nSteps h_status h_decode h_lookup]

theorem loopFuel_succ_running_missing_invalid
    {table : HandlerTable} (nSteps : Nat) {state : EvmState}
    {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : table opcode = none) :
    InterpreterLoop.loopFuel (toLoopHandler table) (nSteps + 1) state =
      InterpreterLoop.loopFuel (toLoopHandler table) nSteps state.invalid := by
  rw [loopFuel_succ_running_decode table nSteps h_status h_decode]
  rw [HandlerTable.dispatchOpcode_none h_lookup state]

theorem loopFuel_table_invalid_fixed
    (table : HandlerTable) :
    ∀ (nSteps : Nat) (state : EvmState),
      InterpreterLoop.loopFuel (toLoopHandler table) nSteps state.invalid = state.invalid
  | 0, _ => rfl
  | nSteps + 1, state => by
      simp [InterpreterLoop.loopFuel]

theorem loopFuel_table_invalid_fixed_status
    (table : HandlerTable) (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel (toLoopHandler table) nSteps state.invalid).status =
      .error := by
  rw [loopFuel_table_invalid_fixed table nSteps state]
  exact EvmState.invalid_status state

theorem loopFuel_succ_running_missing_invalid_status
    {table : HandlerTable} (nSteps : Nat) {state : EvmState}
    {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : table opcode = none) :
    (InterpreterLoop.loopFuel (toLoopHandler table) (nSteps + 1) state).status =
      .error := by
  rw [loopFuel_succ_running_missing_invalid nSteps h_status h_decode h_lookup]
  exact loopFuel_table_invalid_fixed_status table nSteps state

theorem loopFuel_succ_running_unsupported_invalid
    (table : HandlerTable) (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    InterpreterLoop.loopFuel (toLoopHandler table) (nSteps + 1) state =
      InterpreterLoop.loopFuel (toLoopHandler table) nSteps state.invalid := by
  rw [InterpreterLoop.loopFuel_succ_running (toLoopHandler table) nSteps state h_status]
  rw [InterpreterLoop.stepWithHandler_of_unsupported (toLoopHandler table) h_decode]

theorem loopFuel_succ_running_unsupported_invalid_status
    (table : HandlerTable) (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    (InterpreterLoop.loopFuel (toLoopHandler table) (nSteps + 1) state).status =
      .error := by
  rw [loopFuel_succ_running_unsupported_invalid table nSteps h_status h_decode]
  exact loopFuel_table_invalid_fixed_status table nSteps state

theorem loopFuel_succ_running_eof_invalid
    (table : HandlerTable) (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.code.length ≤ state.pc) :
    InterpreterLoop.loopFuel (toLoopHandler table) (nSteps + 1) state =
      InterpreterLoop.loopFuel (toLoopHandler table) nSteps state.invalid := by
  rw [InterpreterLoop.loopFuel_succ_running (toLoopHandler table) nSteps state h_status]
  rw [stepWithTableHandler_eof_invalid table h_pc]

theorem loopFuel_succ_running_eof_invalid_status
    (table : HandlerTable) (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.code.length ≤ state.pc) :
    (InterpreterLoop.loopFuel (toLoopHandler table) (nSteps + 1) state).status =
      .error := by
  rw [loopFuel_succ_running_eof_invalid table nSteps h_status h_pc]
  exact loopFuel_table_invalid_fixed_status table nSteps state

theorem loopFuel_empty_succ_running_decode
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    InterpreterLoop.loopFuel (toLoopHandler HandlerTable.empty) (nSteps + 1) state =
      InterpreterLoop.loopFuel (toLoopHandler HandlerTable.empty) nSteps state.invalid := by
  rw [loopFuel_succ_running_decode HandlerTable.empty nSteps h_status h_decode]
  simp [HandlerTable.dispatchOpcode]

theorem loopFuel_empty_succ_running_decode_status
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    (InterpreterLoop.loopFuel (toLoopHandler HandlerTable.empty) (nSteps + 1) state).status =
      .error := by
  rw [loopFuel_empty_succ_running_decode nSteps h_status h_decode]
  exact loopFuel_table_invalid_fixed_status HandlerTable.empty nSteps state

theorem handlerMatchesSpec_of_dispatch_eq
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state) :
    InterpreterSimulation.HandlerMatchesSpec (toLoopHandler table) spec := by
  intro opcode state h_decode
  exact h_dispatch opcode state h_decode

end HandlerLoopBridge

end EvmAsm.Evm64
