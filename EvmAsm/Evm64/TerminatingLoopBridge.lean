/-
  EvmAsm.Evm64.TerminatingLoopBridge

  Executable-loop bridge for terminating handler-table entries (GH #113).
-/

module

public import EvmAsm.Evm64.HandlerLoopBridge
public import EvmAsm.Evm64.TerminatingHandlers

@[expose] public section

namespace EvmAsm.Evm64

namespace TerminatingLoopBridge

/--
Executable-loop handler backed by the terminating opcode handler table.

Distinctive token: TerminatingLoopBridge.terminatingLoopHandler #113.
-/
def terminatingLoopHandler : InterpreterLoop.Handler :=
  HandlerLoopBridge.toLoopHandler TerminatingHandlers.terminatingHandlerTable

@[simp] theorem terminatingLoopHandler_apply
    (opcode : EvmOpcode) (state : EvmState) :
    terminatingLoopHandler opcode state =
      HandlerTable.dispatchOpcode TerminatingHandlers.terminatingHandlerTable
        opcode state := rfl

theorem stepWithTerminatingHandler_STOP
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .STOP) :
    InterpreterLoop.stepWithHandler terminatingLoopHandler state = state.stop := by
  change
    InterpreterLoop.stepWithHandler
      (HandlerLoopBridge.toLoopHandler TerminatingHandlers.terminatingHandlerTable)
      state = state.stop
  rw [HandlerLoopBridge.stepWithTableHandler_of_decode
    TerminatingHandlers.terminatingHandlerTable h_decode]
  simp

theorem stepWithTerminatingHandler_STOP_status
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .STOP) :
    (InterpreterLoop.stepWithHandler terminatingLoopHandler state).status =
      .stopped := by
  rw [stepWithTerminatingHandler_STOP h_decode]
  exact EvmState.stop_status state

theorem stepWithTerminatingHandler_INVALID
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .INVALID) :
    InterpreterLoop.stepWithHandler terminatingLoopHandler state = state.invalid := by
  change
    InterpreterLoop.stepWithHandler
      (HandlerLoopBridge.toLoopHandler TerminatingHandlers.terminatingHandlerTable)
      state = state.invalid
  rw [HandlerLoopBridge.stepWithTableHandler_of_decode
    TerminatingHandlers.terminatingHandlerTable h_decode]
  simp

theorem stepWithTerminatingHandler_INVALID_status
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .INVALID) :
    (InterpreterLoop.stepWithHandler terminatingLoopHandler state).status =
      .error := by
  rw [stepWithTerminatingHandler_INVALID h_decode]
  exact EvmState.invalid_status state

/--
Decoded opcodes absent from `terminatingHandlerTable` step to `state.invalid`
through the terminating loop handler.

Distinctive token: TerminatingLoopBridge.stepWithTerminatingHandler_missing_invalid #113.
-/
theorem stepWithTerminatingHandler_missing_invalid
    {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : TerminatingHandlers.terminatingHandlerTable opcode = none) :
    InterpreterLoop.stepWithHandler terminatingLoopHandler state = state.invalid :=
  HandlerLoopBridge.stepWithTableHandler_missing_invalid h_decode h_lookup

/--
Status projection of `stepWithTerminatingHandler_missing_invalid`: missing-entry
opcodes step to `.error`.
-/
theorem stepWithTerminatingHandler_missing_invalid_status
    {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : TerminatingHandlers.terminatingHandlerTable opcode = none) :
    (InterpreterLoop.stepWithHandler terminatingLoopHandler state).status =
      .error := by
  rw [stepWithTerminatingHandler_missing_invalid h_decode h_lookup]
  exact EvmState.invalid_status state

theorem loopFuel_stop_fixed :
    ∀ (fuel : Nat) (state : EvmState),
      InterpreterLoop.loopFuel terminatingLoopHandler fuel state.stop = state.stop
  | 0, _ => rfl
  | fuel + 1, state => by
      simp [InterpreterLoop.loopFuel]

theorem loopFuel_stop_fixed_status
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel terminatingLoopHandler fuel state.stop).status =
      .stopped := by
  rw [loopFuel_stop_fixed fuel state]
  exact EvmState.stop_status state

theorem loopFuel_invalid_fixed :
    ∀ (fuel : Nat) (state : EvmState),
      InterpreterLoop.loopFuel terminatingLoopHandler fuel state.invalid = state.invalid
  | 0, _ => rfl
  | fuel + 1, state => by
      simp [InterpreterLoop.loopFuel]

theorem loopFuel_invalid_fixed_status
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel terminatingLoopHandler fuel state.invalid).status =
      .error := by
  rw [loopFuel_invalid_fixed fuel state]
  exact EvmState.invalid_status state

theorem loopFuel_succ_running_STOP
    (fuel : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .STOP) :
    InterpreterLoop.loopFuel terminatingLoopHandler (fuel + 1) state =
      state.stop := by
  rw [InterpreterLoop.loopFuel_succ_running terminatingLoopHandler fuel state h_status]
  rw [stepWithTerminatingHandler_STOP h_decode]
  exact loopFuel_stop_fixed fuel state

theorem loopFuel_succ_running_STOP_status
    (fuel : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .STOP) :
    (InterpreterLoop.loopFuel terminatingLoopHandler (fuel + 1) state).status =
      .stopped := by
  rw [loopFuel_succ_running_STOP fuel h_status h_decode]
  exact EvmState.stop_status state

theorem loopFuel_succ_running_INVALID
    (fuel : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .INVALID) :
    InterpreterLoop.loopFuel terminatingLoopHandler (fuel + 1) state =
      state.invalid := by
  rw [InterpreterLoop.loopFuel_succ_running terminatingLoopHandler fuel state h_status]
  rw [stepWithTerminatingHandler_INVALID h_decode]
  exact loopFuel_invalid_fixed fuel state

theorem loopFuel_succ_running_INVALID_status
    (fuel : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .INVALID) :
    (InterpreterLoop.loopFuel terminatingLoopHandler (fuel + 1) state).status =
      .error := by
  rw [loopFuel_succ_running_INVALID fuel h_status h_decode]
  exact EvmState.invalid_status state

end TerminatingLoopBridge

end EvmAsm.Evm64
