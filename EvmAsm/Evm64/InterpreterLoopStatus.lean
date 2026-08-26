/-
  EvmAsm.Evm64.InterpreterLoopStatus

  Status/control lemmas for the pure interpreter loop (GH #108).
-/

module

public import EvmAsm.Evm64.InterpreterLoop

@[expose] public section

namespace EvmAsm.Evm64

namespace InterpreterLoopStatus

abbrev Handler := InterpreterLoop.Handler

/-- Predicate for states that the nSteps-bounded interpreter loop leaves fixed.
    Distinctive token: InterpreterLoopStatus.loopFuel_nonRunning #108. -/
def nonRunning (state : EvmState) : Prop :=
  state.status ≠ .running

theorem nonRunning_of_stopped {state : EvmState}
    (h_status : state.status = .stopped) : nonRunning state := by
  simp [nonRunning, h_status]

theorem nonRunning_of_returned {state : EvmState} {data : List (BitVec 8)}
    (h_status : state.status = .returned data) : nonRunning state := by
  simp [nonRunning, h_status]

theorem nonRunning_of_reverted {state : EvmState} {data : List (BitVec 8)}
    (h_status : state.status = .reverted data) : nonRunning state := by
  simp [nonRunning, h_status]

theorem nonRunning_of_error {state : EvmState}
    (h_status : state.status = .error) : nonRunning state := by
  simp [nonRunning, h_status]

theorem loopFuel_nonRunning
    (handler : Handler) (nSteps : Nat) (state : EvmState)
    (h_nonRunning : nonRunning state) :
    InterpreterLoop.loopFuel handler nSteps state = state := by
  cases nSteps with
  | zero => rfl
  | succ nSteps =>
      cases h_status : state.status <;>
        simp [InterpreterLoop.loopFuel, h_status, nonRunning] at h_nonRunning ⊢

theorem loopFuel_nonRunning_status
    (handler : Handler) (nSteps : Nat) (state : EvmState)
    (h_nonRunning : nonRunning state) :
    (InterpreterLoop.loopFuel handler nSteps state).status = state.status := by
  rw [loopFuel_nonRunning handler nSteps state h_nonRunning]

theorem loopFuel_stopped
    (handler : Handler) (nSteps : Nat) (state : EvmState)
    (h_status : state.status = .stopped) :
    InterpreterLoop.loopFuel handler nSteps state = state :=
  loopFuel_nonRunning handler nSteps state (nonRunning_of_stopped h_status)

theorem loopFuel_stopped_status
    (handler : Handler) (nSteps : Nat) (state : EvmState)
    (h_status : state.status = .stopped) :
    (InterpreterLoop.loopFuel handler nSteps state).status = .stopped := by
  rw [loopFuel_stopped handler nSteps state h_status, h_status]

theorem loopFuel_returned
    (handler : Handler) (nSteps : Nat) (state : EvmState) (data : List (BitVec 8))
    (h_status : state.status = .returned data) :
    InterpreterLoop.loopFuel handler nSteps state = state :=
  loopFuel_nonRunning handler nSteps state (nonRunning_of_returned h_status)

theorem loopFuel_returned_status
    (handler : Handler) (nSteps : Nat) (state : EvmState) (data : List (BitVec 8))
    (h_status : state.status = .returned data) :
    (InterpreterLoop.loopFuel handler nSteps state).status = .returned data := by
  rw [loopFuel_returned handler nSteps state data h_status, h_status]

theorem loopFuel_reverted
    (handler : Handler) (nSteps : Nat) (state : EvmState) (data : List (BitVec 8))
    (h_status : state.status = .reverted data) :
    InterpreterLoop.loopFuel handler nSteps state = state :=
  loopFuel_nonRunning handler nSteps state (nonRunning_of_reverted h_status)

theorem loopFuel_reverted_status
    (handler : Handler) (nSteps : Nat) (state : EvmState) (data : List (BitVec 8))
    (h_status : state.status = .reverted data) :
    (InterpreterLoop.loopFuel handler nSteps state).status = .reverted data := by
  rw [loopFuel_reverted handler nSteps state data h_status, h_status]

theorem loopFuel_error
    (handler : Handler) (nSteps : Nat) (state : EvmState)
    (h_status : state.status = .error) :
    InterpreterLoop.loopFuel handler nSteps state = state :=
  loopFuel_nonRunning handler nSteps state (nonRunning_of_error h_status)

theorem loopFuel_error_status
    (handler : Handler) (nSteps : Nat) (state : EvmState)
    (h_status : state.status = .error) :
    (InterpreterLoop.loopFuel handler nSteps state).status = .error := by
  rw [loopFuel_error handler nSteps state h_status, h_status]

theorem stepWithHandler_eof_invalid_status
    (handler : Handler) {state : EvmState}
    (h_pc : state.code.length ≤ state.pc) :
    (InterpreterLoop.stepWithHandler handler state).status = .error := by
  rw [InterpreterLoop.stepWithHandler_eof_invalid handler h_pc]
  exact EvmState.invalid_status state

theorem stepWithHandler_unsupported_invalid_status
    (handler : Handler) {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    (InterpreterLoop.stepWithHandler handler state).status = .error := by
  rw [InterpreterLoop.stepWithHandler_of_unsupported handler h_decode]
  exact EvmState.invalid_status state

theorem loopFuel_one_eof_invalid
    (handler : Handler) {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.code.length ≤ state.pc) :
    InterpreterLoop.loopFuel handler 1 state = state.invalid := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  simp [InterpreterLoop.stepWithHandler_eof_invalid handler h_pc]

theorem loopFuel_one_eof_invalid_status
    (handler : Handler) {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.code.length ≤ state.pc) :
    (InterpreterLoop.loopFuel handler 1 state).status = .error := by
  rw [loopFuel_one_eof_invalid handler h_status h_pc]
  exact EvmState.invalid_status state

theorem loopFuel_one_unsupported_invalid
    (handler : Handler) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    InterpreterLoop.loopFuel handler 1 state = state.invalid := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  simp [InterpreterLoop.stepWithHandler_of_unsupported handler h_decode]

theorem loopFuel_one_unsupported_invalid_status
    (handler : Handler) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    (InterpreterLoop.loopFuel handler 1 state).status = .error := by
  rw [loopFuel_one_unsupported_invalid handler h_status h_decode]
  exact EvmState.invalid_status state

theorem loopFuel_one_fetch_unsupported_invalid
    (handler : Handler) {state : EvmState} {byte : BitVec 8}
    (h_status : state.status = .running)
    (h_fetch : InterpreterLoop.fetchOpcodeByte? state = some byte)
    (h_decode : EvmOpcode.decodeByte? byte.toNat = none) :
    InterpreterLoop.loopFuel handler 1 state = state.invalid :=
  loopFuel_one_unsupported_invalid handler h_status
    (InterpreterLoop.decodeCurrentOpcode?_of_fetch_unsupported h_fetch h_decode)

theorem loopFuel_one_fetch_unsupported_invalid_status
    (handler : Handler) {state : EvmState} {byte : BitVec 8}
    (h_status : state.status = .running)
    (h_fetch : InterpreterLoop.fetchOpcodeByte? state = some byte)
    (h_decode : EvmOpcode.decodeByte? byte.toNat = none) :
    (InterpreterLoop.loopFuel handler 1 state).status = .error := by
  rw [loopFuel_one_fetch_unsupported_invalid handler h_status h_fetch h_decode]
  exact EvmState.invalid_status state

theorem loopFuel_one_decode
    (handler : Handler) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    InterpreterLoop.loopFuel handler 1 state = handler opcode state := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  simp [InterpreterLoop.stepWithHandler_of_decode handler h_decode]

theorem loopFuel_one_decode_status
    (handler : Handler) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    (InterpreterLoop.loopFuel handler 1 state).status = (handler opcode state).status := by
  rw [loopFuel_one_decode handler h_status h_decode]

end InterpreterLoopStatus

end EvmAsm.Evm64
