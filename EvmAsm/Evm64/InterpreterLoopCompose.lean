/-
  EvmAsm.Evm64.InterpreterLoopCompose

  Whole-loop composition hooks for the pure interpreter loop (GH #109).
-/

module

public import EvmAsm.Evm64.InterpreterLoop

@[expose] public section

namespace EvmAsm.Evm64

namespace InterpreterLoopCompose

abbrev Handler := InterpreterLoop.Handler

/-- Non-running states are fixed points for every nSteps budget. -/
theorem loopFuel_of_not_running
    (handler : Handler) (nSteps : Nat) (state : EvmState)
    (h_status : state.status ≠ .running) :
    InterpreterLoop.loopFuel handler nSteps state = state := by
  cases nSteps with
  | zero => rfl
  | succ _ =>
      cases h : state.status <;> simp [InterpreterLoop.loopFuel, h] at h_status ⊢

/-- Distinctive token: InterpreterLoopCompose.loopFuel_add #109. -/
theorem loopFuel_add
    (handler : Handler) (nStepsA nStepsB : Nat) (state : EvmState) :
    InterpreterLoop.loopFuel handler (nStepsA + nStepsB) state =
      InterpreterLoop.loopFuel handler nStepsB
        (InterpreterLoop.loopFuel handler nStepsA state) := by
  induction nStepsA generalizing state with
  | zero => simp
  | succ nStepsA ih =>
      rw [Nat.succ_add]
      cases h_status : state.status
      · simp [InterpreterLoop.loopFuel, h_status]
        exact ih (InterpreterLoop.stepWithHandler handler state)
      · simp [InterpreterLoop.loopFuel, h_status, loopFuel_of_not_running]
      · simp [InterpreterLoop.loopFuel, h_status, loopFuel_of_not_running]
      · simp [InterpreterLoop.loopFuel, h_status, loopFuel_of_not_running]
      · simp [InterpreterLoop.loopFuel, h_status, loopFuel_of_not_running]

theorem loopFuel_add_status
    (handler : Handler) (nStepsA nStepsB : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel handler (nStepsA + nStepsB) state).status =
      (InterpreterLoop.loopFuel handler nStepsB
        (InterpreterLoop.loopFuel handler nStepsA state)).status := by
  rw [loopFuel_add handler nStepsA nStepsB state]

theorem loopFuel_one_add
    (handler : Handler) (nSteps : Nat) (state : EvmState) :
    InterpreterLoop.loopFuel handler (1 + nSteps) state =
      InterpreterLoop.loopFuel handler nSteps
        (InterpreterLoop.loopFuel handler 1 state) := by
  exact loopFuel_add handler 1 nSteps state

theorem loopFuel_one_add_status
    (handler : Handler) (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel handler (1 + nSteps) state).status =
      (InterpreterLoop.loopFuel handler nSteps
        (InterpreterLoop.loopFuel handler 1 state)).status := by
  rw [loopFuel_one_add handler nSteps state]

theorem loopFuel_add_one
    (handler : Handler) (nSteps : Nat) (state : EvmState) :
    InterpreterLoop.loopFuel handler (nSteps + 1) state =
      InterpreterLoop.loopFuel handler 1
        (InterpreterLoop.loopFuel handler nSteps state) := by
  exact loopFuel_add handler nSteps 1 state

theorem loopFuel_add_one_status
    (handler : Handler) (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel handler (nSteps + 1) state).status =
      (InterpreterLoop.loopFuel handler 1
        (InterpreterLoop.loopFuel handler nSteps state)).status := by
  rw [loopFuel_add_one handler nSteps state]

end InterpreterLoopCompose

end EvmAsm.Evm64
