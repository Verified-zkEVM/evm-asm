/-
  EvmAsm.Evm64.InterpreterSimulation

  First simulation-relation surface for the pure interpreter loop (GH #109).
-/

module

public import EvmAsm.Evm64.InterpreterLoop

@[expose] public section

namespace EvmAsm.Evm64

namespace InterpreterSimulation

abbrev Handler := InterpreterLoop.Handler

/--
Per-opcode agreement between an implementation handler and an executable-spec
handler, restricted to the opcode decoded at the current state.
-/
def HandlerMatchesSpec (impl spec : Handler) : Prop :=
  ∀ (opcode : EvmOpcode) (state : EvmState),
    InterpreterLoop.decodeCurrentOpcode? state = some opcode →
      impl opcode state = spec opcode state

theorem HandlerMatchesSpec.refl (handler : Handler) :
    HandlerMatchesSpec handler handler := by
  intro opcode state h_decode
  rfl

theorem HandlerMatchesSpec.symm
    {impl spec : Handler} (h_match : HandlerMatchesSpec impl spec) :
    HandlerMatchesSpec spec impl := by
  intro opcode state h_decode
  exact (h_match opcode state h_decode).symm

theorem HandlerMatchesSpec.trans
    {impl mid spec : Handler}
    (h_left : HandlerMatchesSpec impl mid)
    (h_right : HandlerMatchesSpec mid spec) :
    HandlerMatchesSpec impl spec := by
  intro opcode state h_decode
  exact (h_left opcode state h_decode).trans (h_right opcode state h_decode)

theorem HandlerMatchesSpec.status_eq
    {impl spec : Handler} (h_match : HandlerMatchesSpec impl spec)
    {opcode : EvmOpcode} {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    (impl opcode state).status = (spec opcode state).status := by
  rw [h_match opcode state h_decode]

theorem stepWithHandler_matchesSpec
    {impl spec : Handler} (h_match : HandlerMatchesSpec impl spec) (state : EvmState) :
    InterpreterLoop.stepWithHandler impl state =
      InterpreterLoop.stepWithHandler spec state := by
  unfold InterpreterLoop.stepWithHandler
  cases h_decode : InterpreterLoop.decodeCurrentOpcode? state with
  | none => rfl
  | some opcode => exact h_match opcode state h_decode

theorem stepWithHandler_matchesSpec_status
    {impl spec : Handler} (h_match : HandlerMatchesSpec impl spec) (state : EvmState) :
    (InterpreterLoop.stepWithHandler impl state).status =
      (InterpreterLoop.stepWithHandler spec state).status := by
  rw [stepWithHandler_matchesSpec h_match state]

theorem stepWithHandler_matchesSpec_codeLenMatches_iff
    {impl spec : Handler} (h_match : HandlerMatchesSpec impl spec) (state : EvmState) :
    (InterpreterLoop.stepWithHandler impl state).codeLenMatches ↔
      (InterpreterLoop.stepWithHandler spec state).codeLenMatches := by
  rw [stepWithHandler_matchesSpec h_match state]

theorem stepWithHandler_matchesSpec_codeLenMatches
    {impl spec : Handler} (h_match : HandlerMatchesSpec impl spec) (state : EvmState)
    (h_codeLen : (InterpreterLoop.stepWithHandler spec state).codeLenMatches) :
    (InterpreterLoop.stepWithHandler impl state).codeLenMatches := by
  rw [stepWithHandler_matchesSpec h_match state]
  exact h_codeLen

/-- Distinctive token: InterpreterSimulation.loopFuel_matchesSpec #109. -/
theorem loopFuel_matchesSpec
    {impl spec : Handler} (h_match : HandlerMatchesSpec impl spec) :
    ∀ (nSteps : Nat) (state : EvmState),
      InterpreterLoop.loopFuel impl nSteps state =
        InterpreterLoop.loopFuel spec nSteps state
  | 0, _ => rfl
  | nSteps + 1, state => by
      cases h_status : state.status <;>
        simp [InterpreterLoop.loopFuel, h_status]
      rw [stepWithHandler_matchesSpec h_match]
      exact loopFuel_matchesSpec h_match nSteps (InterpreterLoop.stepWithHandler spec state)

theorem loopFuel_matchesSpec_status
    {impl spec : Handler} (h_match : HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl nSteps state).status =
      (InterpreterLoop.loopFuel spec nSteps state).status := by
  rw [loopFuel_matchesSpec h_match nSteps state]

theorem loopFuel_matchesSpec_codeLenMatches_iff
    {impl spec : Handler} (h_match : HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl nSteps state).codeLenMatches ↔
      (InterpreterLoop.loopFuel spec nSteps state).codeLenMatches := by
  rw [loopFuel_matchesSpec h_match nSteps state]

theorem loopFuel_matchesSpec_codeLenMatches
    {impl spec : Handler} (h_match : HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState)
    (h_codeLen : (InterpreterLoop.loopFuel spec nSteps state).codeLenMatches) :
    (InterpreterLoop.loopFuel impl nSteps state).codeLenMatches := by
  rw [loopFuel_matchesSpec h_match nSteps state]
  exact h_codeLen

end InterpreterSimulation

end EvmAsm.Evm64
