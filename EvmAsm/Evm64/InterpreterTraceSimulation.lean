/-
  EvmAsm.Evm64.InterpreterTraceSimulation

  Trace-level simulation bridge for the pure interpreter loop (GH #109).
-/

module

public import EvmAsm.Evm64.InterpreterSimulation
public import EvmAsm.Evm64.InterpreterTrace

public section

namespace EvmAsm.Evm64

namespace InterpreterTraceSimulation

/--
Per-opcode handler agreement preserves the decoded-opcode trace of the
executable nSteps loop.

Distinctive token: InterpreterTraceSimulation.loopTrace_matchesSpec #109.
-/
theorem loopTrace_matchesSpec
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec) :
    ∀ (nSteps : Nat) (state : EvmState),
      InterpreterTrace.loopTrace impl nSteps state =
        InterpreterTrace.loopTrace spec nSteps state
  | 0, _ => rfl
  | nSteps + 1, state => by
      cases h_status : state.status <;>
        simp [InterpreterTrace.loopTrace, h_status]
      cases h_decode : InterpreterLoop.decodeCurrentOpcode? state with
      | none =>
          simp
      | some opcode =>
          rw [InterpreterSimulation.stepWithHandler_matchesSpec h_match state]
          simp [loopTrace_matchesSpec h_match nSteps
            (InterpreterLoop.stepWithHandler spec state)]

theorem loopTrace_length_matchesSpec
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterTrace.loopTrace impl nSteps state).length =
      (InterpreterTrace.loopTrace spec nSteps state).length := by
  rw [loopTrace_matchesSpec h_match nSteps state]

theorem loopTrace_matchesSpec_get?
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) (idx : Nat) :
    (InterpreterTrace.loopTrace impl nSteps state)[idx]? =
      (InterpreterTrace.loopTrace spec nSteps state)[idx]? := by
  rw [loopTrace_matchesSpec h_match nSteps state]

/-- Handler agreement preserves both the final nSteps-loop state and its decoded
    trace. -/
theorem loopFuelAndTrace_matchesSpec
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl nSteps state,
      InterpreterTrace.loopTrace impl nSteps state) =
    (InterpreterLoop.loopFuel spec nSteps state,
      InterpreterTrace.loopTrace spec nSteps state) := by
  simp [
    InterpreterSimulation.loopFuel_matchesSpec h_match nSteps state,
    loopTrace_matchesSpec h_match nSteps state]

theorem loopFuelAndTrace_matchesSpec_state
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    InterpreterLoop.loopFuel impl nSteps state =
      InterpreterLoop.loopFuel spec nSteps state := by
  exact congrArg Prod.fst (loopFuelAndTrace_matchesSpec h_match nSteps state)

theorem loopFuelAndTrace_matchesSpec_trace
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    InterpreterTrace.loopTrace impl nSteps state =
      InterpreterTrace.loopTrace spec nSteps state := by
  exact congrArg Prod.snd (loopFuelAndTrace_matchesSpec h_match nSteps state)

theorem loopFuelAndTrace_matchesSpec_status
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl nSteps state).status =
      (InterpreterLoop.loopFuel spec nSteps state).status := by
  exact congrArg (fun result => result.1.status)
    (loopFuelAndTrace_matchesSpec h_match nSteps state)

theorem loopFuelAndTrace_matchesSpec_pc
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl nSteps state).pc =
      (InterpreterLoop.loopFuel spec nSteps state).pc := by
  exact congrArg (fun result => result.1.pc)
    (loopFuelAndTrace_matchesSpec h_match nSteps state)

theorem loopFuelAndTrace_matchesSpec_gas
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl nSteps state).gas =
      (InterpreterLoop.loopFuel spec nSteps state).gas := by
  exact congrArg (fun result => result.1.gas)
    (loopFuelAndTrace_matchesSpec h_match nSteps state)

theorem loopFuelAndTrace_matchesSpec_stack
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl nSteps state).stack =
      (InterpreterLoop.loopFuel spec nSteps state).stack := by
  exact congrArg (fun result => result.1.stack)
    (loopFuelAndTrace_matchesSpec h_match nSteps state)

theorem loopFuelAndTrace_matchesSpec_memoryCells
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl nSteps state).memoryCells =
      (InterpreterLoop.loopFuel spec nSteps state).memoryCells := by
  exact congrArg (fun result => result.1.memoryCells)
    (loopFuelAndTrace_matchesSpec h_match nSteps state)

theorem loopFuelAndTrace_matchesSpec_memory
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) (addr : Nat) :
    (InterpreterLoop.loopFuel impl nSteps state).memory addr =
      (InterpreterLoop.loopFuel spec nSteps state).memory addr := by
  exact congrFun (congrArg (fun result => result.1.memory)
    (loopFuelAndTrace_matchesSpec h_match nSteps state)) addr

theorem loopFuelAndTrace_matchesSpec_memSize
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl nSteps state).memSize =
      (InterpreterLoop.loopFuel spec nSteps state).memSize := by
  exact congrArg (fun result => result.1.memSize)
    (loopFuelAndTrace_matchesSpec h_match nSteps state)

theorem loopFuelAndTrace_matchesSpec_code
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl nSteps state).code =
      (InterpreterLoop.loopFuel spec nSteps state).code := by
  exact congrArg (fun result => result.1.code)
    (loopFuelAndTrace_matchesSpec h_match nSteps state)

theorem loopFuelAndTrace_matchesSpec_codeLen
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl nSteps state).codeLen =
      (InterpreterLoop.loopFuel spec nSteps state).codeLen := by
  exact congrArg (fun result => result.1.codeLen)
    (loopFuelAndTrace_matchesSpec h_match nSteps state)

theorem loopFuelAndTrace_matchesSpec_codeLenMatches_iff
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl nSteps state).codeLenMatches ↔
      (InterpreterLoop.loopFuel spec nSteps state).codeLenMatches := by
  rw [loopFuelAndTrace_matchesSpec_state h_match nSteps state]

theorem loopFuelAndTrace_matchesSpec_codeLenMatches
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState)
    (h_codeLen : (InterpreterLoop.loopFuel spec nSteps state).codeLenMatches) :
    (InterpreterLoop.loopFuel impl nSteps state).codeLenMatches := by
  rw [loopFuelAndTrace_matchesSpec_state h_match nSteps state]
  exact h_codeLen

theorem loopFuelAndTrace_matchesSpec_env
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl nSteps state).env =
      (InterpreterLoop.loopFuel spec nSteps state).env := by
  exact congrArg (fun result => result.1.env)
    (loopFuelAndTrace_matchesSpec h_match nSteps state)

theorem loopFuelAndTrace_matchesSpec_trace_length
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterTrace.loopTrace impl nSteps state).length =
      (InterpreterTrace.loopTrace spec nSteps state).length := by
  rw [loopFuelAndTrace_matchesSpec_trace h_match nSteps state]

theorem loopFuelAndTrace_matchesSpec_trace_get?
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (nSteps : Nat) (state : EvmState) (idx : Nat) :
    (InterpreterTrace.loopTrace impl nSteps state)[idx]? =
      (InterpreterTrace.loopTrace spec nSteps state)[idx]? := by
  rw [loopFuelAndTrace_matchesSpec_trace h_match nSteps state]

end InterpreterTraceSimulation

end EvmAsm.Evm64
