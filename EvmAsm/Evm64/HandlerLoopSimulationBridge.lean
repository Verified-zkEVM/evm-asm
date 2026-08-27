/-
  EvmAsm.Evm64.HandlerLoopSimulationBridge

  Lift handler-table dispatch agreement through the pure interpreter loop
  simulation surface (GH #107 / GH #109).
-/

module

public import EvmAsm.Evm64.HandlerLoopBridge
public import EvmAsm.Evm64.InterpreterLoopSimulation
public import EvmAsm.Evm64.InterpreterTraceSimulation

public section

namespace EvmAsm.Evm64

namespace HandlerLoopSimulationBridge

/--
If a handler table dispatches each decoded opcode like the executable-spec
handler, then the table-backed interpreter loop matches the executable-spec
loop for every nSteps budget.

Distinctive token: HandlerLoopSimulationBridge.loopFuel_table_matchesSpec #107 #109.
-/
theorem loopFuel_table_matchesSpec
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state) :
    ∀ (nSteps : Nat) (state : EvmState),
      InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state =
        InterpreterLoop.loopFuel spec nSteps state := by
  exact InterpreterSimulation.loopFuel_matchesSpec
    (HandlerLoopBridge.handlerMatchesSpec_of_dispatch_eq table spec h_dispatch)

theorem stepWithTable_matchesSpec
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) :
    InterpreterLoop.stepWithHandler (HandlerLoopBridge.toLoopHandler table) state =
      InterpreterLoop.stepWithHandler spec state := by
  exact InterpreterSimulation.stepWithHandler_matchesSpec
    (HandlerLoopBridge.handlerMatchesSpec_of_dispatch_eq table spec h_dispatch) state

theorem stepWithTable_matchesSpec_status
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) :
    (InterpreterLoop.stepWithHandler (HandlerLoopBridge.toLoopHandler table) state).status =
      (InterpreterLoop.stepWithHandler spec state).status := by
  rw [stepWithTable_matchesSpec table spec h_dispatch state]

theorem stepWithTable_matchesSpec_memoryCells
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) :
    (InterpreterLoop.stepWithHandler (HandlerLoopBridge.toLoopHandler table) state).memoryCells =
      (InterpreterLoop.stepWithHandler spec state).memoryCells := by
  rw [stepWithTable_matchesSpec table spec h_dispatch state]

theorem stepWithTable_matchesSpec_memory
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) (addr : Nat) :
    (InterpreterLoop.stepWithHandler (HandlerLoopBridge.toLoopHandler table) state).memory addr =
      (InterpreterLoop.stepWithHandler spec state).memory addr := by
  rw [stepWithTable_matchesSpec table spec h_dispatch state]

theorem stepWithTable_matchesSpec_memSize
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) :
    (InterpreterLoop.stepWithHandler (HandlerLoopBridge.toLoopHandler table) state).memSize =
      (InterpreterLoop.stepWithHandler spec state).memSize := by
  rw [stepWithTable_matchesSpec table spec h_dispatch state]

theorem stepWithTable_matchesSpec_code
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) :
    (InterpreterLoop.stepWithHandler (HandlerLoopBridge.toLoopHandler table) state).code =
      (InterpreterLoop.stepWithHandler spec state).code := by
  rw [stepWithTable_matchesSpec table spec h_dispatch state]

theorem stepWithTable_matchesSpec_codeLen
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) :
    (InterpreterLoop.stepWithHandler (HandlerLoopBridge.toLoopHandler table) state).codeLen =
      (InterpreterLoop.stepWithHandler spec state).codeLen := by
  rw [stepWithTable_matchesSpec table spec h_dispatch state]

theorem stepWithTable_matchesSpec_codeLenMatches_iff
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) :
    (InterpreterLoop.stepWithHandler
      (HandlerLoopBridge.toLoopHandler table) state).codeLenMatches ↔
      (InterpreterLoop.stepWithHandler spec state).codeLenMatches := by
  rw [stepWithTable_matchesSpec table spec h_dispatch state]

theorem stepWithTable_matchesSpec_codeLenMatches
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState)
    (h_codeLen :
      (InterpreterLoop.stepWithHandler spec state).codeLenMatches) :
    (InterpreterLoop.stepWithHandler
      (HandlerLoopBridge.toLoopHandler table) state).codeLenMatches := by
  rw [stepWithTable_matchesSpec table spec h_dispatch state]
  exact h_codeLen

theorem stepWithTable_matchesSpec_env
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) :
    (InterpreterLoop.stepWithHandler (HandlerLoopBridge.toLoopHandler table) state).env =
      (InterpreterLoop.stepWithHandler spec state).env := by
  rw [stepWithTable_matchesSpec table spec h_dispatch state]

theorem stepWithTable_matchesSpec_pc
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) :
    (InterpreterLoop.stepWithHandler (HandlerLoopBridge.toLoopHandler table) state).pc =
      (InterpreterLoop.stepWithHandler spec state).pc := by
  rw [stepWithTable_matchesSpec table spec h_dispatch state]

theorem stepWithTable_matchesSpec_gas
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) :
    (InterpreterLoop.stepWithHandler (HandlerLoopBridge.toLoopHandler table) state).gas =
      (InterpreterLoop.stepWithHandler spec state).gas := by
  rw [stepWithTable_matchesSpec table spec h_dispatch state]

theorem stepWithTable_matchesSpec_stack
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) :
    (InterpreterLoop.stepWithHandler (HandlerLoopBridge.toLoopHandler table) state).stack =
      (InterpreterLoop.stepWithHandler spec state).stack := by
  rw [stepWithTable_matchesSpec table spec h_dispatch state]

theorem loopFuel_table_matchesSpec_at
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state =
      InterpreterLoop.loopFuel spec nSteps state := by
  exact loopFuel_table_matchesSpec table spec h_dispatch nSteps state

theorem loopFuel_table_matchesSpec_at_status
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state).status =
      (InterpreterLoop.loopFuel spec nSteps state).status := by
  rw [loopFuel_table_matchesSpec_at table spec h_dispatch nSteps state]

theorem loopFuel_table_matchesSpec_at_pc
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state).pc =
      (InterpreterLoop.loopFuel spec nSteps state).pc := by
  rw [loopFuel_table_matchesSpec_at table spec h_dispatch nSteps state]

theorem loopFuel_table_matchesSpec_at_gas
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state).gas =
      (InterpreterLoop.loopFuel spec nSteps state).gas := by
  rw [loopFuel_table_matchesSpec_at table spec h_dispatch nSteps state]

theorem loopFuel_table_matchesSpec_at_stack
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state).stack =
      (InterpreterLoop.loopFuel spec nSteps state).stack := by
  rw [loopFuel_table_matchesSpec_at table spec h_dispatch nSteps state]

theorem loopFuel_table_matchesSpec_at_memoryCells
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state).memoryCells =
      (InterpreterLoop.loopFuel spec nSteps state).memoryCells := by
  rw [loopFuel_table_matchesSpec_at table spec h_dispatch nSteps state]

theorem loopFuel_table_matchesSpec_at_memory
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) (addr : Nat) :
    (InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state).memory addr =
      (InterpreterLoop.loopFuel spec nSteps state).memory addr := by
  rw [loopFuel_table_matchesSpec_at table spec h_dispatch nSteps state]

theorem loopFuel_table_matchesSpec_at_memSize
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state).memSize =
      (InterpreterLoop.loopFuel spec nSteps state).memSize := by
  rw [loopFuel_table_matchesSpec_at table spec h_dispatch nSteps state]

theorem loopFuel_table_matchesSpec_at_code
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state).code =
      (InterpreterLoop.loopFuel spec nSteps state).code := by
  rw [loopFuel_table_matchesSpec_at table spec h_dispatch nSteps state]

theorem loopFuel_table_matchesSpec_at_codeLen
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state).codeLen =
      (InterpreterLoop.loopFuel spec nSteps state).codeLen := by
  rw [loopFuel_table_matchesSpec_at table spec h_dispatch nSteps state]

theorem loopFuel_table_matchesSpec_at_codeLenMatches_iff
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel
      (HandlerLoopBridge.toLoopHandler table) nSteps state).codeLenMatches ↔
      (InterpreterLoop.loopFuel spec nSteps state).codeLenMatches := by
  rw [loopFuel_table_matchesSpec_at table spec h_dispatch nSteps state]

theorem loopFuel_table_matchesSpec_at_codeLenMatches
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState)
    (h_codeLen : (InterpreterLoop.loopFuel spec nSteps state).codeLenMatches) :
    (InterpreterLoop.loopFuel
      (HandlerLoopBridge.toLoopHandler table) nSteps state).codeLenMatches := by
  rw [loopFuel_table_matchesSpec_at table spec h_dispatch nSteps state]
  exact h_codeLen

theorem loopFuel_table_matchesSpec_at_env
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state).env =
      (InterpreterLoop.loopFuel spec nSteps state).env := by
  rw [loopFuel_table_matchesSpec_at table spec h_dispatch nSteps state]

/--
Handler-table dispatch agreement also preserves the decoded opcode trace.

Distinctive token: handlerTableTraceMatchesSpec #109 #107.
-/
theorem loopTrace_table_matchesSpec
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state) :
    ∀ (nSteps : Nat) (state : EvmState),
      InterpreterTrace.loopTrace (HandlerLoopBridge.toLoopHandler table) nSteps state =
        InterpreterTrace.loopTrace spec nSteps state := by
  exact InterpreterTraceSimulation.loopTrace_matchesSpec
    (HandlerLoopBridge.handlerMatchesSpec_of_dispatch_eq table spec h_dispatch)

theorem loopTrace_table_matchesSpec_at
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    InterpreterTrace.loopTrace (HandlerLoopBridge.toLoopHandler table) nSteps state =
      InterpreterTrace.loopTrace spec nSteps state := by
  exact loopTrace_table_matchesSpec table spec h_dispatch nSteps state

theorem loopTrace_table_matchesSpec_at_length
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterTrace.loopTrace
        (HandlerLoopBridge.toLoopHandler table) nSteps state).length =
      (InterpreterTrace.loopTrace spec nSteps state).length := by
  rw [loopTrace_table_matchesSpec_at table spec h_dispatch nSteps state]

theorem loopTrace_table_matchesSpec_at_get?
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) (idx : Nat) :
    (InterpreterTrace.loopTrace
        (HandlerLoopBridge.toLoopHandler table) nSteps state)[idx]? =
      (InterpreterTrace.loopTrace spec nSteps state)[idx]? := by
  rw [loopTrace_table_matchesSpec_at table spec h_dispatch nSteps state]

/--
Handler-table dispatch agreement preserves the final loop state together with
the decoded opcode trace.

Distinctive token: handlerTableLoopFuelAndTraceMatchesSpec #109 #107.
-/
theorem loopFuelAndTrace_table_matchesSpec_at
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state,
      InterpreterTrace.loopTrace (HandlerLoopBridge.toLoopHandler table) nSteps state) =
    (InterpreterLoop.loopFuel spec nSteps state,
      InterpreterTrace.loopTrace spec nSteps state) := by
  exact InterpreterTraceSimulation.loopFuelAndTrace_matchesSpec
    (HandlerLoopBridge.handlerMatchesSpec_of_dispatch_eq table spec h_dispatch)
    nSteps state

theorem loopFuelAndTrace_table_matchesSpec_at_state
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state =
      InterpreterLoop.loopFuel spec nSteps state := by
  exact congrArg Prod.fst
    (loopFuelAndTrace_table_matchesSpec_at table spec h_dispatch nSteps state)

theorem loopFuelAndTrace_table_matchesSpec_at_status
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel
        (HandlerLoopBridge.toLoopHandler table) nSteps state).status =
      (InterpreterLoop.loopFuel spec nSteps state).status := by
  exact congrArg (fun result => result.1.status)
    (loopFuelAndTrace_table_matchesSpec_at table spec h_dispatch nSteps state)

theorem loopFuelAndTrace_table_matchesSpec_at_pc
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel
        (HandlerLoopBridge.toLoopHandler table) nSteps state).pc =
      (InterpreterLoop.loopFuel spec nSteps state).pc := by
  exact congrArg (fun result => result.1.pc)
    (loopFuelAndTrace_table_matchesSpec_at table spec h_dispatch nSteps state)

theorem loopFuelAndTrace_table_matchesSpec_at_gas
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel
        (HandlerLoopBridge.toLoopHandler table) nSteps state).gas =
      (InterpreterLoop.loopFuel spec nSteps state).gas := by
  exact congrArg (fun result => result.1.gas)
    (loopFuelAndTrace_table_matchesSpec_at table spec h_dispatch nSteps state)

theorem loopFuelAndTrace_table_matchesSpec_at_stack
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel
        (HandlerLoopBridge.toLoopHandler table) nSteps state).stack =
      (InterpreterLoop.loopFuel spec nSteps state).stack := by
  exact congrArg (fun result => result.1.stack)
    (loopFuelAndTrace_table_matchesSpec_at table spec h_dispatch nSteps state)

theorem loopFuelAndTrace_table_matchesSpec_at_memoryCells
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel
        (HandlerLoopBridge.toLoopHandler table) nSteps state).memoryCells =
      (InterpreterLoop.loopFuel spec nSteps state).memoryCells := by
  exact congrArg (fun result => result.1.memoryCells)
    (loopFuelAndTrace_table_matchesSpec_at table spec h_dispatch nSteps state)

theorem loopFuelAndTrace_table_matchesSpec_at_memory
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) (addr : Nat) :
    (InterpreterLoop.loopFuel
        (HandlerLoopBridge.toLoopHandler table) nSteps state).memory addr =
      (InterpreterLoop.loopFuel spec nSteps state).memory addr := by
  exact congrFun (congrArg (fun result => result.1.memory)
    (loopFuelAndTrace_table_matchesSpec_at table spec h_dispatch nSteps state)) addr

theorem loopFuelAndTrace_table_matchesSpec_at_memSize
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel
        (HandlerLoopBridge.toLoopHandler table) nSteps state).memSize =
      (InterpreterLoop.loopFuel spec nSteps state).memSize := by
  exact congrArg (fun result => result.1.memSize)
    (loopFuelAndTrace_table_matchesSpec_at table spec h_dispatch nSteps state)

theorem loopFuelAndTrace_table_matchesSpec_at_code
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel
        (HandlerLoopBridge.toLoopHandler table) nSteps state).code =
      (InterpreterLoop.loopFuel spec nSteps state).code := by
  exact congrArg (fun result => result.1.code)
    (loopFuelAndTrace_table_matchesSpec_at table spec h_dispatch nSteps state)

theorem loopFuelAndTrace_table_matchesSpec_at_codeLen
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel
        (HandlerLoopBridge.toLoopHandler table) nSteps state).codeLen =
      (InterpreterLoop.loopFuel spec nSteps state).codeLen := by
  exact congrArg (fun result => result.1.codeLen)
    (loopFuelAndTrace_table_matchesSpec_at table spec h_dispatch nSteps state)

theorem loopFuelAndTrace_table_matchesSpec_at_codeLenMatches_iff
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel
        (HandlerLoopBridge.toLoopHandler table) nSteps state).codeLenMatches ↔
      (InterpreterLoop.loopFuel spec nSteps state).codeLenMatches := by
  rw [loopFuelAndTrace_table_matchesSpec_at_state
    table spec h_dispatch nSteps state]

theorem loopFuelAndTrace_table_matchesSpec_at_codeLenMatches
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState)
    (h_codeLen : (InterpreterLoop.loopFuel spec nSteps state).codeLenMatches) :
    (InterpreterLoop.loopFuel
        (HandlerLoopBridge.toLoopHandler table) nSteps state).codeLenMatches := by
  rw [loopFuelAndTrace_table_matchesSpec_at_state
    table spec h_dispatch nSteps state]
  exact h_codeLen

theorem loopFuelAndTrace_table_matchesSpec_at_env
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel
        (HandlerLoopBridge.toLoopHandler table) nSteps state).env =
      (InterpreterLoop.loopFuel spec nSteps state).env := by
  exact congrArg (fun result => result.1.env)
    (loopFuelAndTrace_table_matchesSpec_at table spec h_dispatch nSteps state)

theorem loopFuelAndTrace_table_matchesSpec_at_trace
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    InterpreterTrace.loopTrace (HandlerLoopBridge.toLoopHandler table) nSteps state =
      InterpreterTrace.loopTrace spec nSteps state := by
  exact congrArg Prod.snd
    (loopFuelAndTrace_table_matchesSpec_at table spec h_dispatch nSteps state)

theorem loopResultsMatch_table_matchesSpec
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state) :
    InterpreterLoopSimulation.LoopResultsMatch
      (HandlerLoopBridge.toLoopHandler table) spec := by
  exact loopFuel_table_matchesSpec table spec h_dispatch

end HandlerLoopSimulationBridge

end EvmAsm.Evm64
