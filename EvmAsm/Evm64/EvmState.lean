/-
  EvmAsm.Evm64.EvmState

  Initial EVM machine-state bundle for the interpreter layer (GH #105
  slice 1). This file stays at the assertion-composition level: concrete
  handlers and the dispatch loop can later use `evmStateIs` as the single
  resource invariant that packages stack, memory, code, environment, PC, gas,
  and status.
-/

import EvmAsm.Evm64.CodeRegion
import EvmAsm.Evm64.Environment.Assertion
import EvmAsm.Evm64.Memory
import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Abstract EVM execution status. Returned/reverted data is kept at byte
    granularity; later RETURN/REVERT slices can connect it to concrete memory
    slices. -/
inductive EvmStatus where
  | running
  | stopped
  | returned (data : List (BitVec 8))
  | reverted (data : List (BitVec 8))
  | error
  deriving DecidableEq, Repr

namespace EvmStatus

/-- Concrete status tag stored in the RV64 status register/cell. -/
def tag : EvmStatus → Word
  | running => 0
  | stopped => 1
  | returned _ => 2
  | reverted _ => 3
  | error => 4

theorem tag_running : tag running = 0 := rfl
theorem tag_stopped : tag stopped = 1 := rfl
theorem tag_returned (data : List (BitVec 8)) : tag (returned data) = 2 := rfl
theorem tag_reverted (data : List (BitVec 8)) : tag (reverted data) = 3 := rfl
theorem tag_error : tag error = 4 := rfl

end EvmStatus

/-- Pure EVM-level state seen by the interpreter. The bytecode itself is a list
    of bytes; the active memory contents use the existing dword-cell view from
    `Evm64/Memory.lean`. -/
structure EvmState where
  pc : Nat
  gas : Nat
  stack : List EvmWord
  memoryCells : Nat
  memory : Nat → Word
  memSize : Nat
  code : List (BitVec 8)
  codeLen : Nat
  env : EvmEnv
  status : EvmStatus

namespace EvmState

/-- Well-formed states keep the explicit code length in sync with the bytecode
    list. The assertion is intentionally separate so early handler specs can
    decide whether they need this pure side condition. -/
def codeLenMatches (state : EvmState) : Prop :=
  state.codeLen = state.code.length

def withPc (state : EvmState) (pc : Nat) : EvmState :=
  { state with pc := pc }

def withGas (state : EvmState) (gas : Nat) : EvmState :=
  { state with gas := gas }

/-- Pure precondition for charging `cost` gas from an EVM state. -/
def hasGas (state : EvmState) (cost : Nat) : Bool :=
  decide (cost ≤ state.gas)

/-- Charge gas with saturating Nat subtraction. Consumers that need an
    out-of-gas branch should use `chargeGas?`. -/
def chargeGas (state : EvmState) (cost : Nat) : EvmState :=
  withGas state (state.gas - cost)

/-- Charge gas only when enough gas is available. -/
def chargeGas? (state : EvmState) (cost : Nat) : Option EvmState :=
  if state.hasGas cost then
    some (state.chargeGas cost)
  else
    none

def withStack (state : EvmState) (stack : List EvmWord) : EvmState :=
  { state with stack := stack }

def withStatus (state : EvmState) (status : EvmStatus) : EvmState :=
  { state with status := status }

@[simp] theorem withPc_pc (state : EvmState) (pc : Nat) :
    (withPc state pc).pc = pc := rfl

@[simp] theorem withGas_gas (state : EvmState) (gas : Nat) :
    (withGas state gas).gas = gas := rfl

@[simp] theorem hasGas_zero (state : EvmState) :
    state.hasGas 0 = true := by
  simp [hasGas]

@[simp] theorem chargeGas_gas (state : EvmState) (cost : Nat) :
    (state.chargeGas cost).gas = state.gas - cost := rfl

@[simp] theorem chargeGas_pc (state : EvmState) (cost : Nat) :
    (state.chargeGas cost).pc = state.pc := rfl

@[simp] theorem chargeGas_status (state : EvmState) (cost : Nat) :
    (state.chargeGas cost).status = state.status := rfl

@[simp] theorem chargeGas_stack (state : EvmState) (cost : Nat) :
    (state.chargeGas cost).stack = state.stack := rfl

theorem chargeGas?_of_hasGas {state : EvmState} {cost : Nat}
    (h_gas : state.hasGas cost = true) :
    state.chargeGas? cost = some (state.chargeGas cost) := by
  simp [chargeGas?, h_gas]

theorem chargeGas?_of_not_hasGas {state : EvmState} {cost : Nat}
    (h_gas : state.hasGas cost = false) :
    state.chargeGas? cost = none := by
  simp [chargeGas?, h_gas]

@[simp] theorem withStack_stack (state : EvmState) (stack : List EvmWord) :
    (withStack state stack).stack = stack := rfl

@[simp] theorem withStatus_status (state : EvmState) (status : EvmStatus) :
    (withStatus state status).status = status := rfl

end EvmState

/-- Concrete RV64 placement of the abstract EVM state. The stack pointer itself
    remains the LP64/EVM convention register `x12`; the layout records the value
    that register should hold at the interpreter boundary. -/
structure EvmLayout where
  pcReg : Reg
  gasReg : Reg
  memBaseReg : Reg
  memSizeReg : Reg
  codeBaseReg : Reg
  codeLenReg : Reg
  envBaseReg : Reg
  statusReg : Reg
  stackPtr : Word
  memBase : Word
  memSizeLoc : Word
  codeBase : Word
  envBase : Word
  deriving Repr

/-- Composite EVM-state assertion for the interpreter loop. It packages scalar
    interpreter registers with the existing memory/code/environment/stack
    assertions, so opcode handlers can later frame and update one component at
    a time. -/
def evmStateIs (layout : EvmLayout) (state : EvmState) : Assertion :=
  (layout.pcReg ↦ᵣ BitVec.ofNat 64 state.pc) **
  (layout.gasReg ↦ᵣ BitVec.ofNat 64 state.gas) **
  (layout.memBaseReg ↦ᵣ layout.memBase) **
  (layout.memSizeReg ↦ᵣ layout.memSizeLoc) **
  (layout.codeBaseReg ↦ᵣ layout.codeBase) **
  (layout.codeLenReg ↦ᵣ BitVec.ofNat 64 state.codeLen) **
  (layout.envBaseReg ↦ᵣ layout.envBase) **
  (layout.statusReg ↦ᵣ state.status.tag) **
  (.x12 ↦ᵣ layout.stackPtr) **
  evmStackIs layout.stackPtr state.stack **
  evmMemIs layout.memBase state.memoryCells state.memory **
  evmMemSizeIs layout.memSizeLoc state.memSize **
  evmCodeIs layout.codeBase state.code **
  EvmEnv.envIs layout.envBase state.env

theorem evmStateIs_unfold (layout : EvmLayout) (state : EvmState) :
    evmStateIs layout state =
      ((layout.pcReg ↦ᵣ BitVec.ofNat 64 state.pc) **
       (layout.gasReg ↦ᵣ BitVec.ofNat 64 state.gas) **
       (layout.memBaseReg ↦ᵣ layout.memBase) **
       (layout.memSizeReg ↦ᵣ layout.memSizeLoc) **
       (layout.codeBaseReg ↦ᵣ layout.codeBase) **
       (layout.codeLenReg ↦ᵣ BitVec.ofNat 64 state.codeLen) **
       (layout.envBaseReg ↦ᵣ layout.envBase) **
       (layout.statusReg ↦ᵣ state.status.tag) **
       (.x12 ↦ᵣ layout.stackPtr) **
       evmStackIs layout.stackPtr state.stack **
       evmMemIs layout.memBase state.memoryCells state.memory **
       evmMemSizeIs layout.memSizeLoc state.memSize **
       evmCodeIs layout.codeBase state.code **
       EvmEnv.envIs layout.envBase state.env) := rfl

/-- Everything in `evmStateIs` except the scalar EVM PC register. -/
def evmStatePcRest (layout : EvmLayout) (state : EvmState) : Assertion :=
  (layout.gasReg ↦ᵣ BitVec.ofNat 64 state.gas) **
  (layout.memBaseReg ↦ᵣ layout.memBase) **
  (layout.memSizeReg ↦ᵣ layout.memSizeLoc) **
  (layout.codeBaseReg ↦ᵣ layout.codeBase) **
  (layout.codeLenReg ↦ᵣ BitVec.ofNat 64 state.codeLen) **
  (layout.envBaseReg ↦ᵣ layout.envBase) **
  (layout.statusReg ↦ᵣ state.status.tag) **
  (.x12 ↦ᵣ layout.stackPtr) **
  evmStackIs layout.stackPtr state.stack **
  evmMemIs layout.memBase state.memoryCells state.memory **
  evmMemSizeIs layout.memSizeLoc state.memSize **
  evmCodeIs layout.codeBase state.code **
  EvmEnv.envIs layout.envBase state.env

/-- Everything in `evmStateIs` except the scalar gas register. -/
def evmStateGasRest (layout : EvmLayout) (state : EvmState) : Assertion :=
  (layout.pcReg ↦ᵣ BitVec.ofNat 64 state.pc) **
  (layout.memBaseReg ↦ᵣ layout.memBase) **
  (layout.memSizeReg ↦ᵣ layout.memSizeLoc) **
  (layout.codeBaseReg ↦ᵣ layout.codeBase) **
  (layout.codeLenReg ↦ᵣ BitVec.ofNat 64 state.codeLen) **
  (layout.envBaseReg ↦ᵣ layout.envBase) **
  (layout.statusReg ↦ᵣ state.status.tag) **
  (.x12 ↦ᵣ layout.stackPtr) **
  evmStackIs layout.stackPtr state.stack **
  evmMemIs layout.memBase state.memoryCells state.memory **
  evmMemSizeIs layout.memSizeLoc state.memSize **
  evmCodeIs layout.codeBase state.code **
  EvmEnv.envIs layout.envBase state.env

/-- Everything in `evmStateIs` except the scalar status register. -/
def evmStateStatusRest (layout : EvmLayout) (state : EvmState) : Assertion :=
  (layout.pcReg ↦ᵣ BitVec.ofNat 64 state.pc) **
  (layout.gasReg ↦ᵣ BitVec.ofNat 64 state.gas) **
  (layout.memBaseReg ↦ᵣ layout.memBase) **
  (layout.memSizeReg ↦ᵣ layout.memSizeLoc) **
  (layout.codeBaseReg ↦ᵣ layout.codeBase) **
  (layout.codeLenReg ↦ᵣ BitVec.ofNat 64 state.codeLen) **
  (layout.envBaseReg ↦ᵣ layout.envBase) **
  (.x12 ↦ᵣ layout.stackPtr) **
  evmStackIs layout.stackPtr state.stack **
  evmMemIs layout.memBase state.memoryCells state.memory **
  evmMemSizeIs layout.memSizeLoc state.memSize **
  evmCodeIs layout.codeBase state.code **
  EvmEnv.envIs layout.envBase state.env

/-- Split out the PC register from the composite state assertion. -/
theorem evmStateIs_pc_split (layout : EvmLayout) (state : EvmState) :
    evmStateIs layout state =
      ((layout.pcReg ↦ᵣ BitVec.ofNat 64 state.pc) **
       evmStatePcRest layout state) := rfl

/-- Split out the gas register from the composite state assertion. -/
theorem evmStateIs_gas_split (layout : EvmLayout) (state : EvmState) :
    evmStateIs layout state =
      ((layout.gasReg ↦ᵣ BitVec.ofNat 64 state.gas) **
       evmStateGasRest layout state) := by
  unfold evmStateIs evmStateGasRest
  ac_rfl

/-- Split out the status register from the composite state assertion. -/
theorem evmStateIs_status_split (layout : EvmLayout) (state : EvmState) :
    evmStateIs layout state =
      ((layout.statusReg ↦ᵣ state.status.tag) **
       evmStateStatusRest layout state) := by
  unfold evmStateIs evmStateStatusRest
  ac_rfl

theorem pcFree_evmStatePcRest {layout : EvmLayout} {state : EvmState} :
    (evmStatePcRest layout state).pcFree := by
  unfold evmStatePcRest
  pcFree

theorem pcFree_evmStateGasRest {layout : EvmLayout} {state : EvmState} :
    (evmStateGasRest layout state).pcFree := by
  unfold evmStateGasRest
  pcFree

theorem pcFree_evmStateStatusRest {layout : EvmLayout} {state : EvmState} :
    (evmStateStatusRest layout state).pcFree := by
  unfold evmStateStatusRest
  pcFree

theorem pcFree_evmStateIs {layout : EvmLayout} {state : EvmState} :
    (evmStateIs layout state).pcFree := by
  unfold evmStateIs
  pcFree

instance (layout : EvmLayout) (state : EvmState) :
    Assertion.PCFree (evmStatePcRest layout state) :=
  ⟨pcFree_evmStatePcRest⟩

instance (layout : EvmLayout) (state : EvmState) :
    Assertion.PCFree (evmStateGasRest layout state) :=
  ⟨pcFree_evmStateGasRest⟩

instance (layout : EvmLayout) (state : EvmState) :
    Assertion.PCFree (evmStateStatusRest layout state) :=
  ⟨pcFree_evmStateStatusRest⟩

instance (layout : EvmLayout) (state : EvmState) :
    Assertion.PCFree (evmStateIs layout state) :=
  ⟨pcFree_evmStateIs⟩

end EvmAsm.Evm64
