/-
  EvmAsm.Evm64.ControlHandlers

  Pure PC/GAS/JUMPDEST handler entries for the interpreter handler table
  (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable

@[expose] public section

namespace EvmAsm.Evm64

namespace ControlHandlers

/-- EVM word pushed by the PC opcode for the current abstract state. -/
def pcWord (state : EvmState) : EvmWord :=
  BitVec.ofNat 256 state.pc

/-- EVM word pushed by the GAS opcode for the current abstract state. -/
def gasWord (state : EvmState) : EvmWord :=
  BitVec.ofNat 256 state.gas

/-- PC pushes the current EVM program counter. -/
def pcHandler : OpcodeHandler :=
  fun state => state.withStack (pcWord state :: state.stack)

/-- GAS pushes the current remaining-gas counter. -/
def gasHandler : OpcodeHandler :=
  fun state => state.withStack (gasWord state :: state.stack)

/-- JUMPDEST is a marker opcode and leaves the abstract state unchanged. -/
def jumpdestHandler : OpcodeHandler :=
  fun state => state

/-- Lookup just the control/metadata handlers introduced in this slice. -/
def controlHandler? : EvmOpcode → Option OpcodeHandler
  | .PC => some pcHandler
  | .GAS => some gasHandler
  | .JUMPDEST => some jumpdestHandler
  | _ => none

@[simp] theorem eq_pcHandler_iff (handler : OpcodeHandler) :
    pcHandler = handler ↔ handler = pcHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm

@[simp] theorem eq_gasHandler_iff (handler : OpcodeHandler) :
    gasHandler = handler ↔ handler = gasHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm

@[simp] theorem eq_jumpdestHandler_iff (handler : OpcodeHandler) :
    jumpdestHandler = handler ↔ handler = jumpdestHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm

/-- Handler table fragment containing PC, GAS, and JUMPDEST entries.
    Distinctive token: ControlHandlers.controlHandlerTable #107. -/
def controlHandlerTable : HandlerTable :=
  controlHandler?

@[simp] theorem controlHandler?_PC :
    controlHandler? .PC = some pcHandler := rfl

@[simp] theorem controlHandler?_GAS :
    controlHandler? .GAS = some gasHandler := rfl

@[simp] theorem controlHandler?_JUMPDEST :
    controlHandler? .JUMPDEST = some jumpdestHandler := rfl

theorem controlHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    controlHandler? opcode = some handler ↔
      (opcode = .PC ∧ handler = pcHandler) ∨
        (opcode = .GAS ∧ handler = gasHandler) ∨
          (opcode = .JUMPDEST ∧ handler = jumpdestHandler) := by
  cases opcode <;> simp [controlHandler?]

theorem controlHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    controlHandler? opcode = none ↔
      opcode ≠ .PC ∧ opcode ≠ .GAS ∧ opcode ≠ .JUMPDEST := by
  cases opcode <;> simp [controlHandler?]

@[simp] theorem pcHandler_stack (state : EvmState) :
    (pcHandler state).stack = pcWord state :: state.stack := rfl

@[simp] theorem gasHandler_stack (state : EvmState) :
    (gasHandler state).stack = gasWord state :: state.stack := rfl

@[simp] theorem jumpdestHandler_eq (state : EvmState) :
    jumpdestHandler state = state := rfl

@[simp] theorem pcHandler_status (state : EvmState) :
    (pcHandler state).status = state.status := rfl

@[simp] theorem gasHandler_status (state : EvmState) :
    (gasHandler state).status = state.status := rfl

@[simp] theorem controlHandlerTable_PC :
    controlHandlerTable .PC = some pcHandler := rfl

@[simp] theorem controlHandlerTable_GAS :
    controlHandlerTable .GAS = some gasHandler := rfl

@[simp] theorem controlHandlerTable_JUMPDEST :
    controlHandlerTable .JUMPDEST = some jumpdestHandler := rfl

@[simp] theorem dispatchOpcode?_controlHandlerTable_PC (state : EvmState) :
    HandlerTable.dispatchOpcode? controlHandlerTable .PC state =
      some (pcHandler state) := by
  simp [HandlerTable.dispatchOpcode?]

@[simp] theorem dispatchOpcode_controlHandlerTable_PC (state : EvmState) :
    HandlerTable.dispatchOpcode controlHandlerTable .PC state =
      pcHandler state := by
  simp [HandlerTable.dispatchOpcode]

@[simp] theorem dispatchOpcode?_controlHandlerTable_GAS (state : EvmState) :
    HandlerTable.dispatchOpcode? controlHandlerTable .GAS state =
      some (gasHandler state) := by
  simp [HandlerTable.dispatchOpcode?]

@[simp] theorem dispatchOpcode_controlHandlerTable_GAS (state : EvmState) :
    HandlerTable.dispatchOpcode controlHandlerTable .GAS state =
      gasHandler state := by
  simp [HandlerTable.dispatchOpcode]

@[simp] theorem dispatchOpcode?_controlHandlerTable_JUMPDEST (state : EvmState) :
    HandlerTable.dispatchOpcode? controlHandlerTable .JUMPDEST state =
      some (jumpdestHandler state) := by
  simp [HandlerTable.dispatchOpcode?]

@[simp] theorem dispatchOpcode_controlHandlerTable_JUMPDEST (state : EvmState) :
    HandlerTable.dispatchOpcode controlHandlerTable .JUMPDEST state =
      jumpdestHandler state := by
  simp [HandlerTable.dispatchOpcode]

theorem dispatchOpcode_controlHandlerTable_PC_status (state : EvmState) :
    (HandlerTable.dispatchOpcode controlHandlerTable .PC state).status =
      state.status := by
  rw [dispatchOpcode_controlHandlerTable_PC state]
  exact pcHandler_status state

theorem dispatchOpcode_controlHandlerTable_GAS_status (state : EvmState) :
    (HandlerTable.dispatchOpcode controlHandlerTable .GAS state).status =
      state.status := by
  rw [dispatchOpcode_controlHandlerTable_GAS state]
  exact gasHandler_status state

theorem dispatchOpcode_controlHandlerTable_JUMPDEST_status (state : EvmState) :
    (HandlerTable.dispatchOpcode controlHandlerTable .JUMPDEST state).status =
      state.status := by
  rw [dispatchOpcode_controlHandlerTable_JUMPDEST state]
  rfl

end ControlHandlers

end EvmAsm.Evm64
