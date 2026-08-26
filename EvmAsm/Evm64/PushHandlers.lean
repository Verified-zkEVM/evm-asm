/-
  EvmAsm.Evm64.PushHandlers

  Pure PUSH1-32 handler entries for the interpreter handler table
  (GH #101 / GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable
public import EvmAsm.Evm64.Push.ExecEffect

@[expose] public section

namespace EvmAsm.Evm64

namespace PushHandlers

/-- PUSHn handler over the abstract interpreter state. The handler uses the
    executable PUSH immediate bridge and advances the EVM PC by 1+n. -/
def pushHandler (n : Nat) : OpcodeHandler :=
  fun state =>
    (state.withPc
      (PushExecEffect.pcAfterPushFromCode state.code state.pc n)).withStack
      (PushExecEffect.stackAfterPush state.code state.pc n state.stack)

/-- Lookup surface for generic PUSH1-32 handlers. Invalid widths stay
    unimplemented rather than installing nonsensical handlers. -/
def pushHandler? : EvmOpcode → Option OpcodeHandler
  | .PUSH n =>
      if EvmOpcode.validPushWidth n then
        some (pushHandler n)
      else
        none
  | _ => none

/-- Handler table containing the generic PUSH1-32 entries.
    Distinctive token: PushHandlers.pushHandlerTable #101 #107. -/
def pushHandlerTable : HandlerTable :=
  pushHandler?

@[simp] theorem pushHandlerTable_eq :
    pushHandlerTable = pushHandler? := rfl

theorem pushHandler?_PUSH_of_valid {n : Nat}
    (h_valid : EvmOpcode.validPushWidth n = true) :
    pushHandler? (.PUSH n) = some (pushHandler n) := by
  simp [pushHandler?, h_valid]

theorem pushHandler?_PUSH_of_invalid {n : Nat}
    (h_valid : EvmOpcode.validPushWidth n = false) :
    pushHandler? (.PUSH n) = none := by
  simp [pushHandler?, h_valid]

@[simp] theorem eq_pushHandler_iff (n : Nat) (handler : OpcodeHandler) :
    pushHandler n = handler ↔ handler = pushHandler n := by
  constructor <;> intro h_eq <;> exact h_eq.symm

theorem pushHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    pushHandler? opcode = some handler ↔
      ∃ n, opcode = .PUSH n ∧ EvmOpcode.validPushWidth n = true ∧
        handler = pushHandler n := by
  cases opcode <;> simp [pushHandler?]

theorem pushHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    pushHandler? opcode = none ↔
      ∀ n, opcode = .PUSH n → EvmOpcode.validPushWidth n = false := by
  cases opcode <;> simp [pushHandler?]

@[simp] theorem pushHandler_stack (n : Nat) (state : EvmState) :
    (pushHandler n state).stack =
      PushExecEffect.stackAfterPush state.code state.pc n state.stack := rfl

@[simp] theorem pushHandler_pc (n : Nat) (state : EvmState) :
    (pushHandler n state).pc =
      PushExecEffect.pcAfterPushFromCode state.code state.pc n := rfl

@[simp] theorem pushHandler_status (n : Nat) (state : EvmState) :
    (pushHandler n state).status = state.status := rfl

theorem pushHandler_stack_eq
    (n : Nat) (state : EvmState) :
    (pushHandler n state).stack =
      PushExecEffect.pushedWordFromCode state.code state.pc n :: state.stack := rfl

theorem pushHandler_pc_eq
    (n : Nat) (state : EvmState) :
    (pushHandler n state).pc = state.pc + 1 + n := rfl

/--
The pure PUSH handler updates the interpreter state with the same stack and
program-counter components as the bundled executable PUSH effect.

Distinctive token:
PushHandlers.pushHandler_eq_effectFromCode #101 #107.
-/
theorem pushHandler_eq_effectFromCode
    (n : Nat) (state : EvmState) :
    (pushHandler n state).pc =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).pc ∧
      (pushHandler n state).stack =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).stack := by
  constructor <;> rfl

theorem dispatchOpcode?_pushHandlerTable_PUSH_of_valid
    {n : Nat} (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    HandlerTable.dispatchOpcode? pushHandlerTable (.PUSH n) state =
      some (pushHandler n state) := by
  exact HandlerTable.dispatchOpcode?_some
    (pushHandler?_PUSH_of_valid h_valid) state

theorem dispatchOpcode_pushHandlerTable_PUSH_of_valid
    {n : Nat} (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    HandlerTable.dispatchOpcode pushHandlerTable (.PUSH n) state =
      pushHandler n state := by
  exact HandlerTable.dispatchOpcode_some
    (pushHandler?_PUSH_of_valid h_valid) state

theorem dispatchOpcode_pushHandlerTable_PUSH_of_valid_status
    {n : Nat} (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    (HandlerTable.dispatchOpcode pushHandlerTable (.PUSH n) state).status =
      state.status := by
  rw [dispatchOpcode_pushHandlerTable_PUSH_of_valid h_valid state]
  exact pushHandler_status n state

end PushHandlers

end EvmAsm.Evm64
