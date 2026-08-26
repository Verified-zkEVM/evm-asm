/-
  EvmAsm.Evm64.HandlerTableCompose

  Composition helpers for pure opcode handler tables (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable

@[expose] public section

namespace EvmAsm.Evm64

namespace HandlerTable

/--
Left-biased composition of independently verified handler tables.

Distinctive token: HandlerTableCompose.orElse #107.
-/
def orElse (left right : HandlerTable) : HandlerTable :=
  fun opcode =>
    match left opcode with
    | some handler => some handler
    | none => right opcode

@[simp] theorem orElse_left_some
    {left right : HandlerTable} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_left : left opcode = some handler) :
    orElse left right opcode = some handler := by
  simp [orElse, h_left]

@[simp] theorem orElse_left_none
    {left right : HandlerTable} {opcode : EvmOpcode}
    (h_left : left opcode = none) :
    orElse left right opcode = right opcode := by
  simp [orElse, h_left]

@[simp] theorem orElse_empty_left (right : HandlerTable) :
    orElse empty right = right := by
  funext opcode
  simp [orElse]

theorem orElse_empty_right_apply (left : HandlerTable) (opcode : EvmOpcode) :
    orElse left empty opcode = left opcode := by
  cases h_left : left opcode with
  | none => simp [orElse, h_left]
  | some handler => simp [orElse, h_left]

@[simp] theorem orElse_empty_right (left : HandlerTable) :
    orElse left empty = left := by
  funext opcode
  exact orElse_empty_right_apply left opcode

theorem dispatchOpcode?_orElse_left
    {left right : HandlerTable} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_left : left opcode = some handler) (state : EvmState) :
    dispatchOpcode? (orElse left right) opcode state = some (handler state) := by
  simp [dispatchOpcode?, h_left]

theorem dispatchOpcode?_orElse_right
    {left right : HandlerTable} {opcode : EvmOpcode}
    (h_left : left opcode = none) (state : EvmState) :
    dispatchOpcode? (orElse left right) opcode state =
      dispatchOpcode? right opcode state := by
  simp [dispatchOpcode?, h_left]

theorem dispatchOpcode_orElse_left
    {left right : HandlerTable} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_left : left opcode = some handler) (state : EvmState) :
    dispatchOpcode (orElse left right) opcode state = handler state := by
  simp [dispatchOpcode, dispatchOpcode?_orElse_left h_left state]

theorem dispatchOpcode_orElse_left_status
    {left right : HandlerTable} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_left : left opcode = some handler) (state : EvmState) :
    (dispatchOpcode (orElse left right) opcode state).status =
      (handler state).status := by
  rw [dispatchOpcode_orElse_left h_left state]

theorem dispatchOpcode_orElse_left_preserves_status
    {left right : HandlerTable} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_left : left opcode = some handler)
    (h_status : ∀ state : EvmState, (handler state).status = state.status)
    (state : EvmState) :
    (dispatchOpcode (orElse left right) opcode state).status =
      state.status := by
  rw [dispatchOpcode_orElse_left_status h_left state]
  exact h_status state

theorem dispatchOpcode_orElse_left_preserves_codeLenMatches
    {left right : HandlerTable} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_left : left opcode = some handler)
    (h_codeLen : ∀ state : EvmState,
      state.codeLenMatches → (handler state).codeLenMatches)
    (state : EvmState) (h_state : state.codeLenMatches) :
    (dispatchOpcode (orElse left right) opcode state).codeLenMatches := by
  rw [dispatchOpcode_orElse_left h_left state]
  exact h_codeLen state h_state

theorem dispatchOpcode_orElse_right
    {left right : HandlerTable} {opcode : EvmOpcode}
    (h_left : left opcode = none) (state : EvmState) :
    dispatchOpcode (orElse left right) opcode state =
      dispatchOpcode right opcode state := by
  simp [dispatchOpcode, dispatchOpcode?_orElse_right h_left state]

theorem dispatchOpcode_orElse_right_status
    {left right : HandlerTable} {opcode : EvmOpcode}
    (h_left : left opcode = none) (state : EvmState) :
    (dispatchOpcode (orElse left right) opcode state).status =
      (dispatchOpcode right opcode state).status := by
  rw [dispatchOpcode_orElse_right h_left state]

theorem dispatchOpcode_orElse_right_preserves_status
    {left right : HandlerTable} {opcode : EvmOpcode}
    (h_left : left opcode = none)
    (h_status :
      ∀ state : EvmState,
        (dispatchOpcode right opcode state).status = state.status)
    (state : EvmState) :
    (dispatchOpcode (orElse left right) opcode state).status =
      state.status := by
  rw [dispatchOpcode_orElse_right_status h_left state]
  exact h_status state

theorem dispatchOpcode_orElse_right_preserves_codeLenMatches
    {left right : HandlerTable} {opcode : EvmOpcode}
    (h_left : left opcode = none)
    (h_codeLen :
      ∀ state : EvmState,
        state.codeLenMatches →
          (dispatchOpcode right opcode state).codeLenMatches)
    (state : EvmState) (h_state : state.codeLenMatches) :
    (dispatchOpcode (orElse left right) opcode state).codeLenMatches := by
  rw [dispatchOpcode_orElse_right h_left state]
  exact h_codeLen state h_state

theorem dispatchOpcode_orElse_none
    {left right : HandlerTable} {opcode : EvmOpcode}
    (h_left : left opcode = none) (h_right : right opcode = none)
    (state : EvmState) :
    dispatchOpcode (orElse left right) opcode state = state.invalid := by
  rw [dispatchOpcode_orElse_right h_left state]
  exact dispatchOpcode_none h_right state

theorem dispatchOpcode_orElse_none_status
    {left right : HandlerTable} {opcode : EvmOpcode}
    (h_left : left opcode = none) (h_right : right opcode = none)
    (state : EvmState) :
    (dispatchOpcode (orElse left right) opcode state).status = .error := by
  rw [dispatchOpcode_orElse_none h_left h_right state]
  exact EvmState.invalid_status state

/-- Lookup-result characterization of `orElse` returning `some`. The combined
    table delegates to the right operand only when the left operand has no
    entry, so a `some handler` result decomposes into "left owns it" or
    "left misses and right owns it".

    Distinctive token: `HandlerTable.orElse_eq_some_iff #107`. -/
theorem orElse_eq_some_iff
    {left right : HandlerTable} {opcode : EvmOpcode} {handler : OpcodeHandler} :
    orElse left right opcode = some handler ↔
      left opcode = some handler ∨
        (left opcode = none ∧ right opcode = some handler) := by
  unfold orElse
  cases h_left : left opcode with
  | none => simp
  | some h => simp

/-- Lookup-result characterization of `orElse` returning `none`. The combined
    table is undefined at `opcode` exactly when both operands are.

    Distinctive token: `HandlerTable.orElse_eq_none_iff #107`. -/
theorem orElse_eq_none_iff
    {left right : HandlerTable} {opcode : EvmOpcode} :
    orElse left right opcode = none ↔
      left opcode = none ∧ right opcode = none := by
  unfold orElse
  cases h_left : left opcode with
  | none => simp
  | some h => simp

end HandlerTable

end EvmAsm.Evm64
