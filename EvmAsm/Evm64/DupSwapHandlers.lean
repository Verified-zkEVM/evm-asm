/-
  EvmAsm.Evm64.DupSwapHandlers

  Generic pure handler-table entries for DUP1-16 and SWAP1-16 (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable

@[expose] public section

namespace EvmAsm.Evm64
namespace DupSwapHandlers

open EvmOpcode

/-- Pure stack transform for DUPn. The index is the EVM opcode suffix, so
    `n = 1` duplicates the stack head. -/
def dupStack? (n : Nat) (stack : List EvmWord) : Option (List EvmWord) :=
  match stack[n - 1]? with
  | some word => some (word :: stack)
  | none => none

/-- Replace the zero-based slot in a tail list, returning the replaced value
    and the updated tail. Used by SWAPn after peeling the stack head. -/
def replaceAt? : Nat → EvmWord → List EvmWord → Option (EvmWord × List EvmWord)
  | 0, new, old :: tail => some (old, new :: tail)
  | slot + 1, new, old :: tail =>
      match replaceAt? slot new tail with
      | some (target, tail') => some (target, old :: tail')
      | none => none
  | _, _, [] => none

/-- Pure stack transform for SWAPn. The index is the EVM opcode suffix, so
    `n = 1` swaps the top two stack items. -/
def swapStack? (n : Nat) (stack : List EvmWord) : Option (List EvmWord) :=
  match stack with
  | top :: rest =>
      match replaceAt? (n - 1) top rest with
      | some (target, rest') => some (target :: rest')
      | none => none
  | [] => none

/-- DUPn handler over the abstract interpreter state. Stack underflow marks the
    state invalid; gas/pc charging belongs to the later executable wrapper. -/
def dupHandler (n : Nat) : OpcodeHandler :=
  fun state =>
    match dupStack? n state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid

/-- SWAPn handler over the abstract interpreter state. Stack underflow marks the
    state invalid; gas/pc charging belongs to the later executable wrapper. -/
def swapHandler (n : Nat) : OpcodeHandler :=
  fun state =>
    match swapStack? n state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid

/-- Lookup surface for generic DUP/SWAP handlers. Invalid parameterized opcode
    values stay unimplemented rather than silently installing nonsensical
    handlers. -/
def dupSwapHandler? : EvmOpcode → Option OpcodeHandler
  | .DUP n =>
      if EvmOpcode.validDupIndex n then
        some (dupHandler n)
      else
        none
  | .SWAP n =>
      if EvmOpcode.validSwapIndex n then
        some (swapHandler n)
      else
        none
  | _ => none

/-- Handler table containing the generic DUP1-16 and SWAP1-16 entries.
    Distinctive token: DupSwapHandlers.dupSwapHandlerTable #107. -/
def dupSwapHandlerTable : HandlerTable :=
  dupSwapHandler?

@[simp] theorem dupStack?_one (word : EvmWord) (stack : List EvmWord) :
    dupStack? 1 (word :: stack) = some (word :: word :: stack) := rfl

@[simp] theorem swapStack?_one
    (top next : EvmWord) (stack : List EvmWord) :
    swapStack? 1 (top :: next :: stack) = some (next :: top :: stack) := rfl

@[simp] theorem replaceAt?_zero
    (new old : EvmWord) (tail : List EvmWord) :
    replaceAt? 0 new (old :: tail) = some (old, new :: tail) := rfl

theorem dupStack?_eq_some_iff
    (n : Nat) (stack stack' : List EvmWord) :
    dupStack? n stack = some stack' ↔
      ∃ word, stack[n - 1]? = some word ∧ stack' = word :: stack := by
  constructor
  · intro h_stack
    cases h_word : stack[n - 1]? with
    | none =>
        simp [dupStack?, h_word] at h_stack
    | some word =>
        simp [dupStack?, h_word] at h_stack
        exact ⟨word, rfl, h_stack.symm⟩
  · rintro ⟨word, h_word, rfl⟩
    simp [dupStack?, h_word]

theorem dupStack?_eq_none_iff
    (n : Nat) (stack : List EvmWord) :
    dupStack? n stack = none ↔ stack[n - 1]? = none := by
  cases h_word : stack[n - 1]? with
  | none =>
      simp [dupStack?, h_word]
  | some word =>
      simp [dupStack?, h_word]

theorem swapStack?_eq_some_iff
    (n : Nat) (stack stack' : List EvmWord) :
    swapStack? n stack = some stack' ↔
      ∃ top rest target rest',
        stack = top :: rest ∧
        replaceAt? (n - 1) top rest = some (target, rest') ∧
        stack' = target :: rest' := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        simp [swapStack?] at h_stack
    | cons top rest =>
        cases h_replace : replaceAt? (n - 1) top rest with
        | none =>
            simp [swapStack?, h_replace] at h_stack
        | some result =>
            obtain ⟨target, rest'⟩ := result
            simp [swapStack?, h_replace] at h_stack
            exact ⟨top, rest, target, rest', rfl, h_replace, h_stack.symm⟩
  · rintro ⟨top, rest, target, rest', rfl, h_replace, rfl⟩
    simp [swapStack?, h_replace]

theorem swapStack?_eq_none_iff
    (n : Nat) (stack : List EvmWord) :
    swapStack? n stack = none ↔
      stack = [] ∨
        ∃ top rest, stack = top :: rest ∧
          replaceAt? (n - 1) top rest = none := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        exact Or.inl rfl
    | cons top rest =>
        right
        cases h_replace : replaceAt? (n - 1) top rest with
        | none =>
            exact ⟨top, rest, rfl, h_replace⟩
        | some result =>
            simp [swapStack?, h_replace] at h_stack
  · rintro (rfl | ⟨top, rest, rfl, h_replace⟩)
    · simp [swapStack?]
    · simp [swapStack?, h_replace]

@[simp] theorem dupSwapHandlerTable_eq :
    dupSwapHandlerTable = dupSwapHandler? := rfl

theorem dupSwapHandler?_DUP_of_valid {n : Nat}
    (h_valid : EvmOpcode.validDupIndex n = true) :
    dupSwapHandler? (.DUP n) = some (dupHandler n) := by
  simp [dupSwapHandler?, h_valid]

theorem dupSwapHandler?_DUP_of_invalid {n : Nat}
    (h_valid : EvmOpcode.validDupIndex n = false) :
    dupSwapHandler? (.DUP n) = none := by
  simp [dupSwapHandler?, h_valid]

theorem dupSwapHandler?_SWAP_of_valid {n : Nat}
    (h_valid : EvmOpcode.validSwapIndex n = true) :
    dupSwapHandler? (.SWAP n) = some (swapHandler n) := by
  simp [dupSwapHandler?, h_valid]

theorem dupSwapHandler?_SWAP_of_invalid {n : Nat}
    (h_valid : EvmOpcode.validSwapIndex n = false) :
    dupSwapHandler? (.SWAP n) = none := by
  simp [dupSwapHandler?, h_valid]

@[simp] theorem eq_dupHandler_iff (n : Nat) (handler : OpcodeHandler) :
    dupHandler n = handler ↔ handler = dupHandler n := by
  constructor <;> intro h_eq <;> exact h_eq.symm

@[simp] theorem eq_swapHandler_iff (n : Nat) (handler : OpcodeHandler) :
    swapHandler n = handler ↔ handler = swapHandler n := by
  constructor <;> intro h_eq <;> exact h_eq.symm

theorem dupSwapHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    dupSwapHandler? opcode = some handler ↔
      (∃ n, opcode = .DUP n ∧ EvmOpcode.validDupIndex n = true ∧
        handler = dupHandler n) ∨
        (∃ n, opcode = .SWAP n ∧ EvmOpcode.validSwapIndex n = true ∧
          handler = swapHandler n) := by
  cases opcode <;> simp [dupSwapHandler?]

theorem dupSwapHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    dupSwapHandler? opcode = none ↔
      (∀ n, opcode = .DUP n → EvmOpcode.validDupIndex n = false) ∧
        (∀ n, opcode = .SWAP n → EvmOpcode.validSwapIndex n = false) := by
  cases opcode <;> simp [dupSwapHandler?]

theorem dupHandler_stack_of_dupStack?_some
    {n : Nat} {state : EvmState} {stack' : List EvmWord}
    (h_stack : dupStack? n state.stack = some stack') :
    (dupHandler n state).stack = stack' := by
  simp [dupHandler, h_stack]

theorem swapHandler_stack_of_swapStack?_some
    {n : Nat} {state : EvmState} {stack' : List EvmWord}
    (h_stack : swapStack? n state.stack = some stack') :
    (swapHandler n state).stack = stack' := by
  simp [swapHandler, h_stack]

theorem dupHandler_status_of_dupStack?_none
    {n : Nat} {state : EvmState}
    (h_stack : dupStack? n state.stack = none) :
    (dupHandler n state).status = .error := by
  simp [dupHandler, h_stack]

theorem swapHandler_status_of_swapStack?_none
    {n : Nat} {state : EvmState}
    (h_stack : swapStack? n state.stack = none) :
    (swapHandler n state).status = .error := by
  simp [swapHandler, h_stack]

theorem dispatchOpcode_dupSwapHandlerTable_DUP_of_valid
    {n : Nat} (h_valid : EvmOpcode.validDupIndex n = true)
    (state : EvmState) :
    HandlerTable.dispatchOpcode dupSwapHandlerTable (.DUP n) state =
      dupHandler n state := by
  exact HandlerTable.dispatchOpcode_some
    (dupSwapHandler?_DUP_of_valid h_valid) state

theorem dispatchOpcode_dupSwapHandlerTable_SWAP_of_valid
    {n : Nat} (h_valid : EvmOpcode.validSwapIndex n = true)
    (state : EvmState) :
    HandlerTable.dispatchOpcode dupSwapHandlerTable (.SWAP n) state =
      swapHandler n state := by
  exact HandlerTable.dispatchOpcode_some
    (dupSwapHandler?_SWAP_of_valid h_valid) state

theorem dispatchOpcode_dupSwapHandlerTable_DUP_of_valid_status_of_some
    {n : Nat} (h_valid : EvmOpcode.validDupIndex n = true)
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : dupStack? n state.stack = some stack') :
    (HandlerTable.dispatchOpcode dupSwapHandlerTable (.DUP n) state).status =
      state.status := by
  rw [dispatchOpcode_dupSwapHandlerTable_DUP_of_valid h_valid state]
  simp [dupHandler, h_stack, EvmState.withStack]

theorem dispatchOpcode_dupSwapHandlerTable_SWAP_of_valid_status_of_some
    {n : Nat} (h_valid : EvmOpcode.validSwapIndex n = true)
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : swapStack? n state.stack = some stack') :
    (HandlerTable.dispatchOpcode dupSwapHandlerTable (.SWAP n) state).status =
      state.status := by
  rw [dispatchOpcode_dupSwapHandlerTable_SWAP_of_valid h_valid state]
  simp [swapHandler, h_stack, EvmState.withStack]

theorem dispatchOpcode?_dupSwapHandlerTable_DUP_of_valid
    {n : Nat} (h_valid : EvmOpcode.validDupIndex n = true)
    (state : EvmState) :
    HandlerTable.dispatchOpcode? dupSwapHandlerTable (.DUP n) state =
      some (dupHandler n state) := by
  exact HandlerTable.dispatchOpcode?_some
    (dupSwapHandler?_DUP_of_valid h_valid) state

theorem dispatchOpcode?_dupSwapHandlerTable_SWAP_of_valid
    {n : Nat} (h_valid : EvmOpcode.validSwapIndex n = true)
    (state : EvmState) :
    HandlerTable.dispatchOpcode? dupSwapHandlerTable (.SWAP n) state =
      some (swapHandler n state) := by
  exact HandlerTable.dispatchOpcode?_some
    (dupSwapHandler?_SWAP_of_valid h_valid) state

end DupSwapHandlers
end EvmAsm.Evm64
