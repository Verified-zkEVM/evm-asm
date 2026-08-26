/-
  EvmAsm.Evm64.ComparisonHandlers

  Pure handler-table entries for comparison opcodes (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable

@[expose] public section

namespace EvmAsm.Evm64
namespace ComparisonHandlers

/-- Convert a comparison flag to the EVM 0/1 word result. -/
def boolWord (p : Bool) : EvmWord :=
  if p then 1 else 0

/-- Pure stack transform for binary comparison opcodes. -/
def binaryStack? (cmp : EvmWord → EvmWord → Bool)
    (stack : List EvmWord) : Option (List EvmWord) :=
  match stack with
  | a :: b :: rest => some (boolWord (cmp a b) :: rest)
  | _ => none

/-- Pure stack transform for unary comparison opcodes. -/
def unaryStack? (cmp : EvmWord → Bool)
    (stack : List EvmWord) : Option (List EvmWord) :=
  match stack with
  | a :: rest => some (boolWord (cmp a) :: rest)
  | [] => none

def binaryHandler (cmp : EvmWord → EvmWord → Bool) : OpcodeHandler :=
  fun state =>
    match binaryStack? cmp state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid

def unaryHandler (cmp : EvmWord → Bool) : OpcodeHandler :=
  fun state =>
    match unaryStack? cmp state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid

def ltHandler : OpcodeHandler :=
  binaryHandler BitVec.ult

def gtHandler : OpcodeHandler :=
  binaryHandler (fun a b => BitVec.ult b a)

def sltHandler : OpcodeHandler :=
  binaryHandler BitVec.slt

def sgtHandler : OpcodeHandler :=
  binaryHandler (fun a b => BitVec.slt b a)

def eqHandler : OpcodeHandler :=
  binaryHandler (fun a b => decide (a = b))

def iszeroHandler : OpcodeHandler :=
  unaryHandler (fun a => decide (a = 0))

/-- Lookup surface for comparison handlers. -/
def comparisonHandler? : EvmOpcode → Option OpcodeHandler
  | .LT => some ltHandler
  | .GT => some gtHandler
  | .SLT => some sltHandler
  | .SGT => some sgtHandler
  | .EQ => some eqHandler
  | .ISZERO => some iszeroHandler
  | _ => none

/-- Handler table containing LT/GT/SLT/SGT/EQ/ISZERO entries.
    Distinctive token: ComparisonHandlers.comparisonHandlerTable #107. -/
def comparisonHandlerTable : HandlerTable :=
  comparisonHandler?

@[simp] theorem boolWord_true : boolWord true = 1 := rfl

@[simp] theorem boolWord_false : boolWord false = 0 := rfl

@[simp] theorem binaryStack?_two
    (cmp : EvmWord → EvmWord → Bool)
    (a b : EvmWord) (rest : List EvmWord) :
    binaryStack? cmp (a :: b :: rest) = some (boolWord (cmp a b) :: rest) :=
  rfl

@[simp] theorem unaryStack?_one
    (cmp : EvmWord → Bool)
    (a : EvmWord) (rest : List EvmWord) :
    unaryStack? cmp (a :: rest) = some (boolWord (cmp a) :: rest) := rfl

@[simp] theorem binaryStack?_nil
    (cmp : EvmWord → EvmWord → Bool) :
    binaryStack? cmp [] = none := rfl

@[simp] theorem unaryStack?_nil
    (cmp : EvmWord → Bool) :
    unaryStack? cmp [] = none := rfl

theorem binaryStack?_eq_some_iff
    (cmp : EvmWord → EvmWord → Bool) (stack stack' : List EvmWord) :
    binaryStack? cmp stack = some stack' ↔
      ∃ a b rest, stack = a :: b :: rest ∧
        stack' = boolWord (cmp a b) :: rest := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        simp [binaryStack?] at h_stack
    | cons a stackTail =>
        cases stackTail with
        | nil =>
            simp [binaryStack?] at h_stack
        | cons b rest =>
            simp [binaryStack?] at h_stack
            exact ⟨a, b, rest, rfl, h_stack.symm⟩
  · rintro ⟨a, b, rest, rfl, rfl⟩
    simp [binaryStack?]

theorem binaryStack?_eq_none_iff
    (cmp : EvmWord → EvmWord → Bool) (stack : List EvmWord) :
    binaryStack? cmp stack = none ↔ stack.length < 2 := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        simp
    | cons a stackTail =>
        cases stackTail with
        | nil =>
            simp
        | cons b rest =>
            simp [binaryStack?] at h_stack
  · intro h_len
    cases stack with
    | nil =>
        simp [binaryStack?]
    | cons a stackTail =>
        cases stackTail with
        | nil =>
            simp [binaryStack?]
        | cons b rest =>
            exfalso
            simp at h_len
            omega

theorem unaryStack?_eq_some_iff
    (cmp : EvmWord → Bool) (stack stack' : List EvmWord) :
    unaryStack? cmp stack = some stack' ↔
      ∃ a rest, stack = a :: rest ∧ stack' = boolWord (cmp a) :: rest := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        simp [unaryStack?] at h_stack
    | cons a rest =>
        simp [unaryStack?] at h_stack
        exact ⟨a, rest, rfl, h_stack.symm⟩
  · rintro ⟨a, rest, rfl, rfl⟩
    simp [unaryStack?]

theorem unaryStack?_eq_none_iff
    (cmp : EvmWord → Bool) (stack : List EvmWord) :
    unaryStack? cmp stack = none ↔ stack.length < 1 := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        simp
    | cons a rest =>
        simp [unaryStack?] at h_stack
  · intro h_len
    cases stack with
    | nil =>
        simp [unaryStack?]
    | cons a rest =>
        simp at h_len

theorem binaryHandler_stack_of_binaryStack?_some
    {cmp : EvmWord → EvmWord → Bool}
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? cmp state.stack = some stack') :
    (binaryHandler cmp state).stack = stack' := by
  simp [binaryHandler, h_stack]

theorem unaryHandler_stack_of_unaryStack?_some
    {cmp : EvmWord → Bool}
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : unaryStack? cmp state.stack = some stack') :
    (unaryHandler cmp state).stack = stack' := by
  simp [unaryHandler, h_stack]

theorem binaryHandler_status_of_binaryStack?_none
    {cmp : EvmWord → EvmWord → Bool}
    {state : EvmState}
    (h_stack : binaryStack? cmp state.stack = none) :
    (binaryHandler cmp state).status = .error := by
  simp [binaryHandler, h_stack]

theorem unaryHandler_status_of_unaryStack?_none
    {cmp : EvmWord → Bool} {state : EvmState}
    (h_stack : unaryStack? cmp state.stack = none) :
    (unaryHandler cmp state).status = .error := by
  simp [unaryHandler, h_stack]

@[simp] theorem ltHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (ltHandler { state with stack := a :: b :: rest }).stack =
      boolWord (BitVec.ult a b) :: rest := rfl

@[simp] theorem gtHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (gtHandler { state with stack := a :: b :: rest }).stack =
      boolWord (BitVec.ult b a) :: rest := rfl

@[simp] theorem sltHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (sltHandler { state with stack := a :: b :: rest }).stack =
      boolWord (BitVec.slt a b) :: rest := rfl

@[simp] theorem sgtHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (sgtHandler { state with stack := a :: b :: rest }).stack =
      boolWord (BitVec.slt b a) :: rest := rfl

@[simp] theorem eqHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (eqHandler { state with stack := a :: b :: rest }).stack =
      boolWord (decide (a = b)) :: rest := rfl

@[simp] theorem iszeroHandler_stack
    (a : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (iszeroHandler { state with stack := a :: rest }).stack =
      boolWord (decide (a = 0)) :: rest := rfl

@[simp] theorem comparisonHandlerTable_eq :
    comparisonHandlerTable = comparisonHandler? := rfl

@[simp] theorem comparisonHandler?_LT :
    comparisonHandler? .LT = some ltHandler := rfl

@[simp] theorem comparisonHandler?_GT :
    comparisonHandler? .GT = some gtHandler := rfl

@[simp] theorem comparisonHandler?_SLT :
    comparisonHandler? .SLT = some sltHandler := rfl

@[simp] theorem comparisonHandler?_SGT :
    comparisonHandler? .SGT = some sgtHandler := rfl

@[simp] theorem comparisonHandler?_EQ :
    comparisonHandler? .EQ = some eqHandler := rfl

@[simp] theorem comparisonHandler?_ISZERO :
    comparisonHandler? .ISZERO = some iszeroHandler := rfl

@[simp] theorem eq_ltHandler_iff (handler : OpcodeHandler) :
    ltHandler = handler ↔ handler = ltHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm

@[simp] theorem eq_gtHandler_iff (handler : OpcodeHandler) :
    gtHandler = handler ↔ handler = gtHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm

@[simp] theorem eq_sltHandler_iff (handler : OpcodeHandler) :
    sltHandler = handler ↔ handler = sltHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm

@[simp] theorem eq_sgtHandler_iff (handler : OpcodeHandler) :
    sgtHandler = handler ↔ handler = sgtHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm

@[simp] theorem eq_eqHandler_iff (handler : OpcodeHandler) :
    eqHandler = handler ↔ handler = eqHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm

@[simp] theorem eq_iszeroHandler_iff (handler : OpcodeHandler) :
    iszeroHandler = handler ↔ handler = iszeroHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm

theorem comparisonHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    comparisonHandler? opcode = some handler ↔
      (opcode = .LT ∧ handler = ltHandler) ∨
        (opcode = .GT ∧ handler = gtHandler) ∨
          (opcode = .SLT ∧ handler = sltHandler) ∨
            (opcode = .SGT ∧ handler = sgtHandler) ∨
              (opcode = .EQ ∧ handler = eqHandler) ∨
                (opcode = .ISZERO ∧ handler = iszeroHandler) := by
  cases opcode <;> simp [comparisonHandler?]

theorem comparisonHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    comparisonHandler? opcode = none ↔
      opcode ≠ .LT ∧ opcode ≠ .GT ∧ opcode ≠ .SLT ∧
        opcode ≠ .SGT ∧ opcode ≠ .EQ ∧ opcode ≠ .ISZERO := by
  cases opcode <;> simp [comparisonHandler?]

theorem dispatchOpcode?_comparisonHandlerTable_LT
    (state : EvmState) :
    HandlerTable.dispatchOpcode? comparisonHandlerTable .LT state =
      some (ltHandler state) := by
  exact HandlerTable.dispatchOpcode?_some comparisonHandler?_LT state

theorem dispatchOpcode?_comparisonHandlerTable_GT
    (state : EvmState) :
    HandlerTable.dispatchOpcode? comparisonHandlerTable .GT state =
      some (gtHandler state) := by
  exact HandlerTable.dispatchOpcode?_some comparisonHandler?_GT state

theorem dispatchOpcode?_comparisonHandlerTable_SLT
    (state : EvmState) :
    HandlerTable.dispatchOpcode? comparisonHandlerTable .SLT state =
      some (sltHandler state) := by
  exact HandlerTable.dispatchOpcode?_some comparisonHandler?_SLT state

theorem dispatchOpcode?_comparisonHandlerTable_SGT
    (state : EvmState) :
    HandlerTable.dispatchOpcode? comparisonHandlerTable .SGT state =
      some (sgtHandler state) := by
  exact HandlerTable.dispatchOpcode?_some comparisonHandler?_SGT state

theorem dispatchOpcode?_comparisonHandlerTable_EQ
    (state : EvmState) :
    HandlerTable.dispatchOpcode? comparisonHandlerTable .EQ state =
      some (eqHandler state) := by
  exact HandlerTable.dispatchOpcode?_some comparisonHandler?_EQ state

theorem dispatchOpcode?_comparisonHandlerTable_ISZERO
    (state : EvmState) :
    HandlerTable.dispatchOpcode? comparisonHandlerTable .ISZERO state =
      some (iszeroHandler state) := by
  exact HandlerTable.dispatchOpcode?_some comparisonHandler?_ISZERO state

theorem dispatchOpcode_comparisonHandlerTable_LT
    (state : EvmState) :
    HandlerTable.dispatchOpcode comparisonHandlerTable .LT state =
      ltHandler state := by
  exact HandlerTable.dispatchOpcode_some comparisonHandler?_LT state

theorem dispatchOpcode_comparisonHandlerTable_GT
    (state : EvmState) :
    HandlerTable.dispatchOpcode comparisonHandlerTable .GT state =
      gtHandler state := by
  exact HandlerTable.dispatchOpcode_some comparisonHandler?_GT state

theorem dispatchOpcode_comparisonHandlerTable_SLT
    (state : EvmState) :
    HandlerTable.dispatchOpcode comparisonHandlerTable .SLT state =
      sltHandler state := by
  exact HandlerTable.dispatchOpcode_some comparisonHandler?_SLT state

theorem dispatchOpcode_comparisonHandlerTable_SGT
    (state : EvmState) :
    HandlerTable.dispatchOpcode comparisonHandlerTable .SGT state =
      sgtHandler state := by
  exact HandlerTable.dispatchOpcode_some comparisonHandler?_SGT state

theorem dispatchOpcode_comparisonHandlerTable_EQ
    (state : EvmState) :
    HandlerTable.dispatchOpcode comparisonHandlerTable .EQ state =
      eqHandler state := by
  exact HandlerTable.dispatchOpcode_some comparisonHandler?_EQ state

theorem dispatchOpcode_comparisonHandlerTable_ISZERO
    (state : EvmState) :
    HandlerTable.dispatchOpcode comparisonHandlerTable .ISZERO state =
      iszeroHandler state := by
  exact HandlerTable.dispatchOpcode_some comparisonHandler?_ISZERO state

theorem dispatchOpcode_comparisonHandlerTable_LT_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? BitVec.ult state.stack = some stack') :
    (HandlerTable.dispatchOpcode comparisonHandlerTable .LT state).status =
      state.status := by
  rw [dispatchOpcode_comparisonHandlerTable_LT state]
  simp [ltHandler, binaryHandler, h_stack, EvmState.withStack]

theorem dispatchOpcode_comparisonHandlerTable_GT_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? (fun a b => BitVec.ult b a) state.stack =
      some stack') :
    (HandlerTable.dispatchOpcode comparisonHandlerTable .GT state).status =
      state.status := by
  rw [dispatchOpcode_comparisonHandlerTable_GT state]
  simp [gtHandler, binaryHandler, h_stack, EvmState.withStack]

theorem dispatchOpcode_comparisonHandlerTable_SLT_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? BitVec.slt state.stack = some stack') :
    (HandlerTable.dispatchOpcode comparisonHandlerTable .SLT state).status =
      state.status := by
  rw [dispatchOpcode_comparisonHandlerTable_SLT state]
  simp [sltHandler, binaryHandler, h_stack, EvmState.withStack]

theorem dispatchOpcode_comparisonHandlerTable_SGT_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? (fun a b => BitVec.slt b a) state.stack =
      some stack') :
    (HandlerTable.dispatchOpcode comparisonHandlerTable .SGT state).status =
      state.status := by
  rw [dispatchOpcode_comparisonHandlerTable_SGT state]
  simp [sgtHandler, binaryHandler, h_stack, EvmState.withStack]

theorem dispatchOpcode_comparisonHandlerTable_EQ_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? (fun a b => decide (a = b)) state.stack =
      some stack') :
    (HandlerTable.dispatchOpcode comparisonHandlerTable .EQ state).status =
      state.status := by
  rw [dispatchOpcode_comparisonHandlerTable_EQ state]
  simp [eqHandler, binaryHandler, h_stack, EvmState.withStack]

theorem dispatchOpcode_comparisonHandlerTable_ISZERO_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : unaryStack? (fun a => decide (a = (0 : EvmWord))) state.stack =
      some stack') :
    (HandlerTable.dispatchOpcode comparisonHandlerTable .ISZERO state).status =
      state.status := by
  rw [dispatchOpcode_comparisonHandlerTable_ISZERO state]
  cases h_stack_state : state.stack <;>
    simp [unaryStack?, iszeroHandler, unaryHandler, EvmState.withStack,
      h_stack_state] at h_stack ⊢

end ComparisonHandlers
end EvmAsm.Evm64
