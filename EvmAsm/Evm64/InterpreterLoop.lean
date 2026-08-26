/-
  EvmAsm.Evm64.InterpreterLoop

  Pure fetch/decode/dispatch loop scaffold for the EVM interpreter (GH #108).
-/

module

public import EvmAsm.Evm64.Dispatch
public import EvmAsm.Evm64.Termination

@[expose] public section

namespace EvmAsm.Evm64

namespace InterpreterLoop

/-- Fetch the opcode byte at the current EVM PC. -/
def fetchOpcodeByte? (state : EvmState) : Option (BitVec 8) :=
  if h_pc : state.pc < state.code.length then
    some state.code[state.pc]
  else
    none

/-- Decode the current opcode byte through the modeled dispatch table. -/
def decodeCurrentOpcode? (state : EvmState) : Option EvmOpcode :=
  match fetchOpcodeByte? state with
  | some byte => EvmOpcode.decodeByte? byte.toNat
  | none => none

/-- Pluggable interpreter handler surface. Concrete opcode wrappers can later
    instantiate this by dispatching to verified handler specs. -/
abbrev Handler := EvmOpcode → EvmState → EvmState

/-- One fetch/decode/dispatch step. EOF or an unsupported opcode transitions
    to `invalid`; modeled opcodes are delegated to the supplied handler.
    Distinctive token: InterpreterLoop.stepWithHandler. -/
def stepWithHandler (handler : Handler) (state : EvmState) : EvmState :=
  match decodeCurrentOpcode? state with
  | some opcode => handler opcode state
  | none => state.invalid

/-- Step-bounded interpreter loop. Non-running states are returned unchanged;
    running states take at most `nSteps` fetch/decode/dispatch steps.
    Distinctive token: InterpreterLoop.loopFuel. -/
def loopFuel (handler : Handler) : Nat → EvmState → EvmState
  | 0, state => state
  | nSteps + 1, state =>
      match state.status with
      | .running => loopFuel handler nSteps (stepWithHandler handler state)
      | _ => state

theorem fetchOpcodeByte?_of_lt
    {state : EvmState} (h_pc : state.pc < state.code.length) :
    fetchOpcodeByte? state = some state.code[state.pc] := by
  simp [fetchOpcodeByte?, h_pc]

theorem fetchOpcodeByte?_of_ge
    {state : EvmState} (h_pc : state.code.length ≤ state.pc) :
    fetchOpcodeByte? state = none := by
  simp [fetchOpcodeByte?, show ¬ state.pc < state.code.length from by omega]

theorem fetchOpcodeByte?_eq_some_iff
    {state : EvmState} {byte : BitVec 8} :
    fetchOpcodeByte? state = some byte ↔
      ∃ h_pc : state.pc < state.code.length, byte = state.code[state.pc]'h_pc := by
  unfold fetchOpcodeByte?
  by_cases h_pc : state.pc < state.code.length
  · rw [dif_pos h_pc]
    constructor
    · intro h_eq
      injection h_eq with h_byte
      exact ⟨h_pc, h_byte.symm⟩
    · rintro ⟨h_pc', h_eq⟩
      simp only [h_eq]
  · rw [dif_neg h_pc]
    simp [h_pc]

theorem fetchOpcodeByte?_eq_none_iff {state : EvmState} :
    fetchOpcodeByte? state = none ↔ state.code.length ≤ state.pc := by
  unfold fetchOpcodeByte?
  by_cases h_pc : state.pc < state.code.length
  · have h_not : ¬ state.code.length ≤ state.pc := Nat.not_le_of_gt h_pc
    simp [h_pc, h_not]
  · have h_le : state.code.length ≤ state.pc := Nat.le_of_not_gt h_pc
    simp [h_pc, h_le]

theorem decodeCurrentOpcode?_of_fetch
    {state : EvmState} {byte : BitVec 8}
    (h_fetch : fetchOpcodeByte? state = some byte) :
    decodeCurrentOpcode? state = EvmOpcode.decodeByte? byte.toNat := by
  simp [decodeCurrentOpcode?, h_fetch]

theorem decodeCurrentOpcode?_of_fetch_unsupported
    {state : EvmState} {byte : BitVec 8}
    (h_fetch : fetchOpcodeByte? state = some byte)
    (h_decode : EvmOpcode.decodeByte? byte.toNat = none) :
    decodeCurrentOpcode? state = none := by
  rw [decodeCurrentOpcode?_of_fetch h_fetch, h_decode]

theorem decodeCurrentOpcode?_of_eof
    {state : EvmState} (h_fetch : fetchOpcodeByte? state = none) :
    decodeCurrentOpcode? state = none := by
  simp [decodeCurrentOpcode?, h_fetch]

/-- Characterize when `decodeCurrentOpcode?` returns `some opcode`: exactly when the
    current PC fetches a byte whose `decodeByte?` succeeds with that opcode.
    Distinctive token: InterpreterLoop.decodeCurrentOpcode?_eq_some_iff. -/
theorem decodeCurrentOpcode?_eq_some_iff
    {state : EvmState} {opcode : EvmOpcode} :
    decodeCurrentOpcode? state = some opcode ↔
      ∃ byte : BitVec 8,
        fetchOpcodeByte? state = some byte ∧
          EvmOpcode.decodeByte? byte.toNat = some opcode := by
  constructor
  · intro h_eq
    by_cases h_pc : state.pc < state.code.length
    · have h_fetch : fetchOpcodeByte? state = some state.code[state.pc] :=
        fetchOpcodeByte?_of_lt h_pc
      rw [decodeCurrentOpcode?_of_fetch h_fetch] at h_eq
      exact ⟨state.code[state.pc], h_fetch, h_eq⟩
    · have h_le : state.code.length ≤ state.pc := Nat.le_of_not_gt h_pc
      have h_fetch : fetchOpcodeByte? state = none := fetchOpcodeByte?_of_ge h_le
      rw [decodeCurrentOpcode?_of_eof h_fetch] at h_eq
      cases h_eq
  · rintro ⟨byte, h_fetch, h_decode⟩
    rw [decodeCurrentOpcode?_of_fetch h_fetch]
    exact h_decode

/-- Characterize when `decodeCurrentOpcode?` returns `none`: either the fetch is at
    or past EOF, or the fetched byte does not decode to a modeled opcode.
    Distinctive token: InterpreterLoop.decodeCurrentOpcode?_eq_none_iff. -/
theorem decodeCurrentOpcode?_eq_none_iff {state : EvmState} :
    decodeCurrentOpcode? state = none ↔
      fetchOpcodeByte? state = none ∨
        ∃ byte : BitVec 8,
          fetchOpcodeByte? state = some byte ∧
            EvmOpcode.decodeByte? byte.toNat = none := by
  constructor
  · intro h_eq
    by_cases h_pc : state.pc < state.code.length
    · have h_fetch : fetchOpcodeByte? state = some state.code[state.pc] :=
        fetchOpcodeByte?_of_lt h_pc
      rw [decodeCurrentOpcode?_of_fetch h_fetch] at h_eq
      exact Or.inr ⟨state.code[state.pc], h_fetch, h_eq⟩
    · have h_le : state.code.length ≤ state.pc := Nat.le_of_not_gt h_pc
      exact Or.inl (fetchOpcodeByte?_of_ge h_le)
  · rintro (h_none | ⟨byte, h_fetch, h_decode⟩)
    · exact decodeCurrentOpcode?_of_eof h_none
    · exact decodeCurrentOpcode?_of_fetch_unsupported h_fetch h_decode

theorem stepWithHandler_of_decode
    (handler : Handler) {state : EvmState} {opcode : EvmOpcode}
    (h_decode : decodeCurrentOpcode? state = some opcode) :
    stepWithHandler handler state = handler opcode state := by
  simp [stepWithHandler, h_decode]

theorem stepWithHandler_of_unsupported
    (handler : Handler) {state : EvmState}
    (h_decode : decodeCurrentOpcode? state = none) :
    stepWithHandler handler state = state.invalid := by
  simp [stepWithHandler, h_decode]

theorem stepWithHandler_of_fetch_unsupported
    (handler : Handler) {state : EvmState} {byte : BitVec 8}
    (h_fetch : fetchOpcodeByte? state = some byte)
    (h_decode : EvmOpcode.decodeByte? byte.toNat = none) :
    stepWithHandler handler state = state.invalid :=
  stepWithHandler_of_unsupported handler
    (decodeCurrentOpcode?_of_fetch_unsupported h_fetch h_decode)

@[simp] theorem loopFuel_zero (handler : Handler) (state : EvmState) :
    loopFuel handler 0 state = state := rfl

theorem loopFuel_succ_running
    (handler : Handler) (nSteps : Nat) (state : EvmState)
    (h_status : state.status = .running) :
    loopFuel handler (nSteps + 1) state =
      loopFuel handler nSteps (stepWithHandler handler state) := by
  simp [loopFuel, h_status]

theorem stepWithHandler_eof_invalid
    (handler : Handler) {state : EvmState}
    (h_pc : state.code.length ≤ state.pc) :
    stepWithHandler handler state = state.invalid := by
  exact stepWithHandler_of_unsupported handler
    (decodeCurrentOpcode?_of_eof (fetchOpcodeByte?_of_ge h_pc))

end InterpreterLoop

end EvmAsm.Evm64
