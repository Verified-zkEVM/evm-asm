/-
  EvmAsm.Evm64.PrecompileResult

  Pure precompile result framing for GH #116.
-/

module

public import EvmAsm.Evm64.Precompile

@[expose] public section

namespace EvmAsm.Evm64

/-- Coarse status returned by a precompile dispatch. -/
inductive PrecompileStatus where
  | success
  | failure
  deriving DecidableEq, Repr

/-- Pure input surface for a precompile invocation. -/
structure PrecompileInput where
  target : Precompile
  caller : Address
  input : List (BitVec 8)
  gas : Nat

/-- Pure output surface for a precompile invocation. -/
structure PrecompileResult where
  status : PrecompileStatus
  output : List (BitVec 8)
  gasRemaining : Nat

namespace PrecompileResult

def ok (out : List (BitVec 8)) (gasRemaining : Nat) : PrecompileResult :=
  { status := .success
    output := out
    gasRemaining := gasRemaining }

def fail (gasRemaining : Nat) : PrecompileResult :=
  { status := .failure
    output := ([] : List (BitVec 8))
    gasRemaining := gasRemaining }

def succeeded (result : PrecompileResult) : Prop :=
  result.status = .success

def failed (result : PrecompileResult) : Prop :=
  result.status = .failure

def preservesGasBound (input : PrecompileInput) (result : PrecompileResult) : Prop :=
  result.gasRemaining ≤ input.gas

def outputMatches (result : PrecompileResult) (out : List (BitVec 8)) : Prop :=
  result.status = .success ∧ result.output = out

@[simp] theorem ok_status (out : List (BitVec 8)) (gasRemaining : Nat) :
    (ok out gasRemaining).status = .success := rfl

@[simp] theorem ok_output (out : List (BitVec 8)) (gasRemaining : Nat) :
    (ok out gasRemaining).output = out := rfl

@[simp] theorem ok_gasRemaining (out : List (BitVec 8)) (gasRemaining : Nat) :
    (ok out gasRemaining).gasRemaining = gasRemaining := rfl

@[simp] theorem fail_status (gasRemaining : Nat) :
    (fail gasRemaining).status = .failure := rfl

@[simp] theorem fail_output (gasRemaining : Nat) :
    (fail gasRemaining).output = ([] : List (BitVec 8)) := rfl

@[simp] theorem fail_gasRemaining (gasRemaining : Nat) :
    (fail gasRemaining).gasRemaining = gasRemaining := rfl

theorem succeeded_ok (out : List (BitVec 8)) (gasRemaining : Nat) :
    succeeded (ok out gasRemaining) := rfl

theorem failed_fail (gasRemaining : Nat) :
    failed (fail gasRemaining) := rfl

@[simp] theorem output_fail (gasRemaining : Nat) :
    (fail gasRemaining).output = ([] : List (BitVec 8)) := rfl

theorem outputMatches_ok (out : List (BitVec 8)) (gasRemaining : Nat) :
    outputMatches (ok out gasRemaining) out := by
  exact ⟨rfl, rfl⟩

theorem not_failed_ok (out : List (BitVec 8)) (gasRemaining : Nat) :
    ¬ failed (ok out gasRemaining) := by
  simp [failed]

theorem not_succeeded_fail (gasRemaining : Nat) :
    ¬ succeeded (fail gasRemaining) := by
  simp [succeeded, fail]

theorem not_outputMatches_fail (out : List (BitVec 8)) (gasRemaining : Nat) :
    ¬ outputMatches (fail gasRemaining) out := by
  simp [outputMatches]

theorem preservesGasBound_ok_iff
    (input : PrecompileInput) (out : List (BitVec 8)) (gasRemaining : Nat) :
    preservesGasBound input (ok out gasRemaining) ↔ gasRemaining ≤ input.gas := by
  simp [preservesGasBound]

theorem preservesGasBound_fail_iff
    (input : PrecompileInput) (gasRemaining : Nat) :
    preservesGasBound input (fail gasRemaining) ↔ gasRemaining ≤ input.gas := by
  simp [preservesGasBound]

theorem preservesGasBound_same (input : PrecompileInput) :
    preservesGasBound input (ok ([] : List (BitVec 8)) input.gas) := by
  simp [preservesGasBound, ok]

end PrecompileResult

end EvmAsm.Evm64
