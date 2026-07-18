/-
  Pure model for `eip8037_prior_state_used_exact` (a4gbr residual leaf).

  Guest (43-instr Program): given prior tx count `a0` and out-ptr `a1`,
  write the exact prior-state gas sum into `*a1` and return `a0=0`, or
  return `a0=1` on any gate/overflow failure.

  Sum over i < prior:
    sum += bvgr_tx_state_gas[i]
    if bv_tx_status_arr[i] ≠ 0:
      sum += bvgr_tx_exec_state_gas[i]
  with unsigned 64-bit overflow → fail.

  Gates (when prior ≠ 0):
    bsg_exact_state_ok ≠ 0
    bvgr_runtime_count ≥ prior
    prior ≤ 16
-/

import EvmAsm.Rv64.Basic

namespace EvmAsm.Codegen.Eip8037PriorStateUsedExactModel

open EvmAsm.Rv64

/-- Per-tx contribution: state gas always; exec state gas only when status ≠ 0. -/
def priorCell (stateGas status execGas : List Nat) (i : Nat) : Nat :=
  stateGas[i]! + (if status[i]! = 0 then 0 else execGas[i]!)

/-- Prefix sum of `priorCell` over `i < k` (unbounded Nat; overflow checked separately). -/
def priorPrefix (stateGas status execGas : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => priorPrefix stateGas status execGas k + priorCell stateGas status execGas k

/-- Unsigned 64-bit overflow-safe add: `none` iff wrap. -/
def add64? (a b : Nat) : Option Nat :=
  if a + b < 2 ^ 64 then some (a + b) else none

/-- Overflow-safe prefix: `none` on any intermediate wrap. -/
def priorPrefixExact (stateGas status execGas : List Nat) : Nat → Option Nat
  | 0 => some 0
  | k + 1 =>
      match priorPrefixExact stateGas status execGas k with
      | none => none
      | some s => add64? s (priorCell stateGas status execGas k)

/-- Static gates that must hold when `prior ≠ 0` (as Bool for computable match). -/
def priorGatesOkB (exactOk runtimeCount prior : Nat) : Bool :=
  decide (exactOk ≠ 0) && decide (runtimeCount ≥ prior) && decide (prior ≤ 16)

def priorGatesOk (exactOk runtimeCount prior : Nat) : Prop :=
  exactOk ≠ 0 ∧ runtimeCount ≥ prior ∧ prior ≤ 16

theorem priorGatesOk_iff (exactOk runtimeCount prior : Nat) :
    priorGatesOk exactOk runtimeCount prior ↔ priorGatesOkB exactOk runtimeCount prior = true := by
  simp only [priorGatesOk, priorGatesOkB, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩

/-- Full pure outcome: `some sum` on success, `none` on fail. -/
def priorExactResult (exactOk runtimeCount prior : Nat)
    (stateGas status execGas : List Nat) : Option Nat :=
  if prior = 0 then some 0
  else if priorGatesOkB exactOk runtimeCount prior = false then none
  else priorPrefixExact stateGas status execGas prior

theorem priorExactResult_zero (exactOk runtimeCount : Nat)
    (stateGas status execGas : List Nat) :
    priorExactResult exactOk runtimeCount 0 stateGas status execGas = some 0 := by
  simp [priorExactResult]

end EvmAsm.Codegen.Eip8037PriorStateUsedExactModel
