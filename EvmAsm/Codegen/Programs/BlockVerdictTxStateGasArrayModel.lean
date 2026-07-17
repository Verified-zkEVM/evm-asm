/-
  Pure model for `block_verdict_tx_state_gas_array` (bead evm-asm-a4gbr).

  The array program (TxIntrinsicStateGas.lean, 96-instr Program) fills
  `out[i]` for each body tx with:

      out[i] = intrinsic_state_gas(tx_i)
             + (bal_ptr ≠ 0 ? teer_applied_state_charge(tx_i, BAL, chain_id, i+1)
                            : 0)

  Post EIP-2780 / tests-zkevm@v0.6.0 the guest's `tx_intrinsic_state_gas`
  success path yields 0 (creation NEW_ACCOUNT and worst-case auth reserve are
  gone; SpecRef `calculate_intrinsic_cost` likewise sets `state := 0`). Exact
  EIP-7702 set_delegation state charges live in
  `tx_eip7702_existing_authority_refund` (teer): APPLIED a0, zeroed when BAL
  shows prep rolled back (matches SpecRef process_message prep ExceptionalHalt
  refill of authStateGasUsed).

  This file is the pure-model half of the first a4gbr deliverable. The
  cpsTripleWithin Fn.Spec lives in BlockVerdictTxStateGasArraySpec.lean and
  is proved under assumed callee contracts for the still-unconverted
  `tx_intrinsic_state_gas` / teer strings (residual convert beads).
-/

import EvmAsm.Stateless.SpecRef.Gas
import EvmAsm.Stateless.SpecRef.Transactions

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel

open EvmAsm.Stateless.SpecRef

/-! ## Constants (re-export for callers) -/

/-- `StateGasCosts.AUTH_BASE` — net-new delegation indicator write. -/
abbrev authBase : Nat := StateGasCosts.AUTH_BASE

/-- `StateGasCosts.NEW_ACCOUNT` — authority leaf materialization. -/
abbrev newAccount : Nat := StateGasCosts.NEW_ACCOUNT

/-! ## Intrinsic state gas (post EIP-2780) -/

/-- Success-path pure intrinsic state gas for an encoded tx.

    Matches SpecRef `calculate_intrinsic_cost(...).state = 0` and the guest
    `tx_intrinsic_state_gas` body (accumulator 0 → `eip8037_tx_state_gas`).
    Parse failures are *not* modeled here — the array prog surfaces them as
    status a0 ∈ {1,2,3} without a success claim on `out[]`. -/
def pureIntrinsicStateGasSuccess : Nat := 0

theorem pureIntrinsicStateGasSuccess_eq_specRef
    (tx : Transaction) (sender : Address) :
    (calculate_intrinsic_cost tx sender).state = pureIntrinsicStateGasSuccess := by
  simp [calculate_intrinsic_cost, pureIntrinsicStateGasSuccess]

/-! ## Teer APPLIED state charge (abstract interface)

    Full BAL-driven set_delegation accounting is large (per-auth NEW_ACCOUNT +
    AUTH_BASE with intra-tx written/delegated sets + rolled-back zeroing). Until
    `tx_eip7702_existing_authority_refund` is converted, the array Fn.Spec is
    parameterized by an arbitrary pure teer model `TeerApplied` that the assumed
    callee contract instantiates.

    Genuineness obligation (checked before proving under a concrete model):
    `TeerApplied` must match execution-specs APPLIED set_delegation state gas
    for the same (tx, BAL, chain_id, block_access_index), including:
      * retained auth residue when set_delegation succeeded and later mid-exec
        failed (the bmvmx.5.5.11.1 FA class);
      * zero APPLIED when prep ExceptionalHalt rolls back (SpecRef
        authStateGasUsed := 0 + refill). -/

/-- Pure teer APPLIED state-charge function shape.
    Args: encoded tx bytes, BAL bytes, chain id, 1-based block_access_index. -/
abbrev TeerApplied :=
  List (BitVec 8) → List (BitVec 8) → Nat → Nat → Nat

/-- Per-tx array cell under a teer model. -/
def txStateGasCell (teer : TeerApplied) (txBytes balBytes : List (BitVec 8))
    (chainId blockAccessIndex : Nat) (balEnabled : Bool) : Nat :=
  pureIntrinsicStateGasSuccess +
    if balEnabled then teer txBytes balBytes chainId blockAccessIndex else 0

/-- Full array model: one cell per tx in order. `txs` is the list of encoded
    body-tx byte strings; `balEnabled` mirrors `bal_ptr ≠ 0`. -/
def txStateGasArray (teer : TeerApplied) (txs : List (List (BitVec 8)))
    (balBytes : List (BitVec 8)) (chainId : Nat) (balEnabled : Bool) :
    List Nat :=
  txs.mapIdx fun i txBytes =>
    txStateGasCell teer txBytes balBytes chainId (i + 1) balEnabled

/-! ## Auth-inclusion 0-FA corollary (statement level)

    When BAL is enabled, every array cell is at least the teer APPLIED charge
    for that tx (intrinsic is 0). The gate's `eip8037_prior_state_used_exact`
    sums `bvgr_tx_state_gas[0..prior)`, so prior auth residues enter the
    sequential state-budget check. Proving the gate sum/budget is residual
    (gate body is still an unconverted asm string — codegen prerequisite). -/

theorem txStateGasCell_ge_teer (teer : TeerApplied)
    (txBytes balBytes : List (BitVec 8)) (chainId blockAccessIndex : Nat) :
    teer txBytes balBytes chainId blockAccessIndex ≤
      txStateGasCell teer txBytes balBytes chainId blockAccessIndex true := by
  simp [txStateGasCell, pureIntrinsicStateGasSuccess]

theorem txStateGasArray_length (teer : TeerApplied)
    (txs : List (List (BitVec 8))) (balBytes : List (BitVec 8))
    (chainId : Nat) (balEnabled : Bool) :
    (txStateGasArray teer txs balBytes chainId balEnabled).length = txs.length := by
  simp [txStateGasArray]

/-- Index-wise cell equation (success path of the array program). -/
theorem txStateGasArray_get (teer : TeerApplied)
    (txs : List (List (BitVec 8))) (balBytes : List (BitVec 8))
    (chainId : Nat) (balEnabled : Bool) (i : Nat) (hi : i < txs.length) :
    (txStateGasArray teer txs balBytes chainId balEnabled)[i]'(by
      simpa [txStateGasArray_length] using hi) =
      txStateGasCell teer txs[i] balBytes chainId (i + 1) balEnabled := by
  simp [txStateGasArray, List.getElem_mapIdx]

end EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
