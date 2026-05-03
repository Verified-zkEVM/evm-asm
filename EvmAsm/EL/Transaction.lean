/-
  EvmAsm.EL.Transaction

  Pure transaction data and validation predicates (GH #122 slice 1). This is
  stacked on the pure world-state model from #123 and intentionally stops before
  message-call execution, refund accounting, or coinbase payment.
-/

import EvmAsm.EL.WorldState

namespace EvmAsm.EL

/-- EIP-1559-style transaction surface needed by the Shanghai validation
    checks. Signature recovery is represented by the already-recovered sender
    address; calldata bytes are kept for later message-call execution. -/
structure Transaction where
  sender : Address
  nonce : Nat
  gasLimit : Nat
  maxFeePerGas : Nat
  maxPriorityFeePerGas : Nat
  to : Option Address
  value : Word256
  data : List Byte
  deriving Repr

namespace Transaction

/-- Effective priority fee per gas, capped by the transaction's fee headroom
    over the block base fee. If `maxFeePerGas < baseFee`, validation fails and
    this helper returns zero. -/
def effectivePriorityFee (tx : Transaction) (baseFee : Nat) : Nat :=
  if baseFee ≤ tx.maxFeePerGas then
    Nat.min tx.maxPriorityFeePerGas (tx.maxFeePerGas - baseFee)
  else
    0

/-- Effective gas price paid by the sender before refunds. -/
def effectiveGasPrice (tx : Transaction) (baseFee : Nat) : Nat :=
  baseFee + tx.effectivePriorityFee baseFee

/-- Upfront gas budget charged before execution, excluding transferred value. -/
def upfrontGasCost (tx : Transaction) (baseFee : Nat) : Nat :=
  tx.gasLimit * tx.effectiveGasPrice baseFee

/-- Total upfront balance requirement: gas budget plus transferred value. -/
def upfrontCost (tx : Transaction) (baseFee : Nat) : Nat :=
  tx.upfrontGasCost baseFee + tx.value.toNat

def senderAccount? (state : WorldState) (tx : Transaction) : Option Account :=
  state.getAccount tx.sender

def nonceMatches (account : Account) (tx : Transaction) : Prop :=
  account.nonce = tx.nonce

def gasLimitWithinBlock (tx : Transaction) (blockGasRemaining : Nat) : Prop :=
  tx.gasLimit ≤ blockGasRemaining

def maxFeeCoversBaseFee (tx : Transaction) (baseFee : Nat) : Prop :=
  baseFee ≤ tx.maxFeePerGas

def senderCanPayUpfront (account : Account) (tx : Transaction) (baseFee : Nat) : Prop :=
  tx.upfrontCost baseFee ≤ account.balance.toNat

/-- Validation checks that do not execute the transaction. This captures the
    nonce, block-gas, base-fee, and sender-balance gates from #122. -/
def validatesAgainst
    (state : WorldState) (tx : Transaction) (baseFee blockGasRemaining : Nat) : Prop :=
  ∃ account : Account,
    senderAccount? state tx = some account ∧
    nonceMatches account tx ∧
    gasLimitWithinBlock tx blockGasRemaining ∧
    maxFeeCoversBaseFee tx baseFee ∧
    senderCanPayUpfront account tx baseFee

theorem effectivePriorityFee_eq_min_of_base_le
    (tx : Transaction) {baseFee : Nat} (h_base : baseFee ≤ tx.maxFeePerGas) :
    tx.effectivePriorityFee baseFee =
      Nat.min tx.maxPriorityFeePerGas (tx.maxFeePerGas - baseFee) := by
  simp [effectivePriorityFee, h_base]

theorem effectivePriorityFee_eq_zero_of_base_gt
    (tx : Transaction) {baseFee : Nat} (h_base : tx.maxFeePerGas < baseFee) :
    tx.effectivePriorityFee baseFee = 0 := by
  simp [effectivePriorityFee, show ¬baseFee ≤ tx.maxFeePerGas from by omega]

theorem validatesAgainst_account
    {state : WorldState} {tx : Transaction} {baseFee blockGasRemaining : Nat}
    (h_valid : validatesAgainst state tx baseFee blockGasRemaining) :
    ∃ account : Account, senderAccount? state tx = some account := by
  rcases h_valid with ⟨account, h_account, _⟩
  exact ⟨account, h_account⟩

end Transaction

end EvmAsm.EL
