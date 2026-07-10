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

/-- Amsterdam/Prague base intrinsic gas for a transaction. -/
def txBaseGas : Nat := 21000

/-- Contract-creation intrinsic gas surcharge. Simple value transfers do not pay this. -/
def txCreateGas : Nat := 32000

/-- Intrinsic gas charged for one zero calldata byte. -/
def txDataZeroGas : Nat := 4

/-- Intrinsic gas charged for one nonzero calldata byte. -/
def txDataNonzeroGas : Nat := 16

/-- Intrinsic calldata gas under the legacy/EIP-2028 byte schedule. -/
def calldataIntrinsicGas (data : List Byte) : Nat :=
  data.foldl (fun acc b => acc + if b = 0 then txDataZeroGas else txDataNonzeroGas) 0

/-- Intrinsic gas for the legacy-call subset: base + creation surcharge + data bytes.

    Access-list, authorization-list, blob, and calldata-floor additions are
    deliberately outside this helper; simple value transfers have no such
    fields and `data = []`. -/
def intrinsicGas (tx : Transaction) : Nat :=
  txBaseGas + (if tx.to.isNone then txCreateGas else 0) + calldataIntrinsicGas tx.data

def intrinsicGasWithinLimit (tx : Transaction) : Prop :=
  tx.intrinsicGas ≤ tx.gasLimit

def maxPriorityFeeWithinMaxFee (tx : Transaction) : Prop :=
  tx.maxPriorityFeePerGas ≤ tx.maxFeePerGas

def isSimpleValueTransfer (tx : Transaction) : Prop :=
  tx.to.isSome ∧ tx.data = []

/-- Upfront gas budget charged before execution, excluding transferred value. -/
def upfrontGasCost (tx : Transaction) (baseFee : Nat) : Nat :=
  tx.gasLimit * tx.effectiveGasPrice baseFee

/-- Total upfront balance requirement: gas budget plus transferred value. -/
def upfrontCost (tx : Transaction) (baseFee : Nat) : Nat :=
  tx.upfrontGasCost baseFee + tx.value.toNat

def nonceMatches (account : Account) (tx : Transaction) : Prop :=
  account.nonce = tx.nonce

def gasLimitWithinBlock (tx : Transaction) (blockGasRemaining : Nat) : Prop :=
  tx.gasLimit ≤ blockGasRemaining

def maxFeeCoversBaseFee (tx : Transaction) (baseFee : Nat) : Prop :=
  baseFee ≤ tx.maxFeePerGas

def senderCanPayUpfront (account : Account) (tx : Transaction) (baseFee : Nat) : Prop :=
  tx.upfrontCost baseFee ≤ account.balance.toNat

theorem effectivePriorityFee_eq_min_of_base_le
    (tx : Transaction) {baseFee : Nat} (h_base : baseFee ≤ tx.maxFeePerGas) :
    tx.effectivePriorityFee baseFee =
      Nat.min tx.maxPriorityFeePerGas (tx.maxFeePerGas - baseFee) := by
  simp [effectivePriorityFee, h_base]

theorem effectivePriorityFee_eq_zero_of_base_gt
    (tx : Transaction) {baseFee : Nat} (h_base : tx.maxFeePerGas < baseFee) :
    tx.effectivePriorityFee baseFee = 0 := by
  simp [effectivePriorityFee, show ¬baseFee ≤ tx.maxFeePerGas from by omega]


@[simp] theorem calldataIntrinsicGas_nil : calldataIntrinsicGas [] = 0 := rfl

theorem intrinsicGas_eq_base_of_simpleValueTransfer
    {tx : Transaction} (h_simple : tx.isSimpleValueTransfer) :
    tx.intrinsicGas = txBaseGas := by
  rcases h_simple with ⟨h_to, h_data⟩
  unfold intrinsicGas
  rw [h_data]
  cases h_to_eq : tx.to with
  | none => simp [h_to_eq] at h_to
  | some to => simp

theorem intrinsicGasWithinLimit_of_simpleValueTransfer
    {tx : Transaction} (h_simple : tx.isSimpleValueTransfer)
    (h_gas : txBaseGas ≤ tx.gasLimit) :
    tx.intrinsicGasWithinLimit := by
  rw [intrinsicGasWithinLimit, intrinsicGas_eq_base_of_simpleValueTransfer h_simple]
  exact h_gas

end Transaction

end EvmAsm.EL
