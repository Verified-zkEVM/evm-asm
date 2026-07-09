/-
  EvmAsm.EL.WorldStateAccount

  Account-existence helpers for the pure EL world-state model (GH #123).
-/

import EvmAsm.EL.WorldState

namespace EvmAsm.EL

namespace Account

/-- Canonical empty account placeholder used when touching a missing account. -/
def empty : Account :=
  { nonce := 0
    balance := 0
    storageRoot := 0
    codeHash := 0
    code := [] }

/-- Coarse empty-account predicate for account lifecycle hooks. -/
def isEmpty (account : Account) : Prop :=
  account.nonce = 0 ∧ account.balance = 0 ∧ account.storageRoot = 0 ∧
    account.codeHash = 0 ∧ account.code = []

@[simp] theorem isEmpty_empty : isEmpty empty := by
  simp [isEmpty, empty]

end Account

namespace WorldState

end WorldState

end EvmAsm.EL
