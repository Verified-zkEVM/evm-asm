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

/-- Account existence as a proposition over `getAccount`. -/
def accountExists (state : WorldState) (addr : Address) : Prop :=
  ∃ account, getAccount state addr = some account

/-- Touch an address by installing `Account.empty` when no account exists. -/
def ensureAccount (state : WorldState) (addr : Address) : WorldState :=
  match getAccount state addr with
  | some _ => state
  | none => setAccount state addr Account.empty

theorem accountExists_iff_getAccount_isSome (state : WorldState) (addr : Address) :
    accountExists state addr ↔ (getAccount state addr).isSome = true := by
  cases h_account : getAccount state addr <;> simp [accountExists, h_account]

end WorldState

end EvmAsm.EL
