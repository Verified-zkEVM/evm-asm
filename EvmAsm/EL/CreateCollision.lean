/-
  EvmAsm.EL.CreateCollision

  CREATE/CREATE2 collision predicate bridge for GH #115.
-/

import EvmAsm.EL.CreateEffects

namespace EvmAsm.EL
namespace CreateCollision

/-- Executable-spec-shaped collision predicate for CREATE-family address checks.

The executable spec names this helper `account_has_code_or_nonce`: a creation
target collides when the account exists and has non-zero nonce or non-empty
code. In this pure model, code non-emptiness is represented by a non-zero
`codeHash` sentinel.

Distinctive token: `CreateCollision.accountHasCodeOrNonce`. -/
def accountHasCodeOrNonce (state : WorldState) (addr : Address) : Prop :=
  ∃ account, WorldState.getAccount state addr = some account ∧
    (account.nonce ≠ 0 ∨ account.codeHash ≠ 0)

/-- A CREATE-family target address is available when it has no collision. -/
def createAddressAvailable (state : WorldState) (addr : Address) : Prop :=
  ¬ accountHasCodeOrNonce state addr

theorem not_accountHasCodeOrNonce_of_getAccount_none
    {state : WorldState} {addr : Address}
    (h_none : WorldState.getAccount state addr = none) :
    ¬ accountHasCodeOrNonce state addr := by
  rintro ⟨account, h_account, _⟩
  rw [h_none] at h_account
  cases h_account

theorem createAddressAvailable_of_getAccount_none
    {state : WorldState} {addr : Address}
    (h_none : WorldState.getAccount state addr = none) :
    createAddressAvailable state addr :=
  not_accountHasCodeOrNonce_of_getAccount_none h_none

theorem accountHasCodeOrNonce_of_nonce_ne
    {state : WorldState} {addr : Address} {account : Account}
    (h_account : WorldState.getAccount state addr = some account)
    (h_nonce : account.nonce ≠ 0) :
    accountHasCodeOrNonce state addr :=
  ⟨account, h_account, Or.inl h_nonce⟩

theorem accountHasCodeOrNonce_of_codeHash_ne
    {state : WorldState} {addr : Address} {account : Account}
    (h_account : WorldState.getAccount state addr = some account)
    (h_codeHash : account.codeHash ≠ 0) :
    accountHasCodeOrNonce state addr :=
  ⟨account, h_account, Or.inr h_codeHash⟩

theorem not_createAddressAvailable_of_nonce_ne
    {state : WorldState} {addr : Address} {account : Account}
    (h_account : WorldState.getAccount state addr = some account)
    (h_nonce : account.nonce ≠ 0) :
    ¬ createAddressAvailable state addr :=
  fun h_available => h_available (accountHasCodeOrNonce_of_nonce_ne h_account h_nonce)

theorem not_createAddressAvailable_of_codeHash_ne
    {state : WorldState} {addr : Address} {account : Account}
    (h_account : WorldState.getAccount state addr = some account)
    (h_codeHash : account.codeHash ≠ 0) :
    ¬ createAddressAvailable state addr :=
  fun h_available => h_available (accountHasCodeOrNonce_of_codeHash_ne h_account h_codeHash)

end CreateCollision
end EvmAsm.EL
