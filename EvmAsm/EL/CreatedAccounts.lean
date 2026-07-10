/-
  EvmAsm.EL.CreatedAccounts

  Transaction-local account-creation tracking for EIP-6780 SELFDESTRUCT.
-/

import EvmAsm.EL.Create

namespace EvmAsm.EL

namespace CreatedAccounts

/-- Transaction-local set of accounts created during the current transaction.
    List membership is enough for the pure bridge; executable handlers can
    choose a compact concrete representation later. -/
abbrev CreatedAccountSet := List Address

def empty : CreatedAccountSet :=
  []

def contains (created : CreatedAccountSet) (address : Address) : Bool :=
  created.contains address

def markCreated (created : CreatedAccountSet) (address : Address) :
    CreatedAccountSet :=
  address :: created

end CreatedAccounts

end EvmAsm.EL
