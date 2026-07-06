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

/-- Update the created-account set after a CREATE-family result. Only deployed
    results with a concrete address mark an account as created in the current
    transaction. -/
def markCreateResult (created : CreatedAccountSet) (result : CreateResult) :
    CreatedAccountSet :=
  match result.status, result.address? with
  | .deployed, some address => markCreated created address
  | _, _ => created

/-- Boolean consumed by the EIP-6780 SELFDESTRUCT effect helper. -/
def createdInSameTx (created : CreatedAccountSet) (address : Address) : Bool :=
  contains created address

theorem contains_empty (address : Address) :
    contains empty address = false := by
  simp [contains, empty]

theorem contains_markCreated_self (created : CreatedAccountSet) (address : Address) :
    contains (markCreated created address) address = true := by
  simp [contains, markCreated]

theorem contains_markCreated_other
    (created : CreatedAccountSet) {address other : Address}
    (h_ne : other ≠ address) :
    contains (markCreated created address) other = contains created other := by
  unfold contains markCreated
  simp only [List.contains_cons]
  simp [h_ne]

theorem markCreateResult_deployed
    (created : CreatedAccountSet) (address : Address)
    (state : WorldState) (returndata : List Byte) (gasRemaining : Nat) :
    markCreateResult created
        { status := .deployed
          address? := some address
          state := state
          returndata := returndata
          gasRemaining := gasRemaining } =
      markCreated created address := rfl

theorem markCreateResult_deployed_none
    (created : CreatedAccountSet)
    (state : WorldState) (returndata : List Byte) (gasRemaining : Nat) :
    markCreateResult created
        { status := .deployed
          address? := none
          state := state
          returndata := returndata
          gasRemaining := gasRemaining } =
      created := rfl

theorem markCreateResult_reverted
    (created : CreatedAccountSet) (address? : Option Address)
    (state : WorldState) (returndata : List Byte) (gasRemaining : Nat) :
    markCreateResult created
        { status := .reverted
          address? := address?
          state := state
          returndata := returndata
          gasRemaining := gasRemaining } =
      created := by
  cases address? <;> rfl

theorem markCreateResult_failed
    (created : CreatedAccountSet) (address? : Option Address)
    (state : WorldState) (returndata : List Byte) (gasRemaining : Nat) :
    markCreateResult created
        { status := .failed
          address? := address?
          state := state
          returndata := returndata
          gasRemaining := gasRemaining } =
      created := by
  cases address? <;> rfl

theorem createdInSameTx_empty (address : Address) :
    createdInSameTx empty address = false :=
  contains_empty address

theorem createdInSameTx_markCreateResult_deployed_self
    (created : CreatedAccountSet) (address : Address)
    (state : WorldState) (returndata : List Byte) (gasRemaining : Nat) :
    createdInSameTx
        (markCreateResult created
          { status := .deployed
            address? := some address
            state := state
            returndata := returndata
            gasRemaining := gasRemaining })
        address =
      true := by
  simp [createdInSameTx, markCreateResult_deployed, contains_markCreated_self]

theorem createdInSameTx_markCreateResult_reverted
    (created : CreatedAccountSet) (address : Address) (address? : Option Address)
    (state : WorldState) (returndata : List Byte) (gasRemaining : Nat) :
    createdInSameTx
        (markCreateResult created
          { status := .reverted
            address? := address?
            state := state
            returndata := returndata
            gasRemaining := gasRemaining })
        address =
      createdInSameTx created address := by
  cases address? <;> rfl

theorem createdInSameTx_markCreateResult_failed
    (created : CreatedAccountSet) (address : Address) (address? : Option Address)
    (state : WorldState) (returndata : List Byte) (gasRemaining : Nat) :
    createdInSameTx
        (markCreateResult created
          { status := .failed
            address? := address?
            state := state
            returndata := returndata
            gasRemaining := gasRemaining })
        address =
      createdInSameTx created address := by
  cases address? <;> rfl

end CreatedAccounts

end EvmAsm.EL
