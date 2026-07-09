/-
  EvmAsm.EL.CreateAddress

  Pure CREATE/CREATE2 address derivation hooks for GH #115.
-/

import EvmAsm.EL.Create

namespace EvmAsm.EL

namespace CreateAddress

/-- Inputs needed by a CREATE-family address derivation backend. CREATE uses
    `salt? = none`; CREATE2 uses `salt? = some salt`. -/
structure CreateAddressInput where
  creator : Address
  nonce : Nat
  salt? : Option Word256
  initcodeHash : Hash256
  deriving Repr

/-- Construct the derivation input for a well-formed CREATE/CREATE2 request. -/
def fromRequest? (request : CreateRequest) (creatorNonce : Nat) (initcodeHash : Hash256) :
    Option CreateAddressInput :=
  match request.kind, request.salt? with
  | .create, none =>
      some
        { creator := request.creator
          nonce := creatorNonce
          salt? := none
          initcodeHash := initcodeHash }
  | .create2, some salt =>
      some
        { creator := request.creator
          nonce := creatorNonce
          salt? := some salt
          initcodeHash := initcodeHash }
  | _, _ => none

/-- Hook for the RLP/keccak-backed address derivation implementation. -/
abbrev AddressDeriver := CreateAddressInput → Address

def derivedAddress (deriver : AddressDeriver) (input : CreateAddressInput) : Address :=
  deriver input

theorem fromRequest?_forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas creatorNonce : Nat)
    (initcodeHash : Hash256) :
    fromRequest? (CreateRequest.forCreate creator value initcode gas) creatorNonce initcodeHash =
      some
        { creator := creator
          nonce := creatorNonce
          salt? := none
          initcodeHash := initcodeHash } := rfl

theorem fromRequest?_forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas creatorNonce : Nat)
    (salt initcodeHash : Hash256) :
    fromRequest? (CreateRequest.forCreate2 creator value initcode gas salt) creatorNonce initcodeHash =
      some
        { creator := creator
          nonce := creatorNonce
          salt? := some salt
          initcodeHash := initcodeHash } := rfl

theorem derivedAddress_eq (deriver : AddressDeriver) (input : CreateAddressInput) :
    derivedAddress deriver input = deriver input := rfl

end CreateAddress

end EvmAsm.EL
