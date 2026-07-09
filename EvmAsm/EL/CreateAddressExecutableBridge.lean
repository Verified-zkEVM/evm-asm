/-
  EvmAsm.EL.CreateAddressExecutableBridge

  Request-level executable bridge for CREATE/CREATE2 address derivation
  (GH #115).
-/

import EvmAsm.EL.CreateAddress

namespace EvmAsm.EL

namespace CreateAddressExecutableBridge

/-- Apply an executable address derivation backend to a well-formed CREATE or
    CREATE2 request. Malformed request/salt combinations return `none`. -/
def deriveRequestAddress?
    (deriver : CreateAddress.AddressDeriver) (request : CreateRequest)
    (creatorNonce : Nat) (initcodeHash : Hash256) : Option Address :=
  (CreateAddress.fromRequest? request creatorNonce initcodeHash).map
    (CreateAddress.derivedAddress deriver)

theorem deriveRequestAddress?_forCreate
    (deriver : CreateAddress.AddressDeriver)
    (creator : Address) (value : Word256) (initcode : List Byte) (gas creatorNonce : Nat)
    (initcodeHash : Hash256) :
    deriveRequestAddress? deriver
        (CreateRequest.forCreate creator value initcode gas) creatorNonce initcodeHash =
      some
        (deriver
          { creator := creator
            nonce := creatorNonce
            salt? := none
            initcodeHash := initcodeHash }) := rfl

theorem deriveRequestAddress?_forCreate2
    (deriver : CreateAddress.AddressDeriver)
    (creator : Address) (value : Word256) (initcode : List Byte) (gas creatorNonce : Nat)
    (salt initcodeHash : Hash256) :
    deriveRequestAddress? deriver
        (CreateRequest.forCreate2 creator value initcode gas salt) creatorNonce initcodeHash =
      some
        (deriver
          { creator := creator
            nonce := creatorNonce
            salt? := some salt
            initcodeHash := initcodeHash }) := rfl

theorem deriveRequestAddress?_create_with_salt
    (deriver : CreateAddress.AddressDeriver)
    (creator : Address) (value salt : Word256) (initcode : List Byte)
    (gas creatorNonce : Nat) (initcodeHash : Hash256) :
    deriveRequestAddress? deriver
        { kind := .create
          creator := creator
          value := value
          initcode := initcode
          gas := gas
          salt? := some salt } creatorNonce initcodeHash =
      none := rfl

theorem deriveRequestAddress?_create2_without_salt
    (deriver : CreateAddress.AddressDeriver)
    (creator : Address) (value : Word256) (initcode : List Byte)
    (gas creatorNonce : Nat) (initcodeHash : Hash256) :
    deriveRequestAddress? deriver
        { kind := .create2
          creator := creator
          value := value
          initcode := initcode
          gas := gas
          salt? := none } creatorNonce initcodeHash =
      none := rfl

theorem deriveRequestAddress?_eq_some_iff
    (deriver : CreateAddress.AddressDeriver) (request : CreateRequest)
    (creatorNonce : Nat) (initcodeHash : Hash256) (address : Address) :
    deriveRequestAddress? deriver request creatorNonce initcodeHash = some address ↔
      ∃ input,
        CreateAddress.fromRequest? request creatorNonce initcodeHash = some input ∧
          deriver input = address := by
  unfold deriveRequestAddress?
  cases h_input : CreateAddress.fromRequest? request creatorNonce initcodeHash with
  | none =>
      simp
  | some input =>
      simp [CreateAddress.derivedAddress]

end CreateAddressExecutableBridge

end EvmAsm.EL
