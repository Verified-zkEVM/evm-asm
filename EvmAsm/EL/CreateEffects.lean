/-
  EvmAsm.EL.CreateEffects

  Pure successful-deployment world-state effect for CREATE and CREATE2
  (GH #115).  This module sits between the request/address surface and
  the later opcode handler specs: once a creation request has produced
  runtime code and an address, `deployResult` records the account that
  appears in the world state and the deployed `CreateResult`.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.CreateAddress

namespace EvmAsm.EL
namespace CreateEffects

/-- Account installed by a successful CREATE-family deployment.

    The storage root is left as zero in this pure model until a trie-backed
    storage-root bridge exists.  The nonce is `1`, matching the post-Spurious
    Dragon creation rule modeled by the executable spec surface. -/
def deployedAccount (request : CreateRequest) (codeHash : Hash256) : Account :=
  { nonce := 1
    balance := request.value
    storageRoot := 0
    codeHash := codeHash
    code := request.initcode }

/-- Successful CREATE-family effect: install the deployed account at the
    derived address and return a deployed result with empty returndata. -/
def deployResult
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) : CreateResult :=
  { status := .deployed
    address? := some address
    state := WorldState.setAccount state address (deployedAccount request codeHash)
    returndata := []
    gasRemaining := gasRemaining }

theorem deployedAccountNonce (request : CreateRequest) (codeHash : Hash256) :
    (deployedAccount request codeHash).nonce = 1 := rfl

theorem deployedAccountBalance (request : CreateRequest) (codeHash : Hash256) :
    (deployedAccount request codeHash).balance = request.value := rfl

theorem deployedAccountCodeHash (request : CreateRequest) (codeHash : Hash256) :
    (deployedAccount request codeHash).codeHash = codeHash := rfl

theorem deployedAccountCode (request : CreateRequest) (codeHash : Hash256) :
    (deployedAccount request codeHash).code = request.initcode := rfl

/-- The deployed result reports the successful status. -/
theorem deployResultDeployed
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    (deployResult state request address codeHash gasRemaining).deployed := rfl

theorem deployResultAddress?
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    (deployResult state request address codeHash gasRemaining).address? =
      some address := rfl

theorem deployResultReturndata
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    (deployResult state request address codeHash gasRemaining).returndata = [] := rfl

theorem deployResultGasRemaining
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    (deployResult state request address codeHash gasRemaining).gasRemaining =
      gasRemaining := rfl

end CreateEffects
end EvmAsm.EL
