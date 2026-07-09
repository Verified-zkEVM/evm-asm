/-
  EvmAsm.EL.CreateCollisionResult

  CREATE/CREATE2 collision result bridge for GH #115.
-/

import EvmAsm.EL.CreateCollision
import EvmAsm.EL.CreateResultBridge

namespace EvmAsm.EL
namespace CreateCollisionResult

/-- Result shape for the executable-spec CREATE collision branch.

When the derived target already has code or nonce, CREATE/CREATE2 fails,
pushes zero, preserves the caller-visible world state, and returns no created
address. Distinctive token: `CreateCollisionResult.collisionResult`. -/
def collisionResult (state : WorldState) (gasRemaining : Nat) : CreateResult :=
  { status := .failed
    address? := none
    state := state
    returndata := []
    gasRemaining := gasRemaining }

theorem collisionResult_status (state : WorldState) (gasRemaining : Nat) :
    (collisionResult state gasRemaining).status = .failed := rfl

theorem collisionResult_address? (state : WorldState) (gasRemaining : Nat) :
    (collisionResult state gasRemaining).address? = none := rfl

theorem collisionResult_state (state : WorldState) (gasRemaining : Nat) :
    (collisionResult state gasRemaining).state = state := rfl

theorem collisionResult_returndata (state : WorldState) (gasRemaining : Nat) :
    (collisionResult state gasRemaining).returndata = [] := rfl

theorem collisionResult_gasRemaining (state : WorldState) (gasRemaining : Nat) :
    (collisionResult state gasRemaining).gasRemaining = gasRemaining := rfl

theorem collisionResult_failed (state : WorldState) (gasRemaining : Nat) :
    (collisionResult state gasRemaining).failed := rfl

theorem collisionResult_stackWord (state : WorldState) (gasRemaining : Nat) :
    CreateResultBridge.createResultStackWord (collisionResult state gasRemaining) = 0 := rfl

end CreateCollisionResult
end EvmAsm.EL
