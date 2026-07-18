/-
  EvmAsm.EL.CallValueTransfer

  Pure CALL value-transfer world-state effect (GH #114).  This module
  records balance movement for value-transferring CALL and simple
  transaction post-execution gas settlement. Balance sufficiency,
  account creation rules beyond touched recipients, and the full handler
  stack/state specs remain later slices.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.MessageCall
import EvmAsm.EL.Transaction
import EvmAsm.EL.WorldStateAccount

namespace EvmAsm.EL
namespace CallValueTransfer

end CallValueTransfer
end EvmAsm.EL
