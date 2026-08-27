/-
  EvmAsm.EL.Conformance.Call

  Compact Lean-side conformance vectors for CALL output bridge helpers
  (GH #125 / GH #114).
-/

module

public import EvmAsm.EL.Conformance
public import EvmAsm.EL.CallOutputBridge

public section

namespace EvmAsm.EL
namespace Conformance
namespace Call

abbrev Byte := EvmAsm.EL.Byte
abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev MemoryRange := EvmAsm.Evm64.CallArgs.MemoryRange

end Call
end Conformance
end EvmAsm.EL
