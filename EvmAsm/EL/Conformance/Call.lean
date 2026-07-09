/-
  EvmAsm.EL.Conformance.Call

  Compact Lean-side conformance vectors for CALL output bridge helpers
  (GH #125 / GH #114).
-/

import EvmAsm.EL.Conformance
import EvmAsm.EL.CallOutputBridge

namespace EvmAsm.EL
namespace Conformance
namespace Call

abbrev Byte := EvmAsm.EL.Byte
abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev MemoryRange := EvmAsm.Evm64.CallArgs.MemoryRange

/-- Input shape for CALL output-copy executable-helper conformance vectors. -/
structure CallOutputInput where
  result : CallResult
  range : MemoryRange

def mkRange (offset size : EvmWord) : MemoryRange :=
  { offset := offset, size := size }

def runCallOutput (input : CallOutputInput) : List Byte :=
  EvmAsm.EL.CallOutputBridge.copiedOutputForRange input.result input.range

end Call
end Conformance
end EvmAsm.EL
