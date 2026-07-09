/-
  EvmAsm.EL.PrecompileCallOutputBridge

  Pure bridge from precompile CALL results to caller-memory output-copy bytes.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.CallOutputArgsMemory
import EvmAsm.EL.PrecompileCallBridge

namespace EvmAsm.EL

namespace PrecompileCallOutputBridge

abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult
abbrev MemoryRange := EvmAsm.Evm64.CallArgs.MemoryRange
abbrev CallArgs := EvmAsm.Evm64.CallArgs.Call
abbrev StaticCallArgs := EvmAsm.Evm64.CallArgs.StaticCall
abbrev Byte := EvmAsm.EL.Byte

end PrecompileCallOutputBridge

end EvmAsm.EL
