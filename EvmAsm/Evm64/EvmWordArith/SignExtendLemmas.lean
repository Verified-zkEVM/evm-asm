import EvmAsm.Evm64.Basic
import EvmAsm.Rv64.Instructions

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Sign-extending the 12-bit immediate `4095` produces the all-ones word. -/
theorem signExtend12_4095_toNat :
    (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by
  decide

end EvmAsm.Evm64
