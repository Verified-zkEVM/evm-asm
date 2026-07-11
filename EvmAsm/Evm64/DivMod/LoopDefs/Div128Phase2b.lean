import EvmAsm.Rv64.Instructions

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Phase 2b refined quotient digit used by the V4 and V5 div128 models.

The high-half guard implements Knuth's requirement to repeat the D3 test only
while `rhat2c < 2^32`; otherwise the truncated 64-bit comparison can fire
spuriously. -/
def div128Quot_phase2b_q0' (q0c rhat2c dLo div_un0 : Word) : Word :=
  if rhat2c >>> (32 : BitVec 6).toNat = 0 then
    let q0Dlo := q0c * dLo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    if BitVec.ult rhat2Un0 q0Dlo then q0c + signExtend12 4095 else q0c
  else q0c

end EvmAsm.Evm64
