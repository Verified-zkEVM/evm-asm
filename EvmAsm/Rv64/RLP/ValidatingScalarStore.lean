/-
  EvmAsm.Rv64.RLP.ValidatingScalarStore

  SINGLE-PASS validated scalar-field decode-AND-STORE (T1/T2 building block of #9373). Composes the
  single-pass validated scalar read (`rlp_decode_shortBytes_scalar_at`) with one `SD` that writes the
  decoded value to a fixed slot of an output struct (`outBase + offset`). One forward sweep:
  validate → read value → store to output, with no second pass over the input.

  SUCCESS: the output cell holds `Nat.fromBytesBE payload` and the verdict
  `decodeScalar (bs.drop O) = some (that value, …)` holds. FAIL: the decoder's abort exit, unchanged.
  This is the per-field operation a fixed-schema scalar decoder (`rlp_field_to_u64`,
  `withdrawal_decode`) repeats; `rOut` is a callee-saved register holding the output base (set up by
  the LP64 wrapper), distinct from the decoder's `x5/x10..x15` working set.
-/

import EvmAsm.Rv64.RLP.ValidatingScalarRead

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

end EvmAsm.Rv64.RLP
