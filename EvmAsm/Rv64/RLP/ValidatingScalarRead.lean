/-
  EvmAsm.Rv64.RLP.ValidatingScalarRead

  SINGLE-PASS validated scalar-field extraction (T1 core of #9373). Composes the offset-general
  validating shortBytes decoder (`rlp_decode_shortBytes_validated_at`) with the existing big-endian
  value read (`unified_field_scalar_read`) on the decoder's SUCCESS exit. The validating arm leaves
  exactly the register convention the value read consumes — payload pointer in `x13`, payload length
  in `x11` — so a `≤8`-byte scalar field is **validated and its value extracted in one forward
  sweep**, with no second pass over the input (per the maintainer's direction on #9461).

  SUCCESS: `x11 = Nat.fromBytesBE payload`, `x13` advanced to the next field, and the verdict
  `decodeScalar (bs.drop O) = some (that value, …)` (via `decodeScalar_of_decode_bytes`). FAIL is the
  decoder's abort exit (`decode = none`) unchanged.
-/

import EvmAsm.Rv64.RLP.ValidatingFieldWalk
import EvmAsm.Rv64.RLP.UnifiedFieldScalarRead
import EvmAsm.Rv64.RLP.SchemaScalarValues

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- The validating arm leaves `x13` at `(regionBase + O) + signExtend12 1`; that is the payload
    pointer `regionBase + (O+1)` the scalar read consumes. -/
private theorem payload_ptr_eq (regionBase : Word) (O : Nat) :
    (regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12)
    = regionBase + BitVec.ofNat 64 (O + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]

end EvmAsm.Rv64.RLP
