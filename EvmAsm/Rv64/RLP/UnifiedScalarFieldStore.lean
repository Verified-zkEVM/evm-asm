/-
  EvmAsm.Rv64.RLP.UnifiedScalarFieldStore

  EL.3 / Phase 5 — decode a scalar field AND STORE its value. Composes the
  end-to-end scalar field decode (`unified_scalar_field_decode`, which leaves the
  field value in `x11` and advances `x13` to the next field) with a single `SD`
  that writes that value to a fixed slot of an output struct (`outBase + offset`).

  This is the missing PERSISTENCE step: a multi-field schema walk decodes each
  field into `x11`, but the next field's decode clobbers `x11`, so every value
  must be written out before moving on. The output slots for scalar fields are
  u64 little-endian (nonce, gas_limit, to_present, v, …; see
  `EvmAsm/Stateless/Transaction/Decode.lean`), which is exactly what a single `SD`
  of the 64-bit value register produces. The result is the atomic, reusable unit
  the fixed-schema STF header/tx decoders repeat: decode one scalar field, store
  it, advance to the next.

  Layout (program base `base`; aligned `regionBase`, buffer `bs`, field offset `O`;
  output pointer register `rOut`, output base `outBase`, struct slot `offset`):
      base       < unified_scalar_field_decode : LBU + decoder + BE read >
                 (base .. base+180)                  ; x11 = value, x13 → next field
      base+180   SD rOut, x11, offset                ; [outBase + offset] := value
      base+184   (exit)
-/

import EvmAsm.Rv64.RLP.UnifiedScalarFieldDecode
import EvmAsm.Rv64.InstructionSpecs

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

end EvmAsm.Rv64.RLP
