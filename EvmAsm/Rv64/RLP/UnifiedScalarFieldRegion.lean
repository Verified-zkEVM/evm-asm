/-
  EvmAsm.Rv64.RLP.UnifiedScalarFieldRegion

  EL.3 / Phase 5 — full scalar field decode-and-store INTO THE OUTPUT REGION. Decode a
  `.bytes data` scalar field (`1 ≤ data.length ≤ 8`) at `x13 = regionBase + ofNat O` and
  write its u64 value little-endian into the unified output-struct `bytesRegion` at byte
  offset `di0`. The region analog of `unified_scalar_field_decode_and_store` (which used
  `SD` to a separate `↦ₘ` cell) and the scalar counterpart of
  `unified_bytes_field_decode_and_copy` — so scalar and byte-array fields share one
  whole-struct output region. Coincides with `decodeScalar (bs.drop O) = some (value, tail)`.

  Composition: `unified_scalar_field_decode` (→ x11 = value) ⨾ `unified_field_scalar_store_region`
  (peeling the decode's `regOwn x14`).
-/

import EvmAsm.Rv64.RLP.UnifiedFieldScalarStoreRegion
import EvmAsm.Rv64.RLP.UnifiedScalarFieldDecode

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- The spill chain maps to `none` outside its slots `{bw + 4*j : j < 3*N}`. -/
theorem spillChainCR_none (bw a : Word) (N : Nat)
    (h : ∀ j, j < 3 * N → a ≠ bw + BitVec.ofNat 64 (4 * j)) :
    spillChainCR bw N a = none := by
  induction N generalizing bw with
  | zero => rfl
  | succ k ih =>
    have h1 : spillIterCR bw a = none := spillIterCR_none bw a (fun s hs => h s (by omega))
    have h2 : spillChainCR (bw + 12) k a = none := ih (bw + 12) (fun j hj => by
      have := h (3 + j) (by omega)
      rwa [show bw + BitVec.ofNat 64 (4 * (3 + j)) = (bw + 12) + BitVec.ofNat 64 (4 * j)
        from by bv_omega] at this)
    simp only [spillChainCR, CodeReq.union, h1, h2]

end EvmAsm.Rv64.RLP
