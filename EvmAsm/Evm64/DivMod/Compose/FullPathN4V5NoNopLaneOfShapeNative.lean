/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneOfShapeNative

  The full n=4 v5 DIV lane, UNCONDITIONAL on the n=4 shape — no runtime
  certificates.  Both branch certificates are now dischargeable from the shape:

  * shift=0 → `evm_div_n4_lane_shift0_v5_of_cert` (#7626) fed by the shift=0
    cert-of-shape `evm_div_n4_shift0_cert_of_shape` (#7635);
  * shift≠0 → the native dispatcher `evm_div_n4_lane_shiftNz_v5_of_cert_native`
    (#7642) fed by the shift≠0 cert-of-shape `evm_div_n4_shiftNz_cert_of_shape_native`
    (#7666).

  This is the `lane_n4` obligation of
  `evm_div_stack_spec_unconditional_of_lanes_v5_div` discharged from `b3 ≠ 0` (and
  the alignment side condition) alone — the v5-native counterpart of
  `evm_div_n4_lane_v5_of_certs` (#7628) with both certificates eliminated.
  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopShiftNzCertOfShape
public import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CertOfShape

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The full v5 n=4 DIV lane, discharged from the n=4 shape (`b3 ≠ 0`) and the
    alignment side condition — no runtime certificates. -/
theorem evm_div_n4_lane_of_shape_native (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  by_cases hsh : (clzResult (b.getLimbN 3)).1 = 0
  · exact evm_div_n4_lane_shift0_v5_of_cert sp base a b x1Val v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem hb3nz hsh halign
      (evm_div_n4_shift0_cert_of_shape a b hb3nz hsh)
  · exact evm_div_n4_lane_shiftNz_v5_of_cert_native sp base a b x1Val v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem hb3nz hsh halign
      (evm_div_n4_shiftNz_cert_of_shape_native a b hb3nz hsh)

end EvmAsm.Evm64
