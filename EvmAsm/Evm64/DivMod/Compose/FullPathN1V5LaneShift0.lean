/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5LaneShift0

  The v5 n=1 DIV lane, shift=0 case: from the stack-dispatch precondition to
  `divStackDispatchPostV5`, over `divCode_noNop_v5`.  Composes the pre lift
  (`n1_dispatchPre_to_pathEntry_v5`, reused from the shift≠0 lane — the entry is
  the same drop-in dispatch entry), the full shift=0 code path
  (`evm_div_n1_full_shift0_spec_v5_noNop`), and the shift=0 post bridge
  (`n1_shift0_post_to_divStackDispatchPost_v5`, with the `hdiv` facts from
  `div_getLimbN_eq_digit_shift0`).  Shift=0 half of `lane_n1`.  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5FullShift0
public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5LaneShiftNz
public import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0QuotientWordLane

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem evm_div_n1_lane_shift0_v5 (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_z : (clzResult b0).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b0).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ := div_getLimbN_eq_digit_shift0 a b a0 a1 a2 a3 b0 b1 b2 b3
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb1z hb2z hb3z hshift_z
  have hpath := evm_div_n1_full_shift0_spec_v5_noNop sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem hbnz hb3z hb2z hb1z hshift_z halign
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n1_dispatchPre_to_pathEntry_v5 sp a b x1Val v5 v6 v7 v10 v11Old a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratch_un0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    delta divStackDispatchPostV5
    exact n1_shift0_post_to_divStackDispatchPost_v5 sp base a b a0 a1 a2 a3 b0 scratchMem
      ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq

/-- The full v5 n=1 DIV lane: combines the shift≠0 and shift=0 halves by
    `by_cases (clzResult b0).1 = 0`.  Both halves share the same dispatch
    precondition (`x9 = 4-4`, `x2 = (clzResult b0).2 >>> 63`) and post
    (`divStackDispatchPostV5`).  This is the `lane_n1` obligation of
    `evm_div_stack_spec_unconditional_of_lanes_v5_div`. -/
theorem evm_div_n1_lane_v5 (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b0).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  by_cases hsh : (clzResult b0).1 = 0
  · exact evm_div_n1_lane_shift0_v5 sp base a b x1Val v5 v6 v7 v10 v11Old
      a0 a1 a2 a3 b0 b1 b2 b3 q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hbnz hb3z hb2z hb1z hsh halign
  · exact evm_div_n1_lane_shiftNz_v5 sp base a b x1Val v5 v6 v7 v10 v11Old
      a0 a1 a2 a3 b0 b1 b2 b3 q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hbnz hb3z hb2z hb1z hsh halign

end EvmAsm.Evm64
