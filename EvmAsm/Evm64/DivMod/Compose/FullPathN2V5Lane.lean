/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5Lane

  The v5 n=2 DIV lane combiner: case-splits on the normalization shift
  (`(clzResult (b.getLimbN 1)).1 = 0`), delegating to the proven shift≠0 lane
  (`evm_div_n2_lane_shiftNz_v5`, #7465) and to the shift=0 lane (supplied as a
  hypothesis, to be discharged once the shift=0 path is assembled).  Produces the
  full `N2`-shape lane in the form the unconditional scaffold
  (`evm_div_stack_spec_unconditional_of_lanes_v5_div`) consumes.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5LaneShiftNz

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- n=2 lane = shift=0 lane ⊕ shift≠0 lane (#7465), combined by `by_cases` on the
    normalization shift. -/
theorem evm_div_n2_lane_v5 (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1nz : b.getLimbN 1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (shift0lane : (clzResult (b.getLimbN 1)).1 = 0 →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
          ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
          q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostV5 sp a b)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  by_cases hsh : (clzResult (b.getLimbN 1)).1 = 0
  · exact shift0lane hsh
  · exact evm_div_n2_lane_shiftNz_v5 sp base a b raVal v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hbnz hb3z hb2z hb1nz hsh halign

end EvmAsm.Evm64
