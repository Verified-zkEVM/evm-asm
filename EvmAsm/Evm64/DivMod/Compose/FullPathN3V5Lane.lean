/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5Lane

  The complete v5 n=3 DIV lane: from the stack-dispatch precondition
  `divModStackDispatchPreNoX1` to `divStackDispatchPostV5` over `divCode_noNop_v5`,
  for an n=3 divisor (`b3 = 0`, `b2 ≠ 0`).  Dispatches on the normalization shift
  `(clzResult b2).1 = 0` between the two proven halves:
    - shift=0  → `evm_div_n3_lane_shift0_v5`  (#7564),
    - shift≠0  → `evm_div_n3_lane_shiftNz_v5` (#7550).
  n=3 analog of `evm_div_n2_lane_v5` (FullPathN2V5Lane), but with the shift=0 case
  discharged in-place (both halves now exist) rather than taken as a hypothesis.
  Bead `evm-asm-wbc4i.9.3.3.5` (piece 4).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5LaneShiftNz
public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5LaneShift0

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The complete v5 n=3 DIV lane (both normalization-shift cases). -/
theorem evm_div_n3_lane_v5 (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  by_cases hsh : (clzResult (b.getLimbN 2)).1 = 0
  · exact evm_div_n3_lane_shift0_v5 sp base a b raVal v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hb3z hb2nz hsh halign
  · exact evm_div_n3_lane_shiftNz_v5 sp base a b raVal v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hb3z hb2nz hsh halign

end EvmAsm.Evm64
