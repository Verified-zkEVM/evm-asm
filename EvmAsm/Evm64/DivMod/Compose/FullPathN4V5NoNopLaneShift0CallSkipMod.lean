/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShift0CallSkipMod

  The n=4 v5 MOD lane, shift=0 call+skip branch, from the dispatch precondition to
  `modStackDispatchPostV5` over `modCode_noNop_v5`, taking the remainder-correctness
  facts `hmod0..hmod3` as HYPOTHESES.  MOD mirror of
  `evm_div_n4_lane_shift0_callSkip_of_hdiv`: composes the (reused) shiftNz pre-bridge
  `n4_dispatchPre_to_pathEntry_v5`, the full shift=0 call+skip MOD path
  (`evm_mod_n4_full_call_skip_shift0_spec_v5_noNop`), and the shift=0 MOD post-bridge
  (`n4_shift0_post_to_modStackDispatchPost_v5`, remainder in the output slots).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5FullShift0CallSkipMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallSkipShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5Shift0PostBridgeMod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- n=4 v5 MOD lane (shift=0 call+skip branch), from the dispatch pre to
    `modStackDispatchPostV5`, given the remainder-correctness facts. -/
theorem evm_mod_n4_lane_shift0_callSkip_of_hmod (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3 (0 : Word))
    (hmod0 : (EvmWord.mod a b).getLimbN 0 =
      (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).1)
    (hmod1 : (EvmWord.mod a b).getLimbN 1 =
      (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.1)
    (hmod2 : (EvmWord.mod a b).getLimbN 2 =
      (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1)
    (hmod3 : (EvmWord.mod a b).getLimbN 3 =
      (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b3).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  have hpath := evm_mod_n4_full_call_skip_shift0_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 ((clzResult b3).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_z halign hborrow
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n4_dispatchPre_to_pathEntry_v5 sp a b x1Val ((clzResult b3).2 >>> (63 : Nat))
      v5 v6 v7 v10 v11Old a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratchUn0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    unfold fullModN4CallSkipShift0PostV5 at hq
    exact n4_shift0_post_to_modStackDispatchPost_v5 sp a b a0 a1 a2 a3
      _ _ _ _ _ _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 hmod0 hmod1 hmod2 hmod3 h hq

end EvmAsm.Evm64
