/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShift0CallAddbackMod

  The n=4 v5 MOD lane, shift=0 call+addback-beq branch, from the dispatch
  precondition to `modStackDispatchPostV5` over `modCode_noNop_v5`, taking the
  remainder-correctness facts `hmod0..hmod3` (in single-addback `ab` form) as
  HYPOTHESES.  MOD mirror of `evm_div_n4_lane_shift0_callAddback_of_hdiv`: composes
  the (reused) shiftNz pre-bridge `n4_dispatchPre_to_pathEntry_v5`, the full shift=0
  call+addback MOD path (`evm_mod_n4_full_call_addback_shift0_spec_v5_noNop`), and
  the shift=0 MOD post-bridge (`n4_shift0_post_to_modStackDispatchPost_v5`).  The
  `carry ≠ 0` (single addback) if-branches of the output `un*Out` are resolved to
  `ab` via `n4_shift0_call_addback_first_carry_nz`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5FullShift0CallAddbackMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallSkipShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5Shift0PostBridgeMod
import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallAddbackCarry

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- n=4 v5 MOD lane (shift=0 call+addback branch), from the dispatch pre to
    `modStackDispatchPostV5`, given the remainder-correctness facts (in `ab` form). -/
theorem evm_mod_n4_lane_shift0_callAddback_of_hmod (sp base : Word) (a b : EvmWord)
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
    (hborrow : (if BitVec.ult (0 : Word)
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat (0 : Word) a3 b3
      let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0 b1 b2 b3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - c3) b0 b1 b2 b3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 b0 b1 b2 b3 ≠ 0)
    (hmod0 : (EvmWord.mod a b).getLimbN 0 =
      (addbackN4 (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
        ((0 : Word) - (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2)
        b0 b1 b2 b3).1)
    (hmod1 : (EvmWord.mod a b).getLimbN 1 =
      (addbackN4 (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
        ((0 : Word) - (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2)
        b0 b1 b2 b3).2.1)
    (hmod2 : (EvmWord.mod a b).getLimbN 2 =
      (addbackN4 (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
        ((0 : Word) - (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2)
        b0 b1 b2 b3).2.2.1)
    (hmod3 : (EvmWord.mod a b).getLimbN 3 =
      (addbackN4 (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
        ((0 : Word) - (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2)
        b0 b1 b2 b3).2.2.2.1) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b3).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  -- carry ≠ 0 (single addback), converted to the a.getLimbN / b.getLimbN form the
  -- shift0 first-carry lemma expects.
  have hborrow' : (if BitVec.ult (0 : Word)
      (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2
    then (1 : Word) else 0) ≠ (0 : Word) := by rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]; exact hborrow
  have hshift_z' : (clzResult (b.getLimbN 3)).1 = 0 := by rw [hb3]; exact hshift_z
  have hcarry_nz := n4_shift0_call_addback_first_carry_nz a b hshift_z' hborrow'
  rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] at hcarry_nz
  have hpath := evm_mod_n4_full_call_addback_shift0_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 ((clzResult b3).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_z halign hborrow hcarry2_nz
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n4_dispatchPre_to_pathEntry_v5 sp a b x1Val ((clzResult b3).2 >>> (63 : Nat))
      v5 v6 v7 v10 v11Old a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratchUn0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    unfold fullModN4CallAddbackShift0PostV5 at hq
    -- resolve the single-addback (carry ≠ 0) if-branches: un*Out = ab.
    simp only [if_neg hcarry_nz] at hq
    exact n4_shift0_post_to_modStackDispatchPost_v5 sp a b a0 a1 a2 a3
      _ _ _ _ _ _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 hmod0 hmod1 hmod2 hmod3 h hq

end EvmAsm.Evm64
