/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShift0Mod

  The n=4 v5 MOD lane, shift=0 case, UNCONDITIONAL on the n=4 shape: from the
  dispatch precondition to `modStackDispatchPostV5` over `modCode_noNop_v5`, given
  only `b.getLimbN 3 ≠ 0`, `shift = 0`, and the alignment side condition.  MOD
  counterpart of `evm_div_n4_lane_shift0_v5_of_cert` fed by
  `evm_div_n4_shift0_cert_of_shape`, fused into one theorem: internally `by_cases`
  the mulsub borrow flag `c3`, deriving the MOD remainder facts from the shape via
  the shift=0 skip/addback MOD word lanes (no separate certificate).
  * `c3 = 0` → call+skip (no borrow), `n4_shift0_call_skip_mod_getLimbN_v5`;
  * `c3 ≠ 0` → call+addback, `n4_shift0_call_addback_mod_getLimbN_v5`, with the
    `carry2` obligation vacuously discharged (`n4_shift0_call_addback_first_carry_nz`).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShift0CallSkipMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShift0CallAddbackMod
import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallSkipModWordLane
import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallAddbackModWordLane

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (ult_iff)

/-- n=4 v5 MOD lane, shift=0 case, discharged from the n=4 shape (`b3 ≠ 0`),
    `shift = 0`, and the alignment side condition — no runtime certificates. -/
theorem evm_mod_n4_lane_shift0_v5 (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  have hbnz : b ≠ 0 := fun h => hb3nz (by rw [h]; exact EvmWord.getLimbN_zero 3)
  have hbnz_lor : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    fun h => hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hshift_z' : (clzResult (b.getLimbN 3)).1 = 0 := hshift_z
  by_cases hc3 : (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = 0
  · -- call+skip branch (no borrow).
    have hsb : mulsubN4NoBorrow (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) (0 : Word) := by
      unfold mulsubN4NoBorrow; rw [hc3]; decide
    obtain ⟨hmod0, hmod1, hmod2, hmod3⟩ :=
      n4_shift0_call_skip_mod_getLimbN_v5 a b hbnz hshift_z' hsb
    exact evm_mod_n4_lane_shift0_callSkip_of_hmod sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hbnz_lor hb3nz hshift_z' halign hsb hmod0 hmod1 hmod2 hmod3
  · -- call+addback branch (borrow fires).
    have hborrow : (if BitVec.ult (0 : Word)
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word) := by
      have hut : BitVec.ult (0 : Word)
          (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = true := by
        rw [ult_iff]
        exact Nat.pos_of_ne_zero (fun h => hc3 (BitVec.eq_of_toNat_eq (by rw [h]; rfl)))
      rw [hut]; decide
    have hcarry2 :
        let qHat := divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3)
        let ms := mulsubN4 qHat (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        let c3 := ms.2.2.2.2
        let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - c3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≠ 0 :=
      fun hc0 => absurd hc0 (n4_shift0_call_addback_first_carry_nz a b hshift_z' hborrow)
    obtain ⟨hmod0, hmod1, hmod2, hmod3⟩ :=
      n4_shift0_call_addback_mod_getLimbN_v5 a b hbnz hshift_z' hborrow
    exact evm_mod_n4_lane_shift0_callAddback_of_hmod sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hbnz_lor hb3nz hshift_z' halign hborrow hcarry2 hmod0 hmod1 hmod2 hmod3

end EvmAsm.Evm64
