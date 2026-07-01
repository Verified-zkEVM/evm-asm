/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5ToDenormShift0CallAddbackMod

  n=4 v5 MOD shift=0 preloop + call+addback-beq loop body, `base → denormOff` over
  `modCode_noNop_v5`.  MOD mirror of `evm_div_n4_preloop_call_addback_shift0_spec_v5_noNop`
  (FullPathN4V5ToDenormShift0CallAddback), and the call+addback counterpart of the
  MOD shift=0 call+skip path (FullPathN4V5ToDenormShift0CallSkipMod): composes the
  n=4 shift=0 MOD preloop (`evm_mod_n4_to_loopSetup_shift0_spec_v5_noNop`,
  base→loopBodyOff) with the GENERIC call+addback loop body over `modCode_noNop_v5`
  (`divK_loop_body_n4_call_addback_j0_beq_norm_v5_noNop_modCode`, loopBodyOff→denormOff)
  over the RAW divisor `(b0,b1,b2,b3)` and shift=0 u-window `(a0,a1,a2,a3, uTop=0)`.
  The op-agnostic loop-body post `preloopCallAddbackShift0PostN4V5` is reused verbatim.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5PreloopShift0Mod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopCallAddbackMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5ToDenormShift0CallAddback

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- n=4 v5 MOD shift=0 pre-loop + call+addback-beq loop body over `modCode_noNop_v5`:
    base → denormOff.  MOD mirror of `evm_div_n4_preloop_call_addback_shift0_spec_v5_noNop`. -/
theorem evm_mod_n4_preloop_call_addback_shift0_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
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
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 b0 b1 b2 b3 ≠ 0) :
    cpsTripleWithin (((8 + 21 + 24 + 4) + 13) + 234) base (base + denormOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1)
      (preloopCallAddbackShift0PostN4V5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) := by
  have hbltu : BitVec.ult (0 : Word) b3 = true := by
    have hb3pos : 0 < b3.toNat := Nat.pos_of_ne_zero (fun h => hb3nz (by
      apply BitVec.eq_of_toNat_eq; simpa using h))
    simpa [BitVec.ult, BitVec.toNat_ofNat] using hb3pos
  have hPre := evm_mod_n4_to_loopSetup_shift0_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz hb3nz hshift_z
  have hPreF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratchUn0) **
     (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1)
    (by pcFree) hPre
  have hLoop := divK_loop_body_n4_call_addback_j0_beq_norm_v5_noNop_modCode sp base
    jMem (4 : Word) (clzResult b3).1 ((clzResult b3).2 >>> (63 : Nat)) b3 v11Old
    (signExtend12 (0 : BitVec 12) - (clzResult b3).1)
    b0 b1 b2 b3 a0 a1 a2 a3 (0 : Word) (0 : Word)
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow hcarry2_nz
  have hLoopF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1))
    (by pcFree) hLoop
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [show signExtend12 (4 : BitVec 12) - (4 : Word) = (0 : Word) from by decide] at hp
      rw [loopBodyN4CallJ0NormPre_unfold]
      xperm_hyp hp) hPreF hLoopF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopCallAddbackShift0PostN4V5; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
