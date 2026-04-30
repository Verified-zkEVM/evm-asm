/-
  EvmAsm.Evm64.DivMod.Compose.ModFullPathN2LoopUnified

  MOD n=2 full-path composition using the shared N2 bundled loop bridge.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Full
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN2
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

theorem divK_loop_n2_unified_modCode (bltu_2 bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_1 u0_orig_0
     q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : bltu_2 = BitVec.ult u2 v1)
    (hbltu_1 : bltu_1 = BitVec.ult
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 606 (base + loopBodyOff) (base + denormOff) (modCode base)
      (loopN2PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2UnifiedPost bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) :=
  cpsTripleWithin_extend_code (hmono := sharedDivModCode_sub_modCode)
    (divK_loop_n2_unified_spec_within bltu_2 bltu_1 bltu_0
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign
      hbltu_2 hbltu_1 hbltu_0 hcarry2)

private theorem evm_mod_n2_loop_unified_inst
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift v0' v1' v2' v3' u0S u1S u2S u3S u4_s : Word)
    (v10_val v11Old jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : bltu_2 = BitVec.ult u4_s v1')
    (hbltu_1 : bltu_1 = BitVec.ult
      (iterN2 bltu_2 v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1 v1')
    (hbltu_0 : bltu_0 = BitVec.ult
      (iterN2 bltu_1 v0' v1' v2' v3' u1S
        (iterN2 bltu_2 v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
        (iterN2 bltu_2 v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
        (iterN2 bltu_2 v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
        (iterN2 bltu_2 v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
      v1')
    (hcarry2 : Carry2NzAll v0' v1' v2' v3') :
    cpsTripleWithin 606 (base + loopBodyOff) (base + denormOff) (modCode base)
      (loopN2PreWithScratch sp jMem (2 : Word) shift u0S v10_val v11Old antiShift
        v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)
        u1S u0S (0 : Word) (0 : Word) (0 : Word)
        retMem dMem dloMem scratch_un0)
      (loopN2UnifiedPost bltu_2 bltu_1 bltu_0 sp base
        v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)
        u1S u0S retMem dMem dloMem scratch_un0) :=
  divK_loop_n2_unified_modCode bltu_2 bltu_1 bltu_0
    sp jMem (2 : Word) shift u0S v10_val v11Old antiShift
    v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)
    u1S u0S (0 : Word) (0 : Word) (0 : Word)
    retMem dMem dloMem scratch_un0 base halign
    hbltu_2 hbltu_1 hbltu_0 hcarry2

theorem evm_mod_n2_preloop_loop_unified_spec
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))) :
    cpsTripleWithin 709 base (base + denormOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
       ((sp + signExtend12 3968) ↦ₘ retMem) **
       ((sp + signExtend12 3960) ↦ₘ dMem) **
       ((sp + signExtend12 3952) ↦ₘ dloMem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (preloopN2UnifiedPost bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0) := by
  have hPre := evm_mod_n2_to_loopSetup_spec_within sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz hb3z hb2z hb1nz hshift_nz
  have hPreF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hPre
  have hLoop := evm_mod_n2_loop_unified_inst bltu_2 bltu_1 bltu_0 sp base
    (clzResult b1).1 (signExtend12 (0 : BitVec 12) - (clzResult b1).1)
    (b0 <<< (((clzResult b1).1).toNat % 64))
    ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
    ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
    ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
    (a0 <<< (((clzResult b1).1).toNat % 64))
    ((a1 <<< (((clzResult b1).1).toNat % 64)) ||| (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
    ((a2 <<< (((clzResult b1).1).toNat % 64)) ||| (a1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
    ((a3 <<< (((clzResult b1).1).toNat % 64)) ||| (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
    (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))
    (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))
    v11Old jMem
    retMem dMem dloMem scratch_un0
    halign
    hbltu_2 hbltu_1 hbltu_0 hcarry2
  have hLoopF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))
    (by pcFree) hLoop
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopSetupPost at hp
      simp only [x1_val_n2] at hp
      delta loopN2PreWithScratch loopN2Pre
      simp only []
      simp only [n2_ub2_off0, n2_ub2_off4088, n2_ub2_off4080,
                  n2_ub2_off4072, n2_ub2_off4064,
                  n3_ub1_off0,
                  n3_ub0_off0,
                  n2_qa2, n3_qa1, n3_qa0,
                  se12_32, se12_40, se12_48, se12_56]
      xperm_hyp hp) hPreF hLoopF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopN2UnifiedPost; xperm_hyp hq)
    hFull

@[irreducible]
def fullModN2DenormPost (bltu_2 bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN2Shift b1
  let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  denormModPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + signExtend12 4088) ↦ₘ r0.1) **
  ((sp + signExtend12 4080) ↦ₘ r1.1) **
  ((sp + signExtend12 4072) ↦ₘ r2.1) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word))

@[irreducible]
def fullModN2UnifiedPost (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  fullModN2DenormPost bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
  fullDivN2Frame bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratch_un0

theorem evm_mod_n2_denorm_epilogue_bundled_spec
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : fullDivN2Shift b1 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (modCode base)
      (fullDivN2DenormPre bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3)
      (fullModN2DenormPost bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := fullDivN2Shift b1
  let v := fullDivN2NormV b0 b1 b2 b3
  let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let c3 := fullDivN2C3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  have h := evm_mod_preamble_denorm_epilogue_spec_within sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3 v.1 v.2.1 v.2.2.1 v.2.2.2 hshift_nz
  have hF := cpsTripleWithin_frameR
    (((sp + signExtend12 4088) ↦ₘ r0.1) **
     ((sp + signExtend12 4080) ↦ₘ r1.1) **
     ((sp + signExtend12 4072) ↦ₘ r2.1) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)))
    (by pcFree) h
  exact cpsTripleWithin_weaken
    (fun h hp => by
      subst shift; subst v; subst r2; subst r1; subst r0; subst c3
      delta fullDivN2DenormPre at hp
      simp only [se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp)
    (fun h hq => by
      subst shift; subst r2; subst r1; subst r0
      delta fullModN2DenormPost
      xperm_hyp hq)
    hF

theorem fullModN2UnifiedPost_weaken (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (h : PartialState)
    (hq :
      (fullModN2DenormPost bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
       fullDivN2Frame bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
         retMem dMem dloMem scratch_un0) h) :
    fullModN2UnifiedPost bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
      retMem dMem dloMem scratch_un0 h := by
  delta fullModN2UnifiedPost
  exact hq

theorem evm_mod_n2_full_unified_spec
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))) :
    cpsTripleWithin 744 base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
       ((sp + signExtend12 3968) ↦ₘ retMem) **
       ((sp + signExtend12 3960) ↦ₘ dMem) **
       ((sp + signExtend12 3952) ↦ₘ dloMem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (fullModN2UnifiedPost bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0) := by
  have hA := evm_mod_n2_preloop_loop_unified_spec bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz halign hbltu_2 hbltu_1 hbltu_0 hcarry2
  have hshift_nz' : fullDivN2Shift b1 ≠ 0 := by
    rw [fullDivN2Shift_unfold]
    exact hshift_nz
  have hB := evm_mod_n2_denorm_epilogue_bundled_spec
    bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz'
  have hBF := cpsTripleWithin_frameR
    (fullDivN2Frame bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
      retMem dMem dloMem scratch_un0)
    (by
      delta fullDivN2Frame fullDivN2ScratchFinal fullDivN2Scratch0 fullDivN2Scratch1
        fullDivN2Scratch2 n2ScratchRet n2ScratchD n2ScratchDLo n2ScratchUn0
      pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => preloopN2UnifiedPost_to_fullDivN2DenormPre_frame
      bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
      retMem dMem dloMem scratch_un0 h hp)
    hA hBF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq =>
      fullModN2UnifiedPost_weaken bltu_2 bltu_1 bltu_0
        sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h hq)
    hFull

end EvmAsm.Evm64
