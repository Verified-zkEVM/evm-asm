/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNopPreloop

  Preloop setup wrappers for the n=3 v4/no-NOP full DIV path.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathV4NoNop
public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNopMaxCall

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- PhaseAB(n=3) + CLZ over `divCode_noNop_v4`. -/
theorem evm_div_phaseAB_n3_clz_spec_within_v4_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24) base (base + phaseC2Off) (divCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (clzResult b2).2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ (clzResult b2).1) ** (.x7 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word))) := by
  have hAB := evm_div_phaseAB_n3_spec_within_v4_noNop sp base b0 b1 b2 b3
    v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3z hb2nz
  have hCLZ := divK_clz_spec_within_v4_noNop b2 b1 b2 base
  have hCLZf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)))
    (by pcFree) hCLZ
  have hABCLZ := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAB hCLZf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hABCLZ

/-- PhaseAB(n=3) + CLZ + PhaseC2(ntaken) + NormB over `divCode_noNop_v4`. -/
theorem evm_div_n3_to_normB_spec_within_v4_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21) base (base + normAOff) (divCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (normBPost sp (3 : Word) (clzResult b2).1 b0 b1 b2 b3) := by
  let shift := (clzResult b2).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  have hABCLZ := evm_div_phaseAB_n3_clz_spec_within_v4_noNop sp base b0 b1 b2 b3
    v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3z hb2nz
  have hABCLZf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
     ((sp + signExtend12 3992) ↦ₘ shiftMem))
    (by pcFree) hABCLZ
  have hC2 := divK_phaseC2_ntaken_spec_within_v4_noNop sp shift
    ((clzResult b2).2 >>> (63 : Nat)) shiftMem base hshift_nz
  have hC2f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (clzResult b2).2) ** (.x10 ↦ᵣ b3) **
     (.x7 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)))
    (by pcFree) hC2
  have hABC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABCLZf hC2f
  have hNB := divK_normB_full_spec_within_v4_noNop sp b0 b1 b2 b3
    (clzResult b2).2 ((clzResult b2).2 >>> (63 : Nat))
    shift antiShift base
  simp only [normBFullPost_unfold] at hNB
  have hNBf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABC2 hNBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta normBPost; xperm_hyp hq)
    hFull

/-- Full n=3 path from entry to loop body start over `divCode_noNop_v4`
    (shift ≠ 0). -/
theorem evm_div_n3_to_loopSetup_spec_within_v4_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4) base (base + loopBodyOff) (divCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (loopSetupPost sp (3 : Word) (clzResult b2).1 a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b2).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  have hNB := evm_div_n3_to_normB_spec_within_v4_noNop sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem shiftMem hbnz hb3z hb2nz hshift_nz
  have hNBf := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4024) ↦ₘ u4Old))
    (by pcFree) hNB
  have hNormA := divK_normA_full_spec_within_v4_noNop sp a0 a1 a2 a3
    b0' (b0 >>> (antiShift.toNat % 64)) b3 shift antiShift
    u0Old u1Old u2Old u3Old u4Old base
  rw [divKNormAFullPreNoNop_unfold] at hNormA
  simp only [normAFullPost_unfold] at hNormA
  have hNormAf := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
     ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNormA
  have hNA := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by delta normBPost at hp; xperm_hyp hp) hNBf hNormAf
  have hLS := divK_loopSetup_ntaken_spec_within_v4_noNop sp (3 : Word)
    (signExtend12 (4 : BitVec 12) - (4 : Word)) u1 base
    (by decide)
  simp only [divKLoopSetupNtakenPreNoNop_unfold,
      divKLoopSetupNtakenPostNoNop_unfold] at hLS
  have hLSf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
     (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ u0) ** (.x2 ↦ᵣ antiShift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
     ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4024) ↦ₘ u4) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hLS
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hNA hLSf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta loopSetupPost; xperm_hyp hq)
    hFull

/-- v4/no-NOP n=3 preloop setup with exact caller-framed `x1` and the loop
    scratch handoff frame carried explicitly. -/
theorem evm_div_n3_to_loopSetup_spec_within_v4_noNop_exact_x1_scratch_frame
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4) base (base + loopBodyOff)
      (divCode_noNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
        (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      (loopSetupPost sp (3 : Word) (clzResult b2).1 a0 a1 a2 a3 b0 b1 b2 b3 **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) := by
  have hPre :=
    evm_div_n3_to_loopSetup_spec_within_v4_noNop sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      hbnz hb3z hb2nz hshift_nz
  have hFramed := cpsTripleWithin_frameR
    (((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
      (sp + signExtend12 3968 ↦ₘ retMem) **
      (sp + signExtend12 3960 ↦ₘ dMem) **
      (sp + signExtend12 3952 ↦ₘ dloMem) **
      (sp + signExtend12 3944 ↦ₘ scratchUn0) **
      (sp + signExtend12 3936 ↦ₘ scratchMem) **
      (.x1 ↦ᵣ raVal)))
    (by pcFree) hPre
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFramed

/-- n=3 v4/no-NOP path from entry through the exact-x1 loop handoff.

    Legacy compatibility surface: this still consumes the raw normalized
    `Carry2NzAll` package. Final/public v4 n=3 stack work should use the
    selected-carry/R1 siblings below. -/
theorem fullDivN3_preloop_loop_unified_exact_x1_scratch_v4_noNop
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max (fullDivN3NormV b0 b1 b2 b3).1
            (fullDivN3NormV b0 b1 b2 b3).2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
              (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
              (fullDivN3NormV b0 b1 b2 b3).2.2.1)
            (fullDivN3NormV b0 b1 b2 b3).1
            (fullDivN3NormV b0 b1 b2 b3).2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hcarry2 : Carry2NzAll
      (fullDivN3NormV b0 b1 b2 b3).1
      (fullDivN3NormV b0 b1 b2 b3).2.1
      (fullDivN3NormV b0 b1 b2 b3).2.2.1
      (fullDivN3NormV b0 b1 b2 b3).2.2.2) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 448) base (base + denormOff)
      (divCode_noNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
        (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      ((loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) := by
  have hPre := evm_div_n3_to_loopSetup_spec_within_v4_noNop_exact_x1_scratch_frame
    sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz
  have hLoop := evm_div_n3_loop_unified_inst_noNop_exact_x1_v4
    bltu_1 bltu_0 sp base
    (fullDivN3Shift b2) (fullDivN3AntiShift b2)
    (fullDivN3NormV b0 b1 b2 b3).1
    (fullDivN3NormV b0 b1 b2 b3).2.1
    (fullDivN3NormV b0 b1 b2 b3).2.2.1
    (fullDivN3NormV b0 b1 b2 b3).2.2.2
    (fullDivN3NormU a0 a1 a2 a3 b2).1
    (fullDivN3NormU a0 a1 a2 a3 b2).2.1
    (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
    (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
    (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
    (a0 >>> ((fullDivN3AntiShift b2).toNat % 64)) v11Old jMem
    retMem dMem dloMem scratchUn0 scratchMem raVal
    halign hbltu_1 (by cases bltu_1 <;> simpa using hbltu_0) hcarry2
  have hLoopf := cpsTripleWithin_frameR
    ((((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
      ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
      ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1)))
    (by pcFree) hLoop
  have hBridge := loopSetupPost_to_loopN3PreWithScratchV4NoX1_framed
    sp a0 a1 a2 a3 b0 b1 b2 b3 v11Old
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
  have hPre' := cpsTripleWithin_weaken
    (fun h hp => hp)
    hBridge
    hPre
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPre' hLoopf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hq => hq)
    hFull

/-- Selected-carry variant of
    `fullDivN3_preloop_loop_unified_exact_x1_scratch_v4_noNop`.  This keeps
    the preloop proof surface aligned with the lower selected-carry loop
    helper, avoiding the false universal `Carry2NzAll` package. -/
theorem fullDivN3_preloop_loop_unified_exact_x1_scratch_v4_noNop_selectedCarry
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max (fullDivN3NormV b0 b1 b2 b3).1
            (fullDivN3NormV b0 b1 b2 b3).2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
              (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
              (fullDivN3NormV b0 b1 b2 b3).2.2.1)
            (fullDivN3NormV b0 b1 b2 b3).1
            (fullDivN3NormV b0 b1 b2 b3).2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hcarry2_j1 :
      if bltu_1 then
        loopBodyN3CallAddbackCarry2NzV4
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word)
      else
        isAddbackCarry2NzN3Max
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word))
    (hcarry2_j0 :
      match bltu_1 with
      | false =>
        let r1 := iterN3Max
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word)
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV4
            (fullDivN3NormV b0 b1 b2 b3).1
            (fullDivN3NormV b0 b1 b2 b3).2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).1
            r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max
            (fullDivN3NormV b0 b1 b2 b3).1
            (fullDivN3NormV b0 b1 b2 b3).2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).1
            r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      | true =>
        let r1 := iterWithDoubleAddback
          (divKTrialCallV4QHat
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1)
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word)
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV4
            (fullDivN3NormV b0 b1 b2 b3).1
            (fullDivN3NormV b0 b1 b2 b3).2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).1
            r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max
            (fullDivN3NormV b0 b1 b2 b3).1
            (fullDivN3NormV b0 b1 b2 b3).2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).1
            r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 448) base (base + denormOff)
      (divCode_noNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
        (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      ((loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) := by
  have hPre := evm_div_n3_to_loopSetup_spec_within_v4_noNop_exact_x1_scratch_frame
    sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz
  have hLoop :
      cpsTripleWithin 448 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
        (loopN3PreWithScratchV4NoX1 sp jMem (3 : Word)
          (fullDivN3Shift b2) (fullDivN3NormU a0 a1 a2 a3 b2).1
          (a0 >>> ((fullDivN3AntiShift b2).toNat % 64)) v11Old (fullDivN3AntiShift b2)
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word) (fullDivN3NormU a0 a1 a2 a3 b2).1
          (0 : Word) (0 : Word) retMem dMem dloMem scratchUn0 scratchMem **
          (.x1 ↦ᵣ raVal))
        (loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word) (fullDivN3NormU a0 a1 a2 a3 b2).1
          retMem dMem dloMem scratchUn0 scratchMem **
          (.x1 ↦ᵣ raVal)) := by
    cases bltu_1 <;> cases bltu_0
    · exact evm_div_n3_loop_unified_inst_noNop_exact_x1_v4_selectedCarry
        false false sp base
        (fullDivN3Shift b2) (fullDivN3AntiShift b2)
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (a0 >>> ((fullDivN3AntiShift b2).toNat % 64)) v11Old jMem
        retMem dMem dloMem scratchUn0 scratchMem raVal
        halign hbltu_1 (by simpa using hbltu_0) hcarry2_j1 hcarry2_j0
    · exact evm_div_n3_loop_unified_inst_noNop_exact_x1_v4_selectedCarry
        false true sp base
        (fullDivN3Shift b2) (fullDivN3AntiShift b2)
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (a0 >>> ((fullDivN3AntiShift b2).toNat % 64)) v11Old jMem
        retMem dMem dloMem scratchUn0 scratchMem raVal
        halign hbltu_1 (by simpa using hbltu_0) hcarry2_j1 hcarry2_j0
    · exact evm_div_n3_loop_unified_inst_noNop_exact_x1_v4_selectedCarry
        true false sp base
        (fullDivN3Shift b2) (fullDivN3AntiShift b2)
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (a0 >>> ((fullDivN3AntiShift b2).toNat % 64)) v11Old jMem
        retMem dMem dloMem scratchUn0 scratchMem raVal
        halign hbltu_1 (by simpa using hbltu_0) hcarry2_j1 hcarry2_j0
    · exact evm_div_n3_loop_unified_inst_noNop_exact_x1_v4_selectedCarry
        true true sp base
        (fullDivN3Shift b2) (fullDivN3AntiShift b2)
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (a0 >>> ((fullDivN3AntiShift b2).toNat % 64)) v11Old jMem
        retMem dMem dloMem scratchUn0 scratchMem raVal
        halign hbltu_1 (by simpa using hbltu_0) hcarry2_j1 hcarry2_j0
  have hLoopf := cpsTripleWithin_frameR
    ((((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
      ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
      ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1)))
    (by pcFree) hLoop
  have hBridge := loopSetupPost_to_loopN3PreWithScratchV4NoX1_framed
    sp a0 a1 a2 a3 b0 b1 b2 b3 v11Old
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
  have hPre' := cpsTripleWithin_weaken
    (fun h hp => hp)
    hBridge
    hPre
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPre' hLoopf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hq => hq)
    hFull

/-- Opaque preloop-level `j=0` selected-carry premise in the same R1 shape as
    `fullDivN3R1V4`.  Keeping this proposition irreducible avoids theorem-type
    normalization of the full expanded normalized-DIV expression. -/
@[irreducible] def fullDivN3PreloopSelectedCarryJ0R1V4
    (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let r1 := iterN3V4 bltu_1
    (fullDivN3NormV b0 b1 b2 b3).1
    (fullDivN3NormV b0 b1 b2 b3).2.1
    (fullDivN3NormV b0 b1 b2 b3).2.2.1
    (fullDivN3NormV b0 b1 b2 b3).2.2.2
    (fullDivN3NormU a0 a1 a2 a3 b2).2.1
    (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
    (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
    (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
    (0 : Word)
  if bltu_0 then
    loopBodyN3CallAddbackCarry2NzV4
      (fullDivN3NormV b0 b1 b2 b3).1
      (fullDivN3NormV b0 b1 b2 b3).2.1
      (fullDivN3NormV b0 b1 b2 b3).2.2.1
      (fullDivN3NormV b0 b1 b2 b3).2.2.2
      (fullDivN3NormU a0 a1 a2 a3 b2).1
      r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  else
    isAddbackCarry2NzN3Max
      (fullDivN3NormV b0 b1 b2 b3).1
      (fullDivN3NormV b0 b1 b2 b3).2.1
      (fullDivN3NormV b0 b1 b2 b3).2.2.1
      (fullDivN3NormV b0 b1 b2 b3).2.2.2
      (fullDivN3NormU a0 a1 a2 a3 b2).1
      r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

/-- R1-shaped selected-carry variant of
    `fullDivN3_preloop_loop_unified_exact_x1_scratch_v4_noNop_selectedCarry`.
    This keeps the `j=0` carry premise in the same `iterN3V4` shape used by
    `fullDivN3R1V4`, avoiding the expanded match-shaped theorem boundary. -/
theorem fullDivN3_preloop_loop_unified_exact_x1_scratch_v4_noNop_selectedCarryR1
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max (fullDivN3NormV b0 b1 b2 b3).1
            (fullDivN3NormV b0 b1 b2 b3).2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
              (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
              (fullDivN3NormV b0 b1 b2 b3).2.2.1)
            (fullDivN3NormV b0 b1 b2 b3).1
            (fullDivN3NormV b0 b1 b2 b3).2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hcarry2_j1 :
      if bltu_1 then
        loopBodyN3CallAddbackCarry2NzV4
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word)
      else
        isAddbackCarry2NzN3Max
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word))
    (hcarry2_j0 :
      fullDivN3PreloopSelectedCarryJ0R1V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 448) base (base + denormOff)
      (divCode_noNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
        (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      ((loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) := by
  have hPre := evm_div_n3_to_loopSetup_spec_within_v4_noNop_exact_x1_scratch_frame
    sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz
  have hcarry2_j0' :
      let r1 := iterN3V4 bltu_1
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
      if bltu_0 then
        loopBodyN3CallAddbackCarry2NzV4
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).1
          r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      else
        isAddbackCarry2NzN3Max
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).1
          r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
    rw [fullDivN3PreloopSelectedCarryJ0R1V4] at hcarry2_j0
    exact hcarry2_j0
  have hLoop :
      cpsTripleWithin 448 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
        (loopN3PreWithScratchV4NoX1 sp jMem (3 : Word)
          (fullDivN3Shift b2) (fullDivN3NormU a0 a1 a2 a3 b2).1
          (a0 >>> ((fullDivN3AntiShift b2).toNat % 64)) v11Old (fullDivN3AntiShift b2)
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word) (fullDivN3NormU a0 a1 a2 a3 b2).1
          (0 : Word) (0 : Word) retMem dMem dloMem scratchUn0 scratchMem **
          (.x1 ↦ᵣ raVal))
        (loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word) (fullDivN3NormU a0 a1 a2 a3 b2).1
          retMem dMem dloMem scratchUn0 scratchMem **
          (.x1 ↦ᵣ raVal)) :=
    evm_div_n3_loop_unified_inst_noNop_exact_x1_v4_selectedCarryR1
      bltu_1 bltu_0 sp base
      (fullDivN3Shift b2) (fullDivN3AntiShift b2)
      (fullDivN3NormV b0 b1 b2 b3).1
      (fullDivN3NormV b0 b1 b2 b3).2.1
      (fullDivN3NormV b0 b1 b2 b3).2.2.1
      (fullDivN3NormV b0 b1 b2 b3).2.2.2
      (fullDivN3NormU a0 a1 a2 a3 b2).1
      (fullDivN3NormU a0 a1 a2 a3 b2).2.1
      (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
      (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
      (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
      (a0 >>> ((fullDivN3AntiShift b2).toNat % 64)) v11Old jMem
      retMem dMem dloMem scratchUn0 scratchMem raVal
      halign hbltu_1 (by cases bltu_1 <;> simpa using hbltu_0) hcarry2_j1 hcarry2_j0'
  have hLoopf := cpsTripleWithin_frameR
    ((((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
      ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
      ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1)))
    (by pcFree) hLoop
  have hBridge := loopSetupPost_to_loopN3PreWithScratchV4NoX1_framed
    sp a0 a1 a2 a3 b0 b1 b2 b3 v11Old
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
  have hPre' := cpsTripleWithin_weaken
    (fun h hp => hp)
    hBridge
    hPre
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPre' hLoopf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hq => hq)
    hFull

end EvmAsm.Evm64
