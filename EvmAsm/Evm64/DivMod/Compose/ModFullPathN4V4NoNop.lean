/-
  EvmAsm.Evm64.DivMod.Compose.ModFullPathN4V4NoNop

  v4/no-NOP wrappers for the n=4 MOD loop-body surfaces.
-/

import EvmAsm.Evm64.DivMod.Compose.V4Code
import EvmAsm.Evm64.DivMod.Compose.FullPath
import EvmAsm.Evm64.DivMod.Compose.ModPhaseABN4V4NoNop
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Loop
import EvmAsm.Evm64.DivMod.LoopIterN4MaxV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN4CallV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN4AddbackV4NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (bv64_4mul_3 se12_0 se12_8 se12_16 se12_24 se12_32 se12_40 se12_48 se12_56)

/-- Phase C2 not-taken over the no-NOP v4 MOD code bundle. -/
theorem divK_phaseC2_ntaken_spec_within_mod_v4_noNop
    (sp shift v2 shiftMem : Word) (base : Word) (hshift_nz : shift ≠ 0) :
    cpsTripleWithin 4 (base + phaseC2Off) (base + normBOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_spec_within sp shift v2 shiftMem 172 (base + phaseC2Off)
  have hbodye := cpsTripleWithin_extend_code (hmono := by
    unfold divK_phaseC2_code
    intro a i h
    exact sharedNoNop_v4_b3_mod a i h) hbody
  have hbeq_raw := beq_spec_gen_within .x6 .x0 172 shift (0 : Word) (base + phaseC2Off + 12)
  rw [show (base + phaseC2Off + 12 : Word) + signExtend13 172 = base + copyAUOff from by rv64_addr,
      show (base + phaseC2Off + 12 : Word) + 4 = base + normBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranchWithin_ntakenStripPure2 hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _).mp h_rest).2 (show shift ≠ (0 : Word) from hshift_nz))
  have hbeq := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact sharedNoNop_v4_b3_mod a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + phaseC2Off) (divK_phaseC2 172) 3
          (by decide) (by decide)
        rw [bv64_4mul_3] at hlookup
        exact hlookup) a i h)) hbeq_clean
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbodye hbeqf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hC2

/-- Phase C2 not-taken over the full v4 MOD code bundle. -/
theorem divK_phaseC2_ntaken_spec_within_mod_v4
    (sp shift v2 shiftMem : Word) (base : Word) (hshift_nz : shift ≠ 0) :
    cpsTripleWithin 4 (base + phaseC2Off) (base + normBOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_phaseC2_ntaken_spec_within_mod_v4_noNop sp shift v2 shiftMem base hshift_nz)

/-- First half of NormB over the no-NOP v4 MOD code bundle. -/
private theorem divK_normB_half1_within_mod_v4_noNop
    (sp b0 b1 b2 b3 v5 v7 shift antiShift : Word) (base : Word) :
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    cpsTripleWithin 12 (base + normBOff) (base + normBOff + 48) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b2') ** (.x7 ↦ᵣ (b1 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3')) := by
  intro b3' b2'
  have hm1 := divK_normB_merge_spec_within 56 48 sp b3 b2 v5 v7 shift antiShift (base + normBOff)
  simp only [se12_56, se12_48] at hm1
  have hm1e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b4_mod a i
      (CodeReq.ofProg_mono_sub (base + normBOff) (base + normBOff) divK_normB
        (divK_normB_merge_prog 56 48) 0
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm1
  have hm1ef := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1))
    (by pcFree) hm1e
  have hm2 := divK_normB_merge_spec_within 48 40 sp b2 b1 b3' (b2 >>> (antiShift.toNat % 64))
    shift antiShift (base + normBOff + 24)
  simp only [se12_48, se12_40] at hm2
  rw [show (base + normBOff + 24 : Word) + 24 = base + normBOff + 48 from by bv_addr] at hm2
  have hm2e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b4_mod a i
      (CodeReq.ofProg_mono_sub (base + normBOff) (base + normBOff + 24) divK_normB
        (divK_normB_merge_prog 48 40) 6
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm2
  have hm2ef := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ b0) ** ((sp + 56) ↦ₘ b3'))
    (by pcFree) hm2e
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hm1ef hm2ef
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

/-- Second half of NormB over the no-NOP v4 MOD code bundle. -/
private theorem divK_normB_half2_within_mod_v4_noNop
    (sp b0 b1 b2' b3' shift antiShift : Word) (base : Word) :
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    cpsTripleWithin 9 (base + normBOff + 48) (base + normAOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b2') ** (.x7 ↦ᵣ (b1 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3'))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3')) := by
  intro b1' b0'
  have hm3 := divK_normB_merge_spec_within 40 32 sp b1 b0
    b2' (b1 >>> (antiShift.toNat % 64)) shift antiShift (base + normBOff + 48)
  simp only [se12_40, se12_32] at hm3
  rw [show (base + normBOff + 48 : Word) + 24 = base + normBOff + 72 from by bv_addr] at hm3
  have hm3e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b4_mod a i
      (CodeReq.ofProg_mono_sub (base + normBOff) (base + normBOff + 48) divK_normB
        (divK_normB_merge_prog 40 32) 12
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm3
  have hm3ef := cpsTripleWithin_frameR
    (((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3'))
    (by pcFree) hm3e
  have hl := divK_normB_last_spec_within 32 sp b0 b1' shift (base + normBOff + 72)
  simp only [se12_32] at hl
  rw [show (base + normBOff + 72 : Word) + 12 = base + normAOff from by bv_addr] at hl
  have hle := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b4_mod a i
      (CodeReq.ofProg_mono_sub (base + normBOff) (base + normBOff + 72) divK_normB
        (divK_normB_last_prog 32) 18
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hl
  have hlef := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) ** (.x2 ↦ᵣ antiShift) **
     ((sp + 40) ↦ₘ b1') ** ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3'))
    (by pcFree) hle
  have h34 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hm3ef hlef
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h34

/-- NormB over the no-NOP v4 MOD code bundle. -/
theorem divK_normB_full_spec_within_mod_v4_noNop
    (sp b0 b1 b2 b3 v5 v7 shift antiShift : Word) (base : Word) :
    cpsTripleWithin 21 (base + normBOff) (base + normAOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (normBFullPost sp b0 b1 b2 b3 shift antiShift) := by
  rw [normBFullPost_unfold]
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  have h1 := divK_normB_half1_within_mod_v4_noNop sp b0 b1 b2 b3 v5 v7 shift antiShift base
  have h2 := divK_normB_half2_within_mod_v4_noNop sp b0 b1 b2' b3' shift antiShift base
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) h1 h2)

/-- NormB over the full v4 MOD code bundle. -/
theorem divK_normB_full_spec_within_mod_v4
    (sp b0 b1 b2 b3 v5 v7 shift antiShift : Word) (base : Word) :
    cpsTripleWithin 21 (base + normBOff) (base + normAOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (normBFullPost sp b0 b1 b2 b3 shift antiShift) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_normB_full_spec_within_mod_v4_noNop sp b0 b1 b2 b3 v5 v7 shift antiShift base)

/-- MOD n=4 path from entry to NormA over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_n4_to_normB_spec_within_v4_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21) base (base + normAOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (normBPost sp (4 : Word) (clzResult b3).1 b0 b1 b2 b3) := by
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  have hABCLZ := evm_mod_phaseAB_n4_clz_spec_within_v4_noNop sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3nz
  have hABCLZf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
     ((sp + signExtend12 3992) ↦ₘ shiftMem))
    (by pcFree) hABCLZ
  have hC2 := divK_phaseC2_ntaken_spec_within_mod_v4_noNop sp shift ((clzResult b3).2 >>> (63 : Nat))
    shiftMem base hshift_nz
  have hC2f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (clzResult b3).2) ** (.x10 ↦ᵣ b3) **
     (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)))
    (by pcFree) hC2
  have hABC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABCLZf hC2f
  have hNB := divK_normB_full_spec_within_mod_v4_noNop sp b0 b1 b2 b3
    (clzResult b3).2 ((clzResult b3).2 >>> (63 : Nat))
    shift antiShift base
  simp only [normBFullPost_unfold] at hNB
  have hNBf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABC2 hNBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta normBPost; xperm_hyp hq)
    hFull

/-- MOD n=4 path from entry to NormA over the full v4 MOD code bundle. -/
theorem evm_mod_n4_to_normB_spec_within_v4 (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21) base (base + normAOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (normBPost sp (4 : Word) (clzResult b3).1 b0 b1 b2 b3) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (evm_mod_n4_to_normB_spec_within_v4_noNop sp base b0 b1 b2 b3 v5 v6 v7 v10
      q0 q1 q2 q3 u5 u6 u7 nMem shiftMem hbnz hb3nz hshift_nz)

/-- NormA over the no-NOP v4 MOD code bundle. -/
theorem divK_normA_full_spec_within_mod_v4_noNop (sp a0 a1 a2 a3 v5 v7 v10 shift antiShift : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word) :
    cpsTripleWithin 21 (base + normAOff) (base + loopSetupOff) (modCode_noNop_v4 base)
      (divKNormAFullPreNoNop sp v5 v7 v10 shift antiShift
        a0 a1 a2 a3 u0Old u1Old u2Old u3Old u4Old)
      (normAFullPost sp a0 a1 a2 a3 shift antiShift) := by
  rw [divKNormAFullPreNoNop_unfold, normAFullPost_unfold]
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  have htop := divK_normA_top_spec_within 24 4024 sp a3 v5 v7 antiShift u4Old (base + normAOff)
  simp only [se12_24] at htop
  have htope := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b5_mod a i
      (CodeReq.ofProg_mono_sub (base + normAOff) (base + normAOff) (divK_normA 40)
        (divK_normA_top_prog 24 4024) 0
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) htop
  have htopef := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ v10) ** (.x6 ↦ᵣ shift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) **
     ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4056) ↦ₘ u0Old))
    (by pcFree) htope
  have hma1 := divK_normA_mergeA_spec_within 16 4032 sp a3 a2 u4 v10 shift antiShift u3Old (base + normAOff + 12)
  simp only [se12_16] at hma1
  rw [show (base + normAOff + 12 : Word) + 20 = base + normAOff + 32 from by bv_addr] at hma1
  have hma1e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b5_mod a i
      (CodeReq.ofProg_mono_sub (base + normAOff) (base + normAOff + 12) (divK_normA 40)
        (divK_normA_mergeA_prog 16 4032) 3
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hma1
  have hma1ef := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4056) ↦ₘ u0Old))
    (by pcFree) hma1e
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) htopef hma1ef
  have hmb := divK_normA_mergeB_spec_within 8 4040 sp a2 a1 u3 (a2 >>> (antiShift.toNat % 64))
    shift antiShift u2Old (base + normAOff + 32)
  simp only [se12_8] at hmb
  rw [show (base + normAOff + 32 : Word) + 20 = base + normAOff + 52 from by bv_addr] at hmb
  have hmbe := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b5_mod a i
      (CodeReq.ofProg_mono_sub (base + normAOff) (base + normAOff + 32) (divK_normA 40)
        (divK_normA_mergeB_prog 8 4040) 8
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hmb
  have hmbef := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4048) ↦ₘ u1Old) ** ((sp + signExtend12 4056) ↦ₘ u0Old))
    (by pcFree) hmbe
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 hmbef
  have hma2 := divK_normA_mergeA_spec_within 0 4048 sp a1 a0 u2 (a1 >>> (antiShift.toNat % 64))
    shift antiShift u1Old (base + normAOff + 52)
  simp only [se12_0] at hma2
  rw [show (base + normAOff + 52 : Word) + 20 = base + normAOff + 72 from by bv_addr] at hma2
  have hma2e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b5_mod a i
      (CodeReq.ofProg_mono_sub (base + normAOff) (base + normAOff + 52) (divK_normA 40)
        (divK_normA_mergeA_prog 0 4048) 13
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hma2
  have hma2ef := cpsTripleWithin_frameR
    (((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4056) ↦ₘ u0Old))
    (by pcFree) hma2e
  have h1234 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hma2ef
  have hlast := divK_normA_last_spec_within 4056 sp a0 shift u0Old (base + normAOff + 72)
  rw [show (base + normAOff + 72 : Word) + 8 = base + normAOff + 80 from by bv_addr] at hlast
  have hlaste := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b5_mod a i
      (CodeReq.ofProg_mono_sub (base + normAOff) (base + normAOff + 72) (divK_normA 40)
        (divK_normA_last_prog 4056) 18
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hlast
  have hlastef := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ u1) ** (.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) ** (.x2 ↦ᵣ antiShift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1))
    (by pcFree) hlaste
  have h12345 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234 hlastef
  have hjal := jal_x0_spec_gen_within 40 (base + normAOff + 80)
  rw [show (base + normAOff + 80 : Word) + signExtend21 40 = base + loopSetupOff from by rv64_addr] at hjal
  have hjale := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact sharedNoNop_v4_b5_mod a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + normAOff) (divK_normA 40) 20
          (by decide) (by decide)
        rw [show (base + normAOff : Word) + BitVec.ofNat 64 (4 * 20) = base + normAOff + 80 from by bv_addr]
          at hlookup
        exact hlookup) a i h)) hjal
  let postAll := (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u1) ** (.x7 ↦ᵣ u0) **
    (.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
    (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
    ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
    ((sp + signExtend12 4056) ↦ₘ u0)
  have hjalef := cpsTripleWithin_frameR postAll (by pcFree) hjale
  have hjal_clean : cpsTripleWithin 1 (base + normAOff + 80) (base + loopSetupOff) (modCode_noNop_v4 base) postAll postAll :=
    cpsTripleWithin_weaken
      (fun h hp => by show (empAssertion ** postAll) h; rw [sepConj_emp_left']; exact hp)
      (fun h hp => by rw [sepConj_emp_left'] at hp; exact hp)
      hjalef
  have h123456 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345 hjal_clean
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h123456

/-- NormA over the full v4 MOD code bundle. -/
theorem divK_normA_full_spec_within_mod_v4 (sp a0 a1 a2 a3 v5 v7 v10 shift antiShift : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word) :
    cpsTripleWithin 21 (base + normAOff) (base + loopSetupOff) (modCode_v4 base)
      (divKNormAFullPreNoNop sp v5 v7 v10 shift antiShift
        a0 a1 a2 a3 u0Old u1Old u2Old u3Old u4Old)
      (normAFullPost sp a0 a1 a2 a3 shift antiShift) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_normA_full_spec_within_mod_v4_noNop sp a0 a1 a2 a3 v5 v7 v10 shift antiShift
      u0Old u1Old u2Old u3Old u4Old base)

/-- LoopSetup not-taken over the no-NOP v4 MOD code bundle. -/
theorem divK_loopSetup_ntaken_spec_within_mod_v4_noNop (sp n v1 v5 : Word) (base : Word)
    (hm_ge : ¬BitVec.slt (signExtend12 (4 : BitVec 12) - n) (0 : Word)) :
    let m := signExtend12 (4 : BitVec 12) - n
    cpsTripleWithin 4 (base + loopSetupOff) (base + loopBodyOff) (modCode_noNop_v4 base)
      (divKLoopSetupNtakenPreNoNop sp v5 v1 n)
      (divKLoopSetupNtakenPostNoNop sp n m) := by
  intro m
  rw [divKLoopSetupNtakenPreNoNop_unfold, divKLoopSetupNtakenPostNoNop_unfold]
  have hbody := divK_loopSetup_body_spec_within sp n v1 v5 464 (base + loopSetupOff)
  have hbodye := cpsTripleWithin_extend_code (hmono := by
    unfold divK_loopSetup_code
    intro a i h
    exact sharedNoNop_v4_b7_mod a i h) hbody
  have hblt_raw := blt_spec_gen_within .x9 .x0 464 m (0 : Word) (base + loopSetupOff + 12)
  rw [show (base + loopSetupOff + 12 : Word) + signExtend13 464 = base + denormOff from by rv64_addr,
      show (base + loopSetupOff + 12 : Word) + 4 = base + loopBodyOff from by bv_addr] at hblt_raw
  have hblt_clean := cpsBranchWithin_ntakenStripPure2 hblt_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hm_ge)
  have hblte := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact sharedNoNop_v4_b7_mod a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + loopSetupOff) (divK_loopSetup 464) 3
          (by decide) (by decide)
        rw [bv64_4mul_3] at hlookup
        exact hlookup) a i h)) hblt_clean
  have hbltef := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hblte
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbodye hbltef
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

/-- LoopSetup not-taken over the full v4 MOD code bundle. -/
theorem divK_loopSetup_ntaken_spec_within_mod_v4 (sp n v1 v5 : Word) (base : Word)
    (hm_ge : ¬BitVec.slt (signExtend12 (4 : BitVec 12) - n) (0 : Word)) :
    let m := signExtend12 (4 : BitVec 12) - n
    cpsTripleWithin 4 (base + loopSetupOff) (base + loopBodyOff) (modCode_v4 base)
      (divKLoopSetupNtakenPreNoNop sp v5 v1 n)
      (divKLoopSetupNtakenPostNoNop sp n m) := by
  intro m
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_loopSetup_ntaken_spec_within_mod_v4_noNop sp n v1 v5 base hm_ge)

/-- MOD n=4 path from entry to loop body start over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_n4_to_loopSetup_spec_within_v4_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4) base (base + loopBodyOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
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
      (loopSetupPost sp (4 : Word) (clzResult b3).1 a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b3).1
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
  have hNormB := evm_mod_n4_to_normB_spec_within_v4_noNop sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem shiftMem hbnz hb3nz hshift_nz
  have hNormBf := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4024) ↦ₘ u4Old))
    (by pcFree) hNormB
  have hNormA := divK_normA_full_spec_within_mod_v4_noNop sp a0 a1 a2 a3
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
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNormA
  have hNA := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by delta normBPost at hp; xperm_hyp hp) hNormBf hNormAf
  have hLS := divK_loopSetup_ntaken_spec_within_mod_v4_noNop sp (4 : Word)
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

/-- MOD n=4 path from entry to loop body start over the full v4 MOD code bundle. -/
theorem evm_mod_n4_to_loopSetup_spec_within_v4 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4) base (base + loopBodyOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
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
      (loopSetupPost sp (4 : Word) (clzResult b3).1 a0 a1 a2 a3 b0 b1 b2 b3) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (evm_mod_n4_to_loopSetup_spec_within_v4_noNop sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      hbnz hb3nz hshift_nz)

/-- MOD denorm body over the no-NOP v4 MOD code bundle. -/
theorem mod_denorm_body_spec_within_noNop_v4
    (sp u0 u1 u2 u3 v2 v5 v7 shift : Word) (base : Word) :
    cpsTripleWithin 23 (base + denormOff + 8) (base + epilogueOff) (modCode_noNop_v4 base)
      (divKDenormBodyPre sp u0 u1 u2 u3 v2 v5 v7 shift)
      (divKDenormBodyPost sp u0 u1 u2 u3 shift) := by
  rw [divKDenormBodyPre_unfold, divKDenormBodyPost_unfold]
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
  let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
  let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
  let u3' := u3 >>> (shift.toNat % 64)
  have haddi := addi_x0_spec_gen_within .x2 v2 0 (base + denormOff + 8) (by nofun)
  rw [show (base + denormOff + 8 : Word) + 4 = base + denormOff + 12 from by bv_addr] at haddi
  have haddie := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b9_mod a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 8) divK_denorm
        [.ADDI .x2 .x0 0] 2
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) haddi
  have haddief := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ shift) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) haddie
  have hsub := sub_spec_gen_rd_eq_rs1_within .x2 .x6
    (signExtend12 (0 : BitVec 12)) shift (base + denormOff + 12) (by nofun)
  rw [show (base + denormOff + 12 : Word) + 4 = base + denormOff + 16 from by bv_addr] at hsub
  have hsube := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b9_mod a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + denormOff) divK_denorm 3
          (by decide) (by decide)
        rw [bv64_4mul_3] at hlookup
        exact hlookup) a i h)) hsub
  have hsubf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hsube
  have h_anti := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) haddief hsubf
  have hm0 := divK_denorm_merge_spec_within 4056 4048 sp u0 u1 v5 v7 shift antiShift (base + denormOff + 16)
  rw [show (base + denormOff + 16 : Word) + 24 = base + denormOff + 40 from by bv_addr] at hm0
  have hm0e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b9_mod a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 16) divK_denorm
        (divK_denorm_merge_prog 4056 4048) 4
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm0
  have hm0ef := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hm0e
  have h_m0 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h_anti hm0ef
  have hm1 := divK_denorm_merge_spec_within 4048 4040 sp u1 u2
    u0' (u1 <<< (antiShift.toNat % 64)) shift antiShift (base + denormOff + 40)
  rw [show (base + denormOff + 40 : Word) + 24 = base + denormOff + 64 from by bv_addr] at hm1
  have hm1e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b9_mod a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 40) divK_denorm
        (divK_denorm_merge_prog 4048 4040) 10
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm1
  have hm1ef := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hm1e
  have h_m1 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h_m0 hm1ef
  have hm2 := divK_denorm_merge_spec_within 4040 4032 sp u2 u3
    u1' (u2 <<< (antiShift.toNat % 64)) shift antiShift (base + denormOff + 64)
  rw [show (base + denormOff + 64 : Word) + 24 = base + denormOff + 88 from by bv_addr] at hm2
  have hm2e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b9_mod a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 64) divK_denorm
        (divK_denorm_merge_prog 4040 4032) 16
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm2
  have hm2ef := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1'))
    (by pcFree) hm2e
  have h_m2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h_m1 hm2ef
  have hl := divK_denorm_last_spec_within 4032 sp u3 u2' shift (base + denormOff + 88)
  rw [show (base + denormOff + 88 : Word) + 12 = base + epilogueOff from by bv_addr] at hl
  have hle := cpsTripleWithin_extend_code (hmono := fun a i h =>
    sharedNoNop_v4_b9_mod a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 88) divK_denorm
        (divK_denorm_last_prog 4032) 22
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hl
  have hlef := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (u3 <<< (antiShift.toNat % 64))) ** (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
     ((sp + signExtend12 4040) ↦ₘ u2'))
    (by pcFree) hle
  have h_all := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h_m2 hlef
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h_all

/-- MOD denorm body over the full v4 MOD code bundle. -/
theorem mod_denorm_body_spec_within_v4
    (sp u0 u1 u2 u3 v2 v5 v7 shift : Word) (base : Word) :
    cpsTripleWithin 23 (base + denormOff + 8) (base + epilogueOff) (modCode_v4 base)
      (divKDenormBodyPre sp u0 u1 u2 u3 v2 v5 v7 shift)
      (divKDenormBodyPost sp u0 u1 u2 u3 shift) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (mod_denorm_body_spec_within_noNop_v4 sp u0 u1 u2 u3 v2 v5 v7 shift base)

/-- MOD epilogue over the no-NOP v4 MOD code bundle. -/
theorem divK_mod_epilogue_spec_within_noNop_v4 (sp : Word) (base : Word)
    (u0 u1 u2 u3 v5 v6 v7 v10 m0 m8 m16 m24 : Word) :
    cpsTripleWithin 10 (base + epilogueOff) (base + nopOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ u0) ** (.x6 ↦ᵣ u1) ** (.x7 ↦ᵣ u2) ** (.x10 ↦ᵣ u3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ u0) ** ((sp + 40) ↦ₘ u1) **
       ((sp + 48) ↦ₘ u2) ** ((sp + 56) ↦ₘ u3)) := by
  have hload := divK_epilogue_load_spec_within 4056 4048 4040 4032 sp u0 u1 u2 u3 v5 v6 v7 v10
    (base + epilogueOff)
  have hloade := cpsTripleWithin_extend_code (hmono := fun a i h =>
    modNoNop_v4_b10_modEpilogue a i
      (CodeReq.ofProg_mono_sub (base + epilogueOff) (base + epilogueOff) (divK_mod_epilogue 24)
        (divK_epilogue_load_prog 4056 4048 4040 4032) 0
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hload
  have hstore := divK_epilogue_store_spec_within sp (base + epilogueOff + 16) u0 u1 u2 u3 m0 m8 m16 m24 24
  rw [show (base + epilogueOff + 16 : Word) + 20 + signExtend21 24 = base + nopOff from by rv64_addr]
    at hstore
  have hstoree := cpsTripleWithin_extend_code (hmono := fun a i h =>
    modNoNop_v4_b10_modEpilogue a i
      (CodeReq.ofProg_mono_sub (base + epilogueOff) (base + epilogueOff + 16) (divK_mod_epilogue 24)
        (divK_epilogue_store_prog 24) 4
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hstore
  have hloadef := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) ** ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hloade
  have hstoref := cpsTripleWithin_frameR
    (((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hstoree
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hloadef hstoref
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

/-- MOD epilogue over the full v4 MOD code bundle. -/
theorem divK_mod_epilogue_spec_within_v4 (sp : Word) (base : Word)
    (u0 u1 u2 u3 v5 v6 v7 v10 m0 m8 m16 m24 : Word) :
    cpsTripleWithin 10 (base + epilogueOff) (base + nopOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ u0) ** (.x6 ↦ᵣ u1) ** (.x7 ↦ᵣ u2) ** (.x10 ↦ᵣ u3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ u0) ** ((sp + 40) ↦ₘ u1) **
       ((sp + 48) ↦ₘ u2) ** ((sp + 56) ↦ₘ u3)) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_mod_epilogue_spec_within_noNop_v4 sp base
      u0 u1 u2 u3 v5 v6 v7 v10 m0 m8 m16 m24)

/-- MOD post-loop denorm+epilogue over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_denorm_epilogue_spec_within_noNop_v4 (sp base : Word)
    (u0 u1 u2 u3 v2 v5 v7 v10 shift : Word)
    (m0 m8 m16 m24 : Word) :
    cpsTripleWithin 33 (base + denormOff + 8) (base + nopOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (denormModPost sp shift u0 u1 u2 u3) := by
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
  let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
  let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
  let u3' := u3 >>> (shift.toNat % 64)
  have hDenorm := mod_denorm_body_spec_within_noNop_v4 sp u0 u1 u2 u3 v2 v5 v7 shift base
  simp only [divKDenormBodyPre_unfold, divKDenormBodyPost_unfold] at hDenorm
  have hDenormF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ v10) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
     ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hDenorm
  have hEpi := divK_mod_epilogue_spec_within_noNop_v4 sp base u0' u1' u2' u3'
    u3' shift (u3 <<< (antiShift.toNat % 64)) v10 m0 m8 m16 m24
  have hEpiF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hEpi
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hDenormF hEpiF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta denormModPost; xperm_hyp hq)
    hFull

/-- MOD post-loop denorm+epilogue over the full v4 MOD code bundle. -/
theorem evm_mod_denorm_epilogue_spec_within_v4 (sp base : Word)
    (u0 u1 u2 u3 v2 v5 v7 v10 shift : Word)
    (m0 m8 m16 m24 : Word) :
    cpsTripleWithin 33 (base + denormOff + 8) (base + nopOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (denormModPost sp shift u0 u1 u2 u3) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (evm_mod_denorm_epilogue_spec_within_noNop_v4 sp base
      u0 u1 u2 u3 v2 v5 v7 v10 shift m0 m8 m16 m24)

/-- MOD denorm preamble over the no-NOP v4 MOD code bundle. -/
theorem mod_denorm_preamble_spec_within_noNop_v4 (sp shift v5 v6 v7 v2 v10 : Word)
    (base : Word) (hshift_nz : shift ≠ 0) :
    cpsTripleWithin 2 (base + denormOff) (base + denormOff + 8) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hld := ld_spec_gen_within .x6 .x12 sp v6 shift (3992 : BitVec 12) (base + denormOff) (by nofun)
  have hlde := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact sharedNoNop_v4_b9_mod a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff) divK_denorm
        [.LD .x6 .x12 3992] 0 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hld
  have hbeq := beq_spec_gen_within .x6 .x0 (96 : BitVec 13) shift (0 : Word) (base + denormOff + 4)
  rw [show (base + denormOff + 4 : Word) + signExtend13 (96 : BitVec 13) = base + epilogueOff from by rv64_addr,
      show (base + denormOff + 4 : Word) + 4 = base + denormOff + 8 from by bv_addr] at hbeq
  have hbeqe := cpsBranchWithin_extend_code (hmono := by
    intro a i h
    exact sharedNoNop_v4_b9_mod a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff + 4) divK_denorm
        [.BEQ .x6 .x0 96] 1 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hbeq
  have hbeq_exit := cpsBranchWithin_ntakenPath hbeqe
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
      exact hshift_nz hpure)
  have hbeq_clean := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    hbeq_exit
  have hldf := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10))
    (by pcFree) hlde
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq_clean
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hldf hbeqf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

/-- MOD denorm preamble over the full v4 MOD code bundle. -/
theorem mod_denorm_preamble_spec_within_v4 (sp shift v5 v6 v7 v2 v10 : Word)
    (base : Word) (hshift_nz : shift ≠ 0) :
    cpsTripleWithin 2 (base + denormOff) (base + denormOff + 8) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (mod_denorm_preamble_spec_within_noNop_v4 sp shift v5 v6 v7 v2 v10 base hshift_nz)

/-- MOD post-loop preamble+denorm+epilogue over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_preamble_denorm_epilogue_spec_within_noNop_v4 (sp base : Word)
    (u0 u1 u2 u3 shift v2 v5 v6 v7 v10 : Word)
    (m0 m8 m16 m24 : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTripleWithin 35 (base + denormOff) (base + nopOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (denormModPost sp shift u0 u1 u2 u3 **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hPre := mod_denorm_preamble_spec_within_noNop_v4 sp shift v5 v6 v7 v2 v10 base hshift_nz
  have hPreF := cpsTripleWithin_frameR
    (((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
     ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hPre
  have hDE := evm_mod_denorm_epilogue_spec_within_noNop_v4 sp base u0 u1 u2 u3 v2 v5 v7 v10 shift
    m0 m8 m16 m24
  have hDEF := cpsTripleWithin_frameR
    (((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hDE
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPreF hDEF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

/-- MOD post-loop preamble+denorm+epilogue over the full v4 MOD code bundle. -/
theorem evm_mod_preamble_denorm_epilogue_spec_within_v4 (sp base : Word)
    (u0 u1 u2 u3 shift v2 v5 v6 v7 v10 : Word)
    (m0 m8 m16 m24 : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTripleWithin 35 (base + denormOff) (base + nopOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (denormModPost sp shift u0 u1 u2 u3 **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (evm_mod_preamble_denorm_epilogue_spec_within_noNop_v4 sp base
      u0 u1 u2 u3 shift v2 v5 v6 v7 v10 m0 m8 m16 m24 hshift_nz)

/-- Loop body n=4, max+skip, j=0 over `modCode_noNop_v4`, with
    sp-relative addresses in the precondition. -/
theorem divK_loop_body_n4_max_skip_j0_norm_mod_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult uTop v3) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld))
      (loopBodyN4SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n4_max_skip_j0_v4_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4) raw
  rw [loopBodyN4MaxSkipJ0Pre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  rw [loopBodyN4MaxSkipJ0Post_unfold] at raw'
  exact raw'

/-- Loop body n=4, max+skip, j=0 over the full `modCode_v4` bundle. -/
theorem divK_loop_body_n4_max_skip_j0_norm_mod_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult uTop v3) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld))
      (loopBodyN4SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_loop_body_n4_max_skip_j0_norm_mod_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow)

/-- Loop body n=4, call+skip, j=0 over `modCode_noNop_v4`, with
    sp-relative addresses in the precondition. -/
theorem divK_loop_body_n4_call_skip_j0_norm_mod_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : loopBodyN4CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       regOwn .x1) ** (sp + signExtend12 3936 ↦ₘ scratchMem))
      (loopBodyN4CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
      (divK_loop_body_n4_call_skip_j0_v4_spec_within_noNop
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow)
  rw [loopBodyN4CallSkipJ0PreV4_unfold] at raw
  rw [loopBodyN4CallSkipJ0Pre_unfold] at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact raw

/-- Loop body n=4, call+skip, j=0 over the full `modCode_v4` bundle. -/
theorem divK_loop_body_n4_call_skip_j0_norm_mod_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : loopBodyN4CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (modCode_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       regOwn .x1) ** (sp + signExtend12 3936 ↦ₘ scratchMem))
      (loopBodyN4CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_loop_body_n4_call_skip_j0_norm_mod_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu hborrow)

/-- Loop body n=4, call+addback (BEQ double-addback), j=0 over
    `modCode_noNop_v4`, with sp-relative addresses in the precondition. -/
theorem divK_loop_body_n4_call_addback_j0_beq_norm_mod_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : loopBodyN4CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN4CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       regOwn .x1) **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (loopBodyN4CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
      (divK_loop_body_n4_call_addback_j0_beq_v4_spec_within_noNop
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow hcarry2_nz)
  rw [loopBodyN4CallSkipJ0PreV4_unfold] at raw
  rw [loopBodyN4CallSkipJ0Pre_unfold] at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact raw

/-- Loop body n=4, call+addback (BEQ double-addback), j=0 over the full
    `modCode_v4` bundle. -/
theorem divK_loop_body_n4_call_addback_j0_beq_norm_mod_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : loopBodyN4CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN4CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (modCode_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       regOwn .x1) **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (loopBodyN4CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_loop_body_n4_call_addback_j0_beq_norm_mod_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu hborrow hcarry2_nz)

end EvmAsm.Evm64
