/-
  EvmAsm.Evm64.DivMod.Compose.NormBV5Mod

  v5 normalize-B brick (21 steps, normBOff → normAOff) over `modCode_noNop_v5`.
  Mirror of `divK_normB_full_spec_within_v4_noNop` (Norm.lean): the normB
  instructions don't touch div128, so the same version-agnostic merge/last bodies
  are extended to the v5 code via the v5 block subsumption `sharedNoNop_v5_b4_mod`.
  Third brick of the v5 n=1 preloop.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.Compose.Norm
import EvmAsm.Evm64.DivMod.Compose.V5NoNop
import EvmAsm.Evm64.DivMod.AddrNorm

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- The normB block instructions are subsumed by `modCode_noNop_v5`. -/
private theorem divK_normB_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + normBOff) divK_normB) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b4_mod a i h

private theorem divK_normB_half1_within_v5_noNop
    (sp b0 b1 b2 b3 v5 v7 shift antiShift : Word) (base : Word) :
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    cpsTripleWithin 12 (base + normBOff) (base + normBOff + 48) (modCode_noNop_v5 base)
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
    divK_normB_code_sub_modCode_noNop_v5 a i
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
    divK_normB_code_sub_modCode_noNop_v5 a i
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

private theorem divK_normB_half2_within_v5_noNop
    (sp b0 b1 b2' b3' shift antiShift : Word) (base : Word) :
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    cpsTripleWithin 9 (base + normBOff + 48) (base + normAOff) (modCode_noNop_v5 base)
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
    divK_normB_code_sub_modCode_noNop_v5 a i
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
    divK_normB_code_sub_modCode_noNop_v5 a i
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

/-- v5 normalize-B full brick, over `modCode_noNop_v5`.  Mirror of the v4 analog. -/
theorem divK_normB_full_spec_within_v5_noNop_mod
    (sp b0 b1 b2 b3 v5 v7 shift antiShift : Word) (base : Word) :
    cpsTripleWithin 21 (base + normBOff) (base + normAOff) (modCode_noNop_v5 base)
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
  have h1 := divK_normB_half1_within_v5_noNop sp b0 b1 b2 b3 v5 v7 shift antiShift base
  have h2 := divK_normB_half2_within_v5_noNop sp b0 b1 b2' b3' shift antiShift base
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) h1 h2)

end EvmAsm.Evm64
