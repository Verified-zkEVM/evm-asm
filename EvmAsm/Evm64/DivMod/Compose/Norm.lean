/-
  EvmAsm.Evm64.DivMod.Compose.Norm

  PhaseC2 and NormB compositions for DivMod.
  Extracted from Compose.lean sections 10g–10h.
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (bv64_4mul_3 se12_32 se12_40 se12_48 se12_56)

/-- Phase C2 code (block 3) is subsumed by divCode. -/
private theorem divK_phaseC2_code_sub_divCode {base : Word} :
    ∀ a i, (divK_phaseC2_code 172 (base + phaseC2Off)) a = some i → (divCode base) a = some i := by
  unfold divCode divK_phaseC2_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left

/-- BEQ x6 x0 172 singleton at base+224 (index 3 of phaseC2) is subsumed by divCode. -/
private theorem beq_shift_sub_divCode {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseC2Off + 12) (.BEQ .x6 .x0 172)) a = some i →
      (divCode base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseC2Off) (divK_phaseC2 172) 3
    (by decide) (by decide)
  rw [bv64_4mul_3] at hlookup
  exact divK_phaseC2_code_sub_divCode a i
    (CodeReq.singleton_mono hlookup a i h)

-- `se13_172` moved to `Compose/Base.lean` (shared with ModNorm).

/-- Phase C2 body (base+212 → base+224): store shift, compute antiShift.
    Extends to divCode. Uses first 3 instructions of phaseC2. -/
private theorem divK_phaseC2_body_divCode_within (sp shift v2 shiftMem : Word) (base : Word) :
    cpsTripleWithin 3 (base + phaseC2Off) (base + phaseC2Off + 12) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_spec_within sp shift v2 shiftMem 172 (base + phaseC2Off)
  exact cpsTripleWithin_extend_code divK_phaseC2_code_sub_divCode hbody

theorem divK_phaseC2_ntaken_spec_within (sp shift v2 shiftMem : Word) (base : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTripleWithin 4 (base + phaseC2Off) (base + normBOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_divCode_within sp shift v2 shiftMem base
  have hbeq_raw := beq_spec_gen_within .x6 .x0 172 shift (0 : Word) (base + phaseC2Off + 12)
  rw [show (base + phaseC2Off + 12 : Word) + signExtend13 172 = base + copyAUOff from by rv64_addr,
      show (base + phaseC2Off + 12 : Word) + 4 = base + normBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranchWithin_ntakenStripPure2 hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _).mp h_rest).2 (show shift ≠ (0 : Word) from hshift_nz))
  have hbeq := cpsTripleWithin_extend_code beq_shift_sub_divCode hbeq_clean
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeqf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hC2

theorem divK_phaseC2_taken_spec_within (sp shift v2 shiftMem : Word) (base : Word)
    (hshift_z : shift = 0) :
    cpsTripleWithin 4 (base + phaseC2Off) (base + copyAUOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_divCode_within sp shift v2 shiftMem base
  have hbeq_raw := beq_spec_gen_within .x6 .x0 172 shift (0 : Word) (base + phaseC2Off + 12)
  rw [show (base + phaseC2Off + 12 : Word) + signExtend13 172 = base + copyAUOff from by rv64_addr,
      show (base + phaseC2Off + 12 : Word) + 4 = base + normBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranchWithin_takenStripPure2 hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hshift_z ((sepConj_pure_right _).mp h_rest).2)
  have hbeq := cpsTripleWithin_extend_code beq_shift_sub_divCode hbeq_clean
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeqf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hC2

theorem divK_phaseC2_taken_spec (sp shift v2 shiftMem : Word) (base : Word)
    (hshift_z : shift = 0) :
    cpsTripleWithin 4 (base + phaseC2Off) (base + copyAUOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) :=
  divK_phaseC2_taken_spec_within sp shift v2 shiftMem base hshift_z

-- ============================================================================
-- Section 10h: NormB composition (normalize divisor, 21 instructions)
-- base+228: 3 merge blocks (6 instrs each) + 1 last block (3 instrs)
-- ============================================================================

/-- NormB code (block 4) is subsumed by divCode. -/
private theorem divK_normB_code_sub_divCode {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + normBOff) divK_normB) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left

-- se12_32, se12_40, se12_48, se12_56 are in Base.lean

/-- NormB first half: merge1 (b[3] with b[2]) + merge2 (b[2] with b[1]).
    base+228 → base+276 (12 instructions). -/
private theorem divK_normB_half1_within (sp b0 b1 b2 b3 v5 v7 shift antiShift : Word) (base : Word) :
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    cpsTripleWithin 12 (base + normBOff) (base + normBOff + 48) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b2') ** (.x7 ↦ᵣ (b1 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3')) := by
  intro b3' b2'
  -- Merge 1: b[3] with b[2] (base+228 → base+252)
  have hm1 := divK_normB_merge_spec_within 56 48 sp b3 b2 v5 v7 shift antiShift (base + normBOff)
  simp only [se12_56, se12_48] at hm1
  have hm1e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_divCode a i
      (CodeReq.ofProg_mono_sub (base + normBOff) (base + normBOff) divK_normB
        (divK_normB_merge_prog 56 48) 0
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm1
  -- Frame merge1 with b[0], b[1] (not touched by merge1)
  have hm1ef := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1))
    (by pcFree) hm1e
  -- Merge 2: b[2] with b[1] (base+252 → base+276)
  have hm2 := divK_normB_merge_spec_within 48 40 sp b2 b1 b3' (b2 >>> (antiShift.toNat % 64))
    shift antiShift (base + normBOff + 24)
  simp only [se12_48, se12_40] at hm2
  rw [show (base + normBOff + 24 : Word) + 24 = base + normBOff + 48 from by bv_addr] at hm2
  have hm2e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_divCode a i
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

private theorem divK_normB_half2_within (sp b0 b1 b2' b3' shift antiShift : Word) (base : Word) :
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    cpsTripleWithin 9 (base + normBOff + 48) (base + normAOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b2') ** (.x7 ↦ᵣ (b1 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3'))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3')) := by
  intro b1' b0'
  -- Merge 3: b[1] with b[0] (base+276 → base+300)
  have hm3 := divK_normB_merge_spec_within 40 32 sp b1 b0
    b2' (b1 >>> (antiShift.toNat % 64)) shift antiShift (base + normBOff + 48)
  simp only [se12_40, se12_32] at hm3
  rw [show (base + normBOff + 48 : Word) + 24 = base + normBOff + 72 from by bv_addr] at hm3
  have hm3e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_divCode a i
      (CodeReq.ofProg_mono_sub (base + normBOff) (base + normBOff + 48) divK_normB
        (divK_normB_merge_prog 40 32) 12
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm3
  have hm3ef := cpsTripleWithin_frameR
    (((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3'))
    (by pcFree) hm3e
  -- Last: b[0] alone (base+300 → base+312)
  have hl := divK_normB_last_spec_within 32 sp b0 b1' shift (base + normBOff + 72)
  simp only [se12_32] at hl
  rw [show (base + normBOff + 72 : Word) + 12 = base + normAOff from by bv_addr] at hl
  have hle := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_divCode a i
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

theorem divK_normB_full_spec_within (sp b0 b1 b2 b3 v5 v7 shift antiShift : Word) (base : Word) :
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    cpsTripleWithin 21 (base + normBOff) (base + normAOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3')) := by
  intro b3' b2' b1' b0'
  have h1 := divK_normB_half1_within sp b0 b1 b2 b3 v5 v7 shift antiShift base
  have h2 := divK_normB_half2_within sp b0 b1 b2' b3' shift antiShift base
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) h1 h2)
