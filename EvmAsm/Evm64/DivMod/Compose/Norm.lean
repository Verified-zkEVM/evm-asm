/-
  EvmAsm.Evm64.DivMod.Compose.Norm

  PhaseC2 and NormB compositions for DivMod.
  Extracted from Compose.lean sections 10g–10h.
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

/-- Phase C2 code (block 3) is subsumed by divCode. -/
private theorem divK_phaseC2_code_sub_divCode (base : Word) :
    ∀ a i, (divK_phaseC2_code 172 (base + 212)) a = some i → (divCode base) a = some i := by
  unfold divCode divK_phaseC2_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- BEQ x6 x0 172 singleton at base+224 (index 3 of phaseC2) is subsumed by divCode. -/
private theorem beq_shift_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 224) (.BEQ .x6 .x0 172)) a = some i →
      (divCode base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 212) (divK_phaseC2 172) 3
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 3) = (12 : Word) from by native_decide,
      show (base + 212 : Word) + 12 = base + 224 from by bv_addr] at hlookup
  exact divK_phaseC2_code_sub_divCode base a i
    (CodeReq.singleton_mono hlookup a i h)

private theorem signExtend13_172 : signExtend13 (172 : BitVec 13) = (172 : Word) := by native_decide

/-- Phase C2 body (base+212 → base+224): store shift, compute anti_shift.
    Extends to divCode. Uses first 3 instructions of phaseC2. -/
private theorem divK_phaseC2_body_divCode (sp shift v2 shift_mem : Word) (base : Word)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true) :
    cpsTriple (base + 212) (base + 224) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_spec sp shift v2 shift_mem 172 (base + 212) hv_shift
  rw [show (base + 212 : Word) + 12 = base + 224 from by bv_addr] at hbody
  exact cpsTriple_extend_code (divK_phaseC2_code_sub_divCode base) hbody

set_option maxRecDepth 2048 in
/-- Phase C2 when shift ≠ 0: falls through to normB at base+228.
    Stores shift to scratch, computes anti_shift = -shift. -/
theorem divK_phaseC2_ntaken_spec (sp shift v2 shift_mem : Word) (base : Word)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hshift_nz : shift ≠ 0) :
    cpsTriple (base + 212) (base + 228) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_divCode sp shift v2 shift_mem base hv_shift
  have hbeq_raw := beq_spec_gen .x6 .x0 172 shift (0 : Word) (base + 224)
  rw [show (base + 224 : Word) + signExtend13 172 = base + 396 from by
        rw [signExtend13_172]; bv_addr,
      show (base + 224 : Word) + 4 = base + 228 from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 (show shift ≠ (0 : Word) from hshift_nz))
  have hbeq := cpsTriple_extend_code (beq_shift_sub_divCode base) hbeq_clean
  have hbeqf := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hC2 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeqf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hC2

set_option maxRecDepth 2048 in
/-- Phase C2 when shift = 0: branches to copyAU at base+396.
    Stores shift (=0) to scratch, computes anti_shift = 0. -/
theorem divK_phaseC2_taken_spec (sp shift v2 shift_mem : Word) (base : Word)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hshift_z : shift = 0) :
    cpsTriple (base + 212) (base + 396) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_divCode sp shift v2 shift_mem base hv_shift
  have hbeq_raw := beq_spec_gen .x6 .x0 172 shift (0 : Word) (base + 224)
  rw [show (base + 224 : Word) + signExtend13 172 = base + 396 from by
        rw [signExtend13_172]; bv_addr,
      show (base + 224 : Word) + 4 = base + 228 from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hshift_z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbeq := cpsTriple_extend_code (beq_shift_sub_divCode base) hbeq_clean
  have hbeqf := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hC2 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeqf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hC2

-- ============================================================================
-- Section 10h: NormB composition (normalize divisor, 21 instructions)
-- base+228: 3 merge blocks (6 instrs each) + 1 last block (3 instrs)
-- ============================================================================

/-- NormB code (block 4) is subsumed by divCode. -/
private theorem divK_normB_code_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 228) divK_normB) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Helper: NormB sub-block subsumption via ofProg_mono_sub. -/
private theorem normB_sub (base : Word) (sub_prog : List Instr) (k : Nat)
    (hk : k + sub_prog.length ≤ divK_normB.length)
    (hslice : (divK_normB.drop k).take sub_prog.length = sub_prog)
    (hbound : 4 * divK_normB.length < 2 ^ 64) :
    ∀ a i, (CodeReq.ofProg ((base + 228) + BitVec.ofNat 64 (4 * k)) sub_prog) a = some i →
      (divCode base) a = some i := by
  intro a i h
  exact divK_normB_code_sub_divCode base a i
    (CodeReq.ofProg_mono_sub (base + 228) _ divK_normB _ k rfl hslice hk hbound a i h)

-- signExtend12 for offsets used by normB merge spec
private theorem se12_56 : signExtend12 (56 : BitVec 12) = (56 : Word) := by native_decide
private theorem se12_48 : signExtend12 (48 : BitVec 12) = (48 : Word) := by native_decide
private theorem se12_40 : signExtend12 (40 : BitVec 12) = (40 : Word) := by native_decide
private theorem se12_32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by native_decide

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 4096 in
/-- Full NormB: normalize divisor b[0..3] in place by left-shifting.
    base+228 → base+312 (21 instructions).
    Pre: x12=sp, x6=shift, x2=anti_shift, b[0..3] at sp+32..56.
    Post: b[i] normalized, x5=b[0]<<<shift, x7=b[0]>>>anti_shift. -/
theorem divK_normB_full_spec (sp b0 b1 b2 b3 v5 v7 shift anti_shift : Word) (base : Word)
    (hvalid : ValidMemRange sp 8) :
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    cpsTriple (base + 228) (base + 312) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x7 ↦ᵣ (b0 >>> (anti_shift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3')) := by
  intro b3' b2' b1' b0'
  -- Merge 1: b[3] with b[2] (base+228 → base+252)
  have hm1 := divK_normB_merge_spec 56 48 sp b3 b2 v5 v7 shift anti_shift (base + 228)
    (by rw [se12_56]; exact hvalid.get (show 7 < 8 from by omega))
    (by rw [se12_48]; exact hvalid.get (show 6 < 8 from by omega))
  simp only [se12_56, se12_48] at hm1
  rw [show (base + 228 : Word) + 24 = base + 252 from by bv_addr] at hm1
  have hm1e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 228) (base + 228) divK_normB
        (divK_normB_merge_prog 56 48) 0
        (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h)) hm1
  -- Frame merge1 with b[0], b[1] (not touched by merge1)
  have hm1ef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1))
    (by pcFree) hm1e
  -- Merge 2: b[2] with b[1] (base+252 → base+276)
  have hm2 := divK_normB_merge_spec 48 40 sp b2 b1 b3' (b2 >>> (anti_shift.toNat % 64))
    shift anti_shift (base + 252)
    (by rw [se12_48]; exact hvalid.get (show 6 < 8 from by omega))
    (by rw [se12_40]; exact hvalid.get (show 5 < 8 from by omega))
  simp only [se12_48, se12_40] at hm2
  rw [show (base + 252 : Word) + 24 = base + 276 from by bv_addr] at hm2
  have hm2e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 228) (base + 252) divK_normB
        (divK_normB_merge_prog 48 40) 6
        (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h)) hm2
  have hm2ef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 32) ↦ₘ b0) ** ((sp + 56) ↦ₘ b3'))
    (by pcFree) hm2e
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hm1ef hm2ef
  -- Merge 3: b[1] with b[0] (base+276 → base+300)
  have hm3 := divK_normB_merge_spec 40 32 sp b1 b0
    b2' (b1 >>> (anti_shift.toNat % 64)) shift anti_shift (base + 276)
    (by rw [se12_40]; exact hvalid.get (show 5 < 8 from by omega))
    (by rw [se12_32]; exact hvalid.get (show 4 < 8 from by omega))
  simp only [se12_40, se12_32] at hm3
  rw [show (base + 276 : Word) + 24 = base + 300 from by bv_addr] at hm3
  have hm3e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 228) (base + 276) divK_normB
        (divK_normB_merge_prog 40 32) 12
        (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h)) hm3
  have hm3ef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3'))
    (by pcFree) hm3e
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 hm3ef
  -- Last: b[0] alone (base+300 → base+312)
  have hl := divK_normB_last_spec 32 sp b0 b1' shift (base + 300)
    (by rw [se12_32]; exact hvalid.get (show 4 < 8 from by omega))
  simp only [se12_32] at hl
  rw [show (base + 300 : Word) + 12 = base + 312 from by bv_addr] at hl
  have hle := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 228) (base + 300) divK_normB
        (divK_normB_last_prog 32) 18
        (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h)) hl
  have hlef := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ (b0 >>> (anti_shift.toNat % 64))) ** (.x2 ↦ᵣ anti_shift) **
     ((sp + 40) ↦ₘ b1') ** ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3'))
    (by pcFree) hle
  have h1234 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hlef
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h1234

end EvmAsm.Rv64
