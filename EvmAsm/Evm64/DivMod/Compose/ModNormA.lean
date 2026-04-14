/-
  EvmAsm.Evm64.DivMod.Compose.ModNormA

  MOD mirrors of NormA, CopyAU, and LoopSetup compositions.
  Proof structure mirrors NormA.lean with modCode instead of divCode.
  Blocks 5 (NormA at base+312), 6 (CopyAU at base+396), and
  7 (LoopSetup at base+432) are identical between divCode and modCode.
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- MOD CodeReq subsumption lemmas for blocks 5, 6, 7
-- ============================================================================

/-- NormA code (block 5) is subsumed by modCode. -/
private theorem divK_normA_code_sub_modCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 312) (divK_normA 40)) a = some i → (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Helper: NormA sub-block subsumption via ofProg_mono_sub for modCode. -/
private theorem normA_sub_mod (base : Word) (sub_prog : List Instr) (k : Nat)
    (hk : k + sub_prog.length ≤ (divK_normA 40).length)
    (hslice : ((divK_normA 40).drop k).take sub_prog.length = sub_prog)
    (hbound : 4 * (divK_normA 40).length < 2 ^ 64) :
    ∀ a i, (CodeReq.ofProg ((base + 312) + BitVec.ofNat 64 (4 * k)) sub_prog) a = some i →
      (modCode base) a = some i := by
  intro a i h
  exact divK_normA_code_sub_modCode base a i
    (CodeReq.ofProg_mono_sub (base + 312) _ (divK_normA 40) _ k rfl hslice hk hbound a i h)

-- signExtend12 for src/dst offsets used by normA specs
private theorem mod_se12_24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
private theorem mod_se12_16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
private theorem mod_se12_8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem mod_se12_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem mod_signExtend21_40 : signExtend21 (40 : BitVec 21) = (40 : Word) := by decide

set_option maxHeartbeats 25600000 in
set_option maxRecDepth 4096 in
/-- Full NormA for modCode: normalize dividend a[0..3] -> u[0..4] and jump to loopSetup.
    base+312 -> base+432 (21 instructions including JAL).
    MOD mirror of divK_normA_full_spec. -/
theorem mod_normA_full_spec (sp a0 a1 a2 a3 v5 v7 v10 shift anti_shift : Word)
    (u0_old u1_old u2_old u3_old u4_old : Word) (base : Word)
    (hvalid : ValidMemRange sp 8)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true) :
    let u4 := a3 >>> (anti_shift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    cpsTriple (base + 312) (base + 432) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ u4_old) ** ((sp + signExtend12 4032) ↦ₘ u3_old) **
       ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
       ((sp + signExtend12 4056) ↦ₘ u0_old))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u1) ** (.x7 ↦ᵣ u0) ** (.x10 ↦ᵣ (a0 >>> (anti_shift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4056) ↦ₘ u0)) := by
  intro u4 u3 u2 u1 u0
  -- Top: LD a[3], SRL->u[4], SD u[4] (base+312 -> base+324)
  have htop := divK_normA_top_spec 24 4024 sp a3 v5 v7 anti_shift u4_old (base + 312)
    (by rw [mod_se12_24]; exact hvalid.get (show 3 < 8 from by omega)) hv_u4
  simp only [mod_se12_24] at htop
  rw [show (base + 312 : Word) + 12 = base + 324 from by bv_addr] at htop
  have htope := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCode base a i
      (CodeReq.ofProg_mono_sub (base + 312) (base + 312) (divK_normA 40)
        (divK_normA_top_prog 24 4024) 0
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) htop
  -- Frame top with x6, x10, a[0..2], u[0..3]
  have htopef := cpsTriple_frame_left _ _ _ _ _
    ((.x10 ↦ᵣ v10) ** (.x6 ↦ᵣ shift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) **
     ((sp + signExtend12 4032) ↦ₘ u3_old) **
     ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
     ((sp + signExtend12 4056) ↦ₘ u0_old))
    (by pcFree) htope
  -- MergeA 1: u[3] = (a[3]<<<shift) | (a[2]>>>anti) (base+324 -> base+344)
  have hma1 := divK_normA_mergeA_spec 16 4032 sp a3 a2 u4 v10 shift anti_shift u3_old (base + 324)
    (by rw [mod_se12_16]; exact hvalid.get (show 2 < 8 from by omega)) hv_u3
  simp only [mod_se12_16] at hma1
  rw [show (base + 324 : Word) + 20 = base + 344 from by bv_addr] at hma1
  have hma1e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCode base a i
      (CodeReq.ofProg_mono_sub (base + 312) (base + 324) (divK_normA 40)
        (divK_normA_mergeA_prog 16 4032) 3
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hma1
  have hma1ef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) **
     ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
     ((sp + signExtend12 4056) ↦ₘ u0_old))
    (by pcFree) hma1e
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) htopef hma1ef
  -- MergeB: u[2] = (a[2]<<<shift) | (a[1]>>>anti) (base+344 -> base+364)
  have hmb := divK_normA_mergeB_spec 8 4040 sp a2 a1 u3 (a2 >>> (anti_shift.toNat % 64))
    shift anti_shift u2_old (base + 344)
    (by rw [mod_se12_8]; exact hvalid.get (show 1 < 8 from by omega)) hv_u2
  simp only [mod_se12_8] at hmb
  rw [show (base + 344 : Word) + 20 = base + 364 from by bv_addr] at hmb
  have hmbe := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCode base a i
      (CodeReq.ofProg_mono_sub (base + 312) (base + 344) (divK_normA 40)
        (divK_normA_mergeB_prog 8 4040) 8
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hmb
  have hmbef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4048) ↦ₘ u1_old) ** ((sp + signExtend12 4056) ↦ₘ u0_old))
    (by pcFree) hmbe
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 hmbef
  -- MergeA 2: u[1] = (a[1]<<<shift) | (a[0]>>>anti) (base+364 -> base+384)
  have hma2 := divK_normA_mergeA_spec 0 4048 sp a1 a0 u2 (a1 >>> (anti_shift.toNat % 64))
    shift anti_shift u1_old (base + 364)
    (by rw [mod_se12_0]; exact hvalid.get (show 0 < 8 from by omega)) hv_u1
  simp only [mod_se12_0] at hma2
  rw [show (base + 364 : Word) + 20 = base + 384 from by bv_addr] at hma2
  have hma2e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCode base a i
      (CodeReq.ofProg_mono_sub (base + 312) (base + 364) (divK_normA 40)
        (divK_normA_mergeA_prog 0 4048) 13
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hma2
  have hma2ef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4056) ↦ₘ u0_old))
    (by pcFree) hma2e
  have h1234 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hma2ef
  -- Last: u[0] = a[0]<<<shift (base+384 -> base+392)
  have hlast := divK_normA_last_spec 4056 sp a0 shift u0_old (base + 384) hv_u0
  rw [show (base + 384 : Word) + 8 = base + 392 from by bv_addr] at hlast
  have hlaste := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCode base a i
      (CodeReq.ofProg_mono_sub (base + 312) (base + 384) (divK_normA 40)
        (divK_normA_last_prog 4056) 18
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hlast
  have hlastef := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ u1) ** (.x10 ↦ᵣ (a0 >>> (anti_shift.toNat % 64))) ** (.x2 ↦ᵣ anti_shift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1))
    (by pcFree) hlaste
  have h12345 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234 hlastef
  -- JAL x0 40 at base+392 -> base+432 (1 instruction, empAssertion pre/post)
  have hjal := jal_x0_spec_gen 40 (base + 392)
  rw [show (base + 392 : Word) + signExtend21 40 = base + 432 from by
        rw [mod_signExtend21_40]; bv_addr] at hjal
  have hjale := cpsTriple_extend_code (hmono := by
    intro a i h
    exact divK_normA_code_sub_modCode base a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + 312) (divK_normA 40) 20
          (by decide) (by decide)
        rw [show (base + 312 : Word) + BitVec.ofNat 64 (4 * 20) = base + 392 from by bv_addr]
          at hlookup
        exact hlookup) a i h)) hjal
  -- Frame JAL with everything, then strip empAssertion via consequence
  let postAll := (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u1) ** (.x7 ↦ᵣ u0) **
    (.x10 ↦ᵣ (a0 >>> (anti_shift.toNat % 64))) **
    (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
    ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
    ((sp + signExtend12 4056) ↦ₘ u0)
  have hjalef := cpsTriple_frame_left _ _ _ _ _ postAll (by pcFree) hjale
  have hjal_clean : cpsTriple (base + 392) (base + 432) (modCode base) postAll postAll :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by show (empAssertion ** postAll) h; rw [sepConj_emp_left']; exact hp)
      (fun h hp => by rw [sepConj_emp_left'] at hp; exact hp)
      hjalef
  have h123456 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12345 hjal_clean
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h123456

-- ============================================================================
-- MOD CopyAU composition (copy a[] to u[], 9 instructions)
-- base+396: used when shift=0 (no normalization needed)
-- ============================================================================

/-- CopyAU code (block 6) is subsumed by modCode. -/
private theorem divK_copyAU_code_sub_modCode (base : Word) :
    ∀ a i, (divK_copyAU_code (base + 396)) a = some i → (modCode base) a = some i := by
  unfold modCode divK_copyAU_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Full CopyAU for modCode: copy a[0..3] to u[0..3], set u[4]=0.
    base+396 -> base+432 (9 instructions).
    MOD mirror of divK_copyAU_full_spec. -/
theorem mod_copyAU_full_spec (sp : Word)
    (a0 a1 a2 a3 : Word) (u0 u1 u2 u3 u4 v5 : Word) (base : Word)
    (hvalid : ValidMemRange sp 8)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true) :
    cpsTriple (base + 396) (base + 432) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
       ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ (0 : Word))) := by
  have hcopy := divK_copyAU_spec sp (base + 396) a0 a1 a2 a3 u0 u1 u2 u3 u4 v5
    hvalid hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
  rw [show (base + 396 : Word) + 36 = base + 432 from by bv_addr] at hcopy
  exact cpsTriple_extend_code (divK_copyAU_code_sub_modCode base) hcopy

-- ============================================================================
-- MOD LoopSetup composition (4 instructions, cpsBranch at base+432)
-- LD n, ADDI 4, SUB m=4-n, BLT m<0
-- ============================================================================

/-- LoopSetup code (block 7) is subsumed by modCode. -/
private theorem divK_loopSetup_code_sub_modCode (base : Word) :
    ∀ a i, (divK_loopSetup_code 460 (base + 432)) a = some i → (modCode base) a = some i := by
  unfold modCode divK_loopSetup_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- BLT singleton at base+444 (index 3 of loopSetup) is subsumed by modCode. -/
private theorem blt_loopSetup_sub_modCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 444) (.BLT .x1 .x0 460)) a = some i →
      (modCode base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 432) (divK_loopSetup 460) 3
    (by decide) (by decide)
  rw [show BitVec.ofNat 64 (4 * 3) = (12 : Word) from by decide,
      show (base + 432 : Word) + 12 = base + 444 from by bv_addr] at hlookup
  exact divK_loopSetup_code_sub_modCode base a i
    (CodeReq.singleton_mono hlookup a i h)

private theorem mod_signExtend13_460 : signExtend13 (460 : BitVec 13) = (460 : Word) := by decide

set_option maxRecDepth 2048 in
/-- LoopSetup when m >= 0 (n <= 4): falls through to loop body at base+448.
    MOD mirror of divK_loopSetup_ntaken_spec. -/
theorem mod_loopSetup_ntaken_spec (sp n v1 v5 : Word) (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hm_ge : ¬BitVec.slt (signExtend12 (4 : BitVec 12) - n) (0 : Word)) :
    let m := signExtend12 (4 : BitVec 12) - n
    cpsTriple (base + 432) (base + 448) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** (.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n)) := by
  intro m
  have hbody := divK_loopSetup_body_spec sp n v1 v5 460 (base + 432) hv_n
  rw [show (base + 432 : Word) + 12 = base + 444 from by bv_addr] at hbody
  have hbodye := cpsTriple_extend_code (divK_loopSetup_code_sub_modCode base) hbody
  have hblt_raw := blt_spec_gen .x1 .x0 460 m (0 : Word) (base + 444)
  rw [show (base + 444 : Word) + signExtend13 460 = base + 904 from by
        rw [mod_signExtend13_460]; bv_addr,
      show (base + 444 : Word) + 4 = base + 448 from by bv_addr] at hblt_raw
  have hblt_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hblt_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hm_ge)
  have hblte := cpsTriple_extend_code (blt_loopSetup_sub_modCode base) hblt_clean
  have hbltef := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hblte
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbodye hbltef
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

set_option maxRecDepth 2048 in
/-- LoopSetup when m < 0 (n > 4, skip loop): branches to denorm at base+904.
    MOD mirror of divK_loopSetup_taken_spec. -/
theorem mod_loopSetup_taken_spec (sp n v1 v5 : Word) (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hm_lt : BitVec.slt (signExtend12 (4 : BitVec 12) - n) (0 : Word)) :
    let m := signExtend12 (4 : BitVec 12) - n
    cpsTriple (base + 432) (base + 904) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** (.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n)) := by
  intro m
  have hbody := divK_loopSetup_body_spec sp n v1 v5 460 (base + 432) hv_n
  rw [show (base + 432 : Word) + 12 = base + 444 from by bv_addr] at hbody
  have hbodye := cpsTriple_extend_code (divK_loopSetup_code_sub_modCode base) hbody
  have hblt_raw := blt_spec_gen .x1 .x0 460 m (0 : Word) (base + 444)
  rw [show (base + 444 : Word) + signExtend13 460 = base + 904 from by
        rw [mod_signExtend13_460]; bv_addr,
      show (base + 444 : Word) + 4 = base + 448 from by bv_addr] at hblt_raw
  have hblt_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hblt_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hm_lt ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hblte := cpsTriple_extend_code (blt_loopSetup_sub_modCode base) hblt_clean
  have hbltef := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hblte
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbodye hbltef
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

end EvmAsm.Evm64
