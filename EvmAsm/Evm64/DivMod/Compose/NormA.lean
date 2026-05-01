/-
  EvmAsm.Evm64.DivMod.Compose.NormA

  NormA, CopyAU, and LoopSetup compositions for DivMod.
  Extracted from Compose.lean sections 10i–10k.
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Section 10i: NormA composition (normalize dividend, 21 instructions)
-- base+312: top(3) + mergeA(5) + mergeB(5) + mergeA(5) + last(2) + JAL(1)
-- ============================================================================

/-- NormA code (block 5) is subsumed by divCode. -/
private theorem divK_normA_code_sub_divCode {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + normAOff) (divK_normA 40)) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left

-- signExtend12 rewrites pulled from the divmod_addr global set (AddrNorm.lean).
open EvmAsm.Evm64.DivMod.AddrNorm (se12_0 se12_8 se12_16 se12_24)
-- signExtend13/21 rewrites pulled from the rv64_addr global set (Rv64/AddrNorm.lean).
open EvmAsm.Rv64.AddrNorm (bv64_4mul_3)

/-- Full NormA: normalize dividend a[0..3] → u[0..4] and jump to loopSetup.
    base+312 → base+432 (21 instructions including JAL).
    u[4] = a[3]>>>antiShift, u[3..0] = merged shifted limbs. -/
theorem divK_normA_full_spec_within (sp a0 a1 a2 a3 v5 v7 v10 shift antiShift : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word) :
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    cpsTripleWithin 21 (base + normAOff) (base + loopSetupOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4056) ↦ₘ u0Old))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u1) ** (.x7 ↦ᵣ u0) ** (.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4056) ↦ₘ u0)) := by
  intro u4 u3 u2 u1 u0
  -- Top: LD a[3], SRL→u[4], SD u[4] (base+312 → base+324)
  have htop := divK_normA_top_spec_within 24 4024 sp a3 v5 v7 antiShift u4Old (base + normAOff)
  simp only [se12_24] at htop
  have htope := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCode a i
      (CodeReq.ofProg_mono_sub (base + normAOff) (base + normAOff) (divK_normA 40)
        (divK_normA_top_prog 24 4024) 0
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) htop
  -- Frame top with x6, x10, a[0..2], u[0..3]
  have htopef := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ v10) ** (.x6 ↦ᵣ shift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) **
     ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4056) ↦ₘ u0Old))
    (by pcFree) htope
  -- MergeA 1: u[3] = (a[3]<<<shift) | (a[2]>>>anti) (base+324 → base+344)
  have hma1 := divK_normA_mergeA_spec_within 16 4032 sp a3 a2 u4 v10 shift antiShift u3Old (base + normAOff + 12)
  simp only [se12_16] at hma1
  rw [show (base + normAOff + 12 : Word) + 20 = base + normAOff + 32 from by bv_addr] at hma1
  have hma1e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCode a i
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
  -- MergeB: u[2] = (a[2]<<<shift) | (a[1]>>>anti) (base+344 → base+364)
  have hmb := divK_normA_mergeB_spec_within 8 4040 sp a2 a1 u3 (a2 >>> (antiShift.toNat % 64))
    shift antiShift u2Old (base + normAOff + 32)
  simp only [se12_8] at hmb
  rw [show (base + normAOff + 32 : Word) + 20 = base + normAOff + 52 from by bv_addr] at hmb
  have hmbe := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCode a i
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
  -- MergeA 2: u[1] = (a[1]<<<shift) | (a[0]>>>anti) (base+364 → base+384)
  have hma2 := divK_normA_mergeA_spec_within 0 4048 sp a1 a0 u2 (a1 >>> (antiShift.toNat % 64))
    shift antiShift u1Old (base + normAOff + 52)
  simp only [se12_0] at hma2
  rw [show (base + normAOff + 52 : Word) + 20 = base + normAOff + 72 from by bv_addr] at hma2
  have hma2e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCode a i
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
  -- Last: u[0] = a[0]<<<shift (base+384 → base+392)
  have hlast := divK_normA_last_spec_within 4056 sp a0 shift u0Old (base + normAOff + 72)
  rw [show (base + normAOff + 72 : Word) + 8 = base + normAOff + 80 from by bv_addr] at hlast
  have hlaste := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCode a i
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
  -- JAL x0 40 at base+392 → base+432 (1 instruction, empAssertion pre/post)
  have hjal := jal_x0_spec_gen_within 40 (base + normAOff + 80)
  rw [show (base + normAOff + 80 : Word) + signExtend21 40 = base + loopSetupOff from by rv64_addr] at hjal
  have hjale := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact divK_normA_code_sub_divCode a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + normAOff) (divK_normA 40) 20
          (by decide) (by decide)
        rw [show (base + normAOff : Word) + BitVec.ofNat 64 (4 * 20) = base + normAOff + 80 from by bv_addr]
          at hlookup
        exact hlookup) a i h)) hjal
  -- Frame JAL with everything, then strip empAssertion via consequence
  let postAll := (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u1) ** (.x7 ↦ᵣ u0) **
    (.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
    (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
    ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
    ((sp + signExtend12 4056) ↦ₘ u0)
  have hjalef := cpsTripleWithin_frameR postAll (by pcFree) hjale
  -- Compose h12345 with JAL by consequence (empAssertion → postAll → postAll)
  -- Since JAL has empAssertion pre/post and frame is postAll, the result is (empAssertion ** postAll).
  -- Use consequence to strip empAssertion from both sides.
  have hjal_clean : cpsTripleWithin 1 (base + normAOff + 80) (base + loopSetupOff) (divCode base) postAll postAll :=
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

theorem divK_normA_full_spec (sp a0 a1 a2 a3 v5 v7 v10 shift antiShift : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word) :
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    cpsTripleWithin 21 (base + normAOff) (base + loopSetupOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4056) ↦ₘ u0Old))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u1) ** (.x7 ↦ᵣ u0) ** (.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4056) ↦ₘ u0)) :=
  divK_normA_full_spec_within sp a0 a1 a2 a3 v5 v7 v10 shift antiShift
    u0Old u1Old u2Old u3Old u4Old base

-- ============================================================================
-- Section 10j: CopyAU composition (copy a[] to u[], 9 instructions)
-- base+396: used when shift=0 (no normalization needed)
-- ============================================================================

/-- CopyAU code (block 6) is subsumed by divCode. -/
private theorem divK_copyAU_code_sub_divCode {base : Word} :
    ∀ a i, (divK_copyAU_code (base + copyAUOff)) a = some i → (divCode base) a = some i := by
  unfold divCode divK_copyAU_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left

/-- Full CopyAU: copy a[0..3] to u[0..3], set u[4]=0.
    base+396 → base+432 (9 instructions). -/
theorem divK_copyAU_full_spec_within (sp : Word)
    (a0 a1 a2 a3 : Word) (u0 u1 u2 u3 u4 v5 : Word) (base : Word) :
    cpsTripleWithin 9 (base + copyAUOff) (base + loopSetupOff) (divCode base)
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
  have hcopy := divK_copyAU_spec_within sp (base + copyAUOff) a0 a1 a2 a3 u0 u1 u2 u3 u4 v5
  rw [show (base + copyAUOff : Word) + 36 = base + loopSetupOff from by bv_addr] at hcopy
  exact cpsTripleWithin_extend_code divK_copyAU_code_sub_divCode hcopy

theorem divK_copyAU_full_spec (sp : Word)
    (a0 a1 a2 a3 : Word) (u0 u1 u2 u3 u4 v5 : Word) (base : Word) :
    cpsTripleWithin 9 (base + copyAUOff) (base + loopSetupOff) (divCode base)
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
       ((sp + signExtend12 4024) ↦ₘ (0 : Word))) :=
  divK_copyAU_full_spec_within sp a0 a1 a2 a3 u0 u1 u2 u3 u4 v5 base

-- ============================================================================
-- Section 10k: LoopSetup composition (4 instructions at base+432)
-- LD n, ADDI 4, SUB m=4-n, BLT m<0
-- ============================================================================

/-- LoopSetup code (block 7) is subsumed by divCode. -/
private theorem divK_loopSetup_code_sub_divCode {base : Word} :
    ∀ a i, (divK_loopSetup_code 464 (base + loopSetupOff)) a = some i → (divCode base) a = some i := by
  unfold divCode divK_loopSetup_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left

/-- BLT singleton at base+loopSetupOff+12 (index 3 of loopSetup) is subsumed by divCode. -/
private theorem blt_loopSetup_sub_divCode {base : Word} :
    ∀ a i, (CodeReq.singleton (base + loopSetupOff + 12) (.BLT .x1 .x0 464)) a = some i →
      (divCode base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + loopSetupOff) (divK_loopSetup 464) 3
    (by decide) (by decide)
  rw [bv64_4mul_3] at hlookup
  exact divK_loopSetup_code_sub_divCode a i
    (CodeReq.singleton_mono hlookup a i h)

-- `se13_464` moved to `Compose/Base.lean` (shared with ModNormA).

/-- LoopSetup when m ≥ 0 (n ≤ 4): falls through to loop body at base+448.
    Loads n from scratch, computes m = 4-n, BLT not taken. -/
theorem divK_loopSetup_ntaken_spec_within (sp n v1 v5 : Word) (base : Word)
    (hm_ge : ¬BitVec.slt (signExtend12 (4 : BitVec 12) - n) (0 : Word)) :
    let m := signExtend12 (4 : BitVec 12) - n
    cpsTripleWithin 4 (base + loopSetupOff) (base + loopBodyOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** (.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n)) := by
  intro m
  have hbody := divK_loopSetup_body_spec_within sp n v1 v5 464 (base + loopSetupOff)
  have hbodye := cpsTripleWithin_extend_code divK_loopSetup_code_sub_divCode hbody
  have hblt_raw := blt_spec_gen_within .x1 .x0 464 m (0 : Word) (base + loopSetupOff + 12)
  rw [show (base + loopSetupOff + 12 : Word) + signExtend13 464 = base + denormOff from by rv64_addr,
      show (base + loopSetupOff + 12 : Word) + 4 = base + loopBodyOff from by bv_addr] at hblt_raw
  have hblt_clean := cpsBranchWithin_ntakenStripPure2 hblt_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hm_ge)
  have hblte := cpsTripleWithin_extend_code blt_loopSetup_sub_divCode hblt_clean
  have hbltef := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hblte
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbodye hbltef
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

theorem divK_loopSetup_taken_spec_within (sp n v1 v5 : Word) (base : Word)
    (hm_lt : BitVec.slt (signExtend12 (4 : BitVec 12) - n) (0 : Word)) :
    let m := signExtend12 (4 : BitVec 12) - n
    cpsTripleWithin 4 (base + loopSetupOff) (base + denormOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** (.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n)) := by
  intro m
  have hbody := divK_loopSetup_body_spec_within sp n v1 v5 464 (base + loopSetupOff)
  have hbodye := cpsTripleWithin_extend_code divK_loopSetup_code_sub_divCode hbody
  have hblt_raw := blt_spec_gen_within .x1 .x0 464 m (0 : Word) (base + loopSetupOff + 12)
  rw [show (base + loopSetupOff + 12 : Word) + signExtend13 464 = base + denormOff from by rv64_addr,
      show (base + loopSetupOff + 12 : Word) + 4 = base + loopBodyOff from by bv_addr] at hblt_raw
  have hblt_clean := cpsBranchWithin_takenStripPure2 hblt_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hm_lt ((sepConj_pure_right _).mp h_rest).2)
  have hblte := cpsTripleWithin_extend_code blt_loopSetup_sub_divCode hblt_clean
  have hbltef := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hblte
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbodye hbltef
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12
