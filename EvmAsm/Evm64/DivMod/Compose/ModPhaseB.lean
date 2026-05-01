/-
  EvmAsm.Evm64.DivMod.Compose.ModPhaseB

  MOD mirrors of Phase B n=4 composition.
  Proof structure mirrors PhaseAB.lean with modCode instead of divCode.
  Blocks 0-1 are identical between divCode and modCode.
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (se12_1 se12_2 se12_3 se12_4 se12_4095)
open EvmAsm.Rv64.AddrNorm (se12_32
  bv64_4mul_9 bv64_4mul_10 bv64_4mul_11 bv64_4mul_12 bv64_4mul_13
  bv64_4mul_14 bv64_4mul_15)

-- ============================================================================
-- MOD CodeReq subsumption lemmas for blocks 0 and 1
-- Proofs mirror PhaseAB.lean: skip block 0 (phaseA), match block 1 (phaseB).
-- For modCode, blocks 0-1 are at identical positions as divCode.
-- ============================================================================

/-- Skip the phaseA block when descending into `modCode`: any membership in
    the phaseB block (left of the remaining union) lifts to membership in
    `phaseA ∪ (phaseB ∪ rest)`. Used by all 10 `*_sub_modCode` theorems in
    this file to avoid repeating the disjoint-range incantation. -/
private theorem sub_modCode_of_phaseB_left {base : Word} {rest : CodeReq} :
    ∀ a i,
      CodeReq.ofProg (base + phaseBOff) divK_phaseB a = some i →
      ((CodeReq.ofProg base (divK_phaseA 1020)).union
        ((CodeReq.ofProg (base + phaseBOff) divK_phaseB).union rest)) a = some i :=
  CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range
      (fun k1 k2 hk1 hk2 => by
        simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left)

theorem divK_phaseB_init1_code_sub_modCode {base : Word} :
    ∀ a i, (divK_phaseB_init1_code (base + phaseBOff)) a = some i → (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have h1 := CodeReq.ofProg_mono_sub (base + phaseBOff) (base + phaseBOff) divK_phaseB
    (divK_phaseB.take 7) 0
    (by bv_addr) (by decide) (by decide) (by decide) a i h
  exact sub_modCode_of_phaseB_left a i h1

theorem divK_phaseB_init2_code_sub_modCode {base : Word} :
    ∀ a i, (divK_phaseB_init2_code (base + 60)) a = some i → (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have h1 := CodeReq.ofProg_mono_sub (base + phaseBOff) (base + 60) divK_phaseB
    (divK_phaseB.drop 7 |>.take 2) 7
    (by bv_addr) (by decide) (by decide) (by decide) a i h
  exact sub_modCode_of_phaseB_left a i h1

theorem addi_x5_singleton_sub_modCode {base : Word} :
    ∀ a i, (CodeReq.singleton (base + 68) (.ADDI .x5 .x0 4)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 9
    (by decide) (by decide)
  rw [bv64_4mul_9,
      show (base + phaseBOff : Word) + 36 = base + 68 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_modCode_of_phaseB_left a i h1

theorem bne_x10_singleton_sub_modCode {base : Word} :
    ∀ a i, (CodeReq.singleton (base + 72) (.BNE .x10 .x0 24)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 10
    (by decide) (by decide)
  rw [bv64_4mul_10,
      show (base + phaseBOff : Word) + 40 = base + 72 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_modCode_of_phaseB_left a i h1

theorem divK_phaseB_tail_code_sub_modCode {base : Word} :
    ∀ a i, (divK_phaseB_tail_code (base + phaseBTailOff)) a = some i → (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have h1 := CodeReq.ofProg_mono_sub (base + phaseBOff) (base + phaseBTailOff) divK_phaseB
    (divK_phaseB.drop 16) 16
    (by bv_addr) (by decide) (by decide) (by decide) a i h
  exact sub_modCode_of_phaseB_left a i h1

-- Address normalization helpers
-- The former `mod_phB_off_28` (identical to PhaseAB's private `phB_off_28`)
-- now lives in `Compose/Base.lean` as the shared `phB_off_28` and is used
-- directly from both the DIV and MOD sides.
theorem mod_phB_i2_8 {base : Word} : (base + 60 : Word) + 8 = base + 68 := by bv_addr
theorem mod_phB_addi_4 {base : Word} : (base + 68 : Word) + 4 = base + 72 := by bv_addr
theorem mod_phB_bne_4 {base : Word} : (base + 72 : Word) + 4 = base + 76 := by bv_addr
theorem mod_phB_t_20 {base : Word} : (base + phaseBTailOff : Word) + 20 = base + clzOff := by bv_addr
-- `mod_signExtend13_24` → use `se13_24` from `Compose/Base.lean`.
theorem mod_phB_sp24_32 {sp : Word} :
    sp + ((4 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat +
      signExtend12 (32 : BitVec 12) = sp + 56 := by
  simp only [se12_4095, se12_32]
  bv_addr

-- ============================================================================
-- MOD Phase B n=4 (b[3] ≠ 0): init1→init2→ADDI→BNE(taken)→tail
-- Mirror of evm_div_phaseB_n4_spec_within with modCode.
-- ============================================================================

/-- MOD Phase B for n=4 (b[3] ≠ 0): x5 = b[3], x10 = b[3] (leading limb).
    init1 → init2 → ADDI x5=4 → BNE(taken, b[3]≠0) → tail. -/
theorem evm_mod_phaseB_n4_spec_within (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3nz : b3 ≠ 0) :
    cpsTripleWithin 21 (base + phaseBOff) (base + clzOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) **
       ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b3) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (4 : Word))) := by
  -- ---- Step 1: init1 (base+32 → base+60) — zero q[0..3] and u[5..7]
  have hinit1_raw := divK_phaseB_init1_spec_within sp (base + phaseBOff) q0 q1 q2 q3 u5 u6 u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTripleWithin_extend_code divK_phaseB_init1_code_sub_modCode hinit1_raw
  have hinit1f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit1
  -- ---- Step 2: init2 (base+60 → base+68) — load b[1], b[2]
  have hinit2_raw := divK_phaseB_init2_spec_within sp (base + 60) b1 b2 v6 v7
  simp only [mod_phB_i2_8] at hinit2_raw
  have hinit2 := cpsTripleWithin_extend_code divK_phaseB_init2_code_sub_modCode hinit2_raw
  seqFrame hinit1f hinit2
  -- ---- Step 3: ADDI x5 x0 4 at base+68 → base+72
  have haddi_raw := addi_x0_spec_gen_within .x5 v5 4 (base + 68) (by nofun)
  simp only [mod_phB_addi_4, se12_4] at haddi_raw
  have haddi := cpsTripleWithin_extend_code addi_x5_singleton_sub_modCode haddi_raw
  seqFrame hinit1fhinit2 haddi
  -- ---- Step 4: BNE x10 x0 24 at base+72, elim ntaken (b3=0 absurd)
  have hbne_raw := bne_spec_gen_within .x10 .x0 24 b3 (0 : Word) (base + 72)
  rw [show (base + 72 : Word) + signExtend13 24 = base + phaseBTailOff from by rv64_addr,
      mod_phB_bne_4] at hbne_raw
  have hbne_clean := cpsBranchWithin_takenStripPure2 hbne_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hb3nz)
  have hbne := cpsTripleWithin_extend_code bne_x10_singleton_sub_modCode hbne_clean
  seqFrame hinit1fhinit2haddi hbne
  -- ---- Step 5: Tail (base+96 → base+116) — store n=4, load leading limb b[3]
  have htail_raw := divK_phaseB_tail_spec_within sp (4 : Word) b3 nMem (base + phaseBTailOff)
  simp only [divK_phaseB_tail_pre_unfold, divK_phaseB_tail_post_unfold,
             mod_phB_t_20, mod_phB_sp24_32] at htail_raw
  have htail := cpsTripleWithin_extend_code divK_phaseB_tail_code_sub_modCode htail_raw
  seqFrame hinit1fhinit2haddihbne htail
  -- ---- Final consequence — permute assertions
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hinit1fhinit2haddihbnehtail

theorem addi_x5_3_sub_modCode {base : Word} :
    ∀ a i, (CodeReq.singleton (base + 76) (.ADDI .x5 .x0 3)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 11
    (by decide) (by decide)
  rw [bv64_4mul_11,
      show (base + phaseBOff : Word) + 44 = base + 76 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_modCode_of_phaseB_left a i h1

-- BNE x7 x0 16 at base+80 (index 12 of phaseB)
theorem bne_x7_16_sub_modCode {base : Word} :
    ∀ a i, (CodeReq.singleton (base + 80) (.BNE .x7 .x0 16)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 12
    (by decide) (by decide)
  rw [bv64_4mul_12,
      show (base + phaseBOff : Word) + 48 = base + 80 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_modCode_of_phaseB_left a i h1

-- ADDI x5 x0 2 at base+84 (index 13 of phaseB)
theorem addi_x5_2_sub_modCode {base : Word} :
    ∀ a i, (CodeReq.singleton (base + 84) (.ADDI .x5 .x0 2)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 13
    (by decide) (by decide)
  rw [bv64_4mul_13,
      show (base + phaseBOff : Word) + 52 = base + 84 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_modCode_of_phaseB_left a i h1

-- BNE x6 x0 8 at base+88 (index 14 of phaseB)
theorem bne_x6_8_sub_modCode {base : Word} :
    ∀ a i, (CodeReq.singleton (base + 88) (.BNE .x6 .x0 8)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 14
    (by decide) (by decide)
  rw [bv64_4mul_14,
      show (base + phaseBOff : Word) + 56 = base + 88 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_modCode_of_phaseB_left a i h1

-- ADDI x5 x0 1 at base+92 (index 15 of phaseB)
theorem addi_x5_1_sub_modCode {base : Word} :
    ∀ a i, (CodeReq.singleton (base + 92) (.ADDI .x5 .x0 1)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 15
    (by decide) (by decide)
  rw [bv64_4mul_15,
      show (base + phaseBOff : Word) + 60 = base + 92 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_modCode_of_phaseB_left a i h1

-- ============================================================================
-- MOD Phase B cascade constants and address lemmas
-- ============================================================================

-- signExtend13 constants for cascade branches: `signExtend13_{8,16}` now live
-- in `Compose/Base.lean` (shared with PhaseAB). `se12_*` come from AddrNorm.

-- nm1X8 = (n + signExtend12 4095) <<< 3 for each n value
theorem mod_divK_phaseB_n3_nm1_x8 :
    ((3 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (16 : Word) := by
  decide
theorem mod_divK_phaseB_n2_nm1_x8 :
    ((2 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (8 : Word) := by
  decide
theorem mod_divK_phaseB_n1_nm1_x8 :
    ((1 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (0 : Word) := by
  decide

-- Cascade address normalization
theorem mod_phB_step1_4 {base : Word} : (base + 76 : Word) + 4 = base + 80 := by bv_addr
theorem mod_phB_step1_8 {base : Word} : (base + 80 : Word) + 4 = base + 84 := by bv_addr
theorem mod_phB_step2_4 {base : Word} : (base + 84 : Word) + 4 = base + 88 := by bv_addr
theorem mod_phB_step2_8 {base : Word} : (base + 88 : Word) + 4 = base + 92 := by bv_addr
theorem mod_phB_fall_4 {base : Word} : (base + 92 : Word) + 4 = base + phaseBTailOff := by bv_addr

-- Tail memory address normalization
theorem mod_phB_sp16_32 {sp : Word} :
    (sp + (16 : Word) + (32 : Word)) = sp + 48 := by bv_addr
theorem mod_phB_sp8_32 {sp : Word} :
    (sp + (8 : Word) + (32 : Word)) = sp + 40 := by bv_addr
theorem mod_phB_sp0_32 {sp : Word} :
    (sp + (0 : Word) + (32 : Word)) = sp + 32 := by bv_addr

end EvmAsm.Evm64

-- n=3/2/1 cascade variants are in separate files:
-- ModPhaseBn3.lean, ModPhaseBn21.lean
