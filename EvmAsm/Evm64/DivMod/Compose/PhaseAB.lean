/-
  EvmAsm.Evm64.DivMod.Compose.PhaseAB

  Phase A and Phase B composition specs for DivMod.
  Includes subsumption lemmas, signExtend/address helpers,
  zero-path composition, Phase A ntaken, Phase B for n=4/3/2/1,
  and Phase AB n=4 composition.
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm
  (bv64_4mul_9 bv64_4mul_10 bv64_4mul_11 bv64_4mul_12 bv64_4mul_13
   bv64_4mul_14 bv64_4mul_15)

-- ============================================================================
-- Section 5: CodeReq subsumption lemmas (via mono_unionAll / mono_sub_unionAll)
-- Each sub-spec's CodeReq is subsumed by divCode using structural union reasoning.
-- ============================================================================

/-- Skip the phaseA block when descending into `divCode`: any membership in
    the phaseB block (left of the remaining union) lifts to membership in
    `phaseA ∪ (phaseB ∪ rest)`. Used by the ten `*_sub_divCode` theorems below
    that would otherwise repeat the disjoint-range incantation verbatim. -/
private theorem sub_divCode_of_phaseB_left (base : Word) (rest : CodeReq) :
    ∀ a i,
      CodeReq.ofProg (base + phaseBOff) divK_phaseB a = some i →
      ((CodeReq.ofProg base (divK_phaseA 1020)).union
        ((CodeReq.ofProg (base + phaseBOff) divK_phaseB).union rest)) a = some i :=
  CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range
      (fun k1 k2 hk1 hk2 => by
        simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _)

/-- Phase A code (8 instructions, block 0) is subsumed by divCode. -/
private theorem divK_phaseA_code_sub_divCode (base : Word) :
    ∀ a i, (divK_phaseA_code base) a = some i → (divCode base) a = some i := by
  unfold divCode divK_phaseA_code; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _

/-- Zero path code (5 instructions, block 11) is subsumed by divCode. -/
private theorem divK_zeroPath_code_sub_divCode (base : Word) :
    ∀ a i, (divK_zeroPath_code (base + zeroPathOff)) a = some i → (divCode base) a = some i := by
  unfold divCode divK_zeroPath_code; simp only [CodeReq.unionAll_cons]
  -- Skip blocks 0-10, then match block 11
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- BEQ singleton at base+28 is subsumed by divCode (part of block 0: phaseA). -/
private theorem beq_singleton_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 28) (.BEQ .x5 .x0 1020)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  exact CodeReq.union_mono_left _ _ a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup base (divK_phaseA 1020) 7
      (by decide) (by decide)) a i h)

/-- Phase B init1 code (ofProg sub-range of block 1) is subsumed by divCode. -/
private theorem divK_phaseB_init1_code_sub_divCode (base : Word) :
    ∀ a i, (divK_phaseB_init1_code (base + phaseBOff)) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  -- Lift from init1 sub-range to full phaseB block
  have h1 := CodeReq.ofProg_mono_sub (base + phaseBOff) (base + phaseBOff) divK_phaseB
    (divK_phaseB.take 7) 0
    (by bv_addr) (by decide) (by decide) (by decide) a i h
  -- Skip block 0 (phaseA disjoint from phaseB), match block 1
  exact sub_divCode_of_phaseB_left base _ a i h1

/-- Phase B init2 code (ofProg sub-range of block 1) is subsumed by divCode. -/
private theorem divK_phaseB_init2_code_sub_divCode (base : Word) :
    ∀ a i, (divK_phaseB_init2_code (base + 60)) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have h1 := CodeReq.ofProg_mono_sub (base + phaseBOff) (base + 60) divK_phaseB
    (divK_phaseB.drop 7 |>.take 2) 7
    (by bv_addr) (by decide) (by decide) (by decide) a i h
  exact sub_divCode_of_phaseB_left base _ a i h1

/-- ADDI x5 x0 4 singleton at base+68 (part of block 1: phaseB) is subsumed by divCode. -/
private theorem addi_x5_singleton_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 68) (.ADDI .x5 .x0 4)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 9
    (by decide) (by decide)
  rw [bv64_4mul_9,
      show (base + phaseBOff : Word) + 36 = base + 68 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_divCode_of_phaseB_left base _ a i h1

/-- BNE x10 x0 24 singleton at base+72 (part of block 1: phaseB) is subsumed by divCode. -/
private theorem bne_x10_singleton_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 72) (.BNE .x10 .x0 24)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 10
    (by decide) (by decide)
  rw [bv64_4mul_10,
      show (base + phaseBOff : Word) + 40 = base + 72 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_divCode_of_phaseB_left base _ a i h1

/-- Phase B tail code (ofProg sub-range of block 1) is subsumed by divCode. -/
private theorem divK_phaseB_tail_code_sub_divCode (base : Word) :
    ∀ a i, (divK_phaseB_tail_code (base + 96)) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have h1 := CodeReq.ofProg_mono_sub (base + phaseBOff) (base + 96) divK_phaseB
    (divK_phaseB.drop 16) 16
    (by bv_addr) (by decide) (by decide) (by decide) a i h
  exact sub_divCode_of_phaseB_left base _ a i h1

-- ============================================================================
-- Section 6: signExtend13 normalization
--
-- `signExtend13_{8,16,24,1020}` now live in `Compose/Base.lean` and are shared
-- with the MOD-side files (ModPhaseB / ModNorm / ModNormA) — the identical
-- `mod_signExtend13_*` duplicates on the MOD side are gone.
-- ============================================================================

-- `signExtend13_{24,1020}` / `divK_se12_{4}` now live in `Compose/Base.lean`
-- and `Rv64/Instructions.lean` respectively — call sites use the shared names
-- (`signExtend13_24`, `signExtend13_1020`, `signExtend12_4`) directly.

-- Phase B tail address: nm1X8 = (4 + signExtend12 4095) <<< 3 = 24
private theorem divK_phaseB_n4_nm1_x8 :
    ((4 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (24 : Word) := by
  decide

-- `divK_se12_{4,32}` removed: use the `@[simp]`-tagged `signExtend12_4`,
-- `signExtend12_32` from `Rv64/Instructions.lean` directly.

-- Address normalization lemmas `phB_off_{4..28}` now live in `Compose/Base.lean`
-- and are shared with the MOD-side files (ModPhaseB / ModPhaseBn3 / ModPhaseBn21).
private theorem phB_i2_8 (base : Word) : (base + 60 : Word) + 8 = base + 68 := by bv_addr
private theorem phB_addi_4 (base : Word) : (base + 68 : Word) + 4 = base + 72 := by bv_addr
private theorem phB_bne_4 (base : Word) : (base + 72 : Word) + 4 = base + 76 := by bv_addr
private theorem phB_t_20 (base : Word) : (base + 96 : Word) + 20 = base + clzOff := by bv_addr
private theorem phB_sp24_32 (sp : Word) : (sp + (24 : Word) + (32 : Word)) = sp + 56 := by bv_addr

-- ============================================================================
-- ============================================================================
-- Section 7: Zero path composition (b = 0)
-- Phase A body → BEQ(taken) → zeroPath → exit
-- ============================================================================

/-- When b = 0 (all limbs zero), evm_div writes zeros and advances sp.
    Execution path: phaseA body (7 instrs), BEQ taken, zeroPath (5 instrs). -/
theorem evm_div_bzero_spec (sp base : Word)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbz : b0 ||| b1 ||| b2 ||| b3 = 0) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  -- Step 1: Phase A body (base → base+28, 7 straight-line instructions)
  -- Extend to divCode CodeReq
  have hbody := cpsTriple_extend_code (divK_phaseA_code_sub_divCode base)
    (divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10)
  -- Step 2: BEQ at base+28, eliminate ntaken via hbz
  have hbeq_raw := beq_spec_gen .x5 .x0 1020 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + 28)
  rw [show (base + 28 : Word) + signExtend13 1020 = base + zeroPathOff from by rv64_addr,
      show (base + 28 : Word) + 4 = base + phaseBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranch_takenStripPure2 hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hbz ((sepConj_pure_right _).mp h_rest).2)
  -- Extend BEQ to divCode CodeReq
  have hbeq := cpsTriple_extend_code (beq_singleton_sub_divCode base) hbeq_clean
  -- Step 3: Frame BEQ with regs + mem (no code atoms needed in frame)
  have hbeq_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  -- Step 4: Compose body → BEQ(taken): base → base+1048
  have hAB := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- Step 5: ZeroPath (base+1048 → base+1068)
  -- Extend to divCode CodeReq
  have hzp := cpsTriple_extend_code (divK_zeroPath_code_sub_divCode base)
    (divK_zeroPath_spec sp (base + zeroPathOff) b0 b1 b2 b3)
  rw [show (base + zeroPathOff : Word) + 20 = base + nopOff from by bv_addr] at hzp
  -- Frame ZP with x5 + x10 + x0
  have hzp_framed := cpsTriple_frameR
    ((.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hzp
  -- Step 6: Compose AB → ZP: base → base+1068
  have hABZ := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAB hzp_framed
  -- Step 7: Final consequence — rewrite bor → 0
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by rw [hbz] at hq; xperm_hyp hq)
    hABZ

-- ============================================================================
-- Section 8: Phase A not-taken composition (b ≠ 0)
-- Phase A body → BEQ(ntaken) → fall through to Phase B
-- ============================================================================

/-- When b ≠ 0, evm_div falls through Phase A to Phase B at base+32.
    Execution path: phaseA body (7 instrs), BEQ not taken. -/
theorem evm_div_phaseA_ntaken_spec (sp base : Word)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0) :
    cpsTriple base (base + phaseBOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  -- Step 1: Phase A body (base → base+28, 7 straight-line instructions)
  have hbody := cpsTriple_extend_code (divK_phaseA_code_sub_divCode base)
    (divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10)
  -- Step 2: BEQ at base+28, eliminate taken path (b=0 absurd since hbnz)
  have hbeq_raw := beq_spec_gen .x5 .x0 1020 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + 28)
  rw [show (base + 28 : Word) + signExtend13 1020 = base + zeroPathOff from by rv64_addr,
      show (base + 28 : Word) + 4 = base + phaseBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranch_ntakenStripPure2 hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hbnz)
  -- Extend BEQ to divCode CodeReq
  have hbeq := cpsTriple_extend_code (beq_singleton_sub_divCode base) hbeq_clean
  -- Step 3: Frame BEQ with regs + mem
  have hbeq_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  -- Step 4: Compose body → BEQ(ntaken): base → base+32
  have hAB := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- Step 5: Final consequence — permute assertions
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hAB

-- ============================================================================
-- Section 9: Phase B composition for n=4 (b[3] ≠ 0)
-- init1 → init2 → ADDI x5=4 → BNE x10(taken) → tail
-- ============================================================================

/-- Phase B when b[3] ≠ 0 (n=4): zero scratch, load b[1..2], cascade BNE taken, load leading limb.
    Execution path: init1 (7 instrs) + init2 (2) + ADDI (1) + BNE taken (1) + tail (5) = 16 instrs.
    Exit at base+116 (start of CLZ). x5 = b[3] (leading limb), x6 = b[1], x7 = b[2], n = 4. -/
theorem evm_div_phaseB_n4_spec (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3nz : b3 ≠ 0) :
    cpsTriple (base + phaseBOff) (base + clzOff) (divCode base)
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
  have hinit1_raw := divK_phaseB_init1_spec sp (base + phaseBOff) q0 q1 q2 q3 u5 u6 u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_divCode base) hinit1_raw
  have hinit1f := cpsTriple_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit1
  -- ---- Step 2: init2 (base+60 → base+68) — load b[1], b[2]
  have hinit2_raw := divK_phaseB_init2_spec sp (base + 60) b1 b2 v6 v7
  simp only [phB_i2_8] at hinit2_raw
  have hinit2 := cpsTriple_extend_code (divK_phaseB_init2_code_sub_divCode base) hinit2_raw
  seqFrame hinit1f hinit2
  -- ---- Step 3: ADDI x5 x0 4 at base+68 → base+72
  have haddi_raw := addi_x0_spec_gen .x5 v5 4 (base + 68) (by nofun)
  simp only [phB_addi_4, signExtend12_4] at haddi_raw
  have haddi := cpsTriple_extend_code (addi_x5_singleton_sub_divCode base) haddi_raw
  seqFrame hinit1fhinit2 haddi
  -- ---- Step 4: BNE x10 x0 24 at base+72, elim ntaken (b3=0 absurd)
  have hbne_raw := bne_spec_gen .x10 .x0 24 b3 (0 : Word) (base + 72)
  rw [show (base + 72 : Word) + signExtend13 24 = base + 96 from by
        rv64_addr, phB_bne_4] at hbne_raw
  have hbne_clean := cpsBranch_takenStripPure2 hbne_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hb3nz)
  have hbne := cpsTriple_extend_code (bne_x10_singleton_sub_divCode base) hbne_clean
  seqFrame hinit1fhinit2haddi hbne
  -- ---- Step 5: Tail (base+96 → base+116) — store n=4, load leading limb b[3]
  have htail_raw := divK_phaseB_tail_spec sp (4 : Word) b3 nMem (base + 96)
  simp only [divK_phaseB_tail_pre_unfold, divK_phaseB_tail_post_unfold,
             phB_t_20, divK_phaseB_n4_nm1_x8, signExtend12_32, phB_sp24_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_divCode base) htail_raw
  seqFrame hinit1fhinit2haddihbne htail
  -- ---- Step 6: Final consequence — permute assertions
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hinit1fhinit2haddihbnehtail

-- ============================================================================
-- Section 10: Phase A + Phase B n=4 composition (b≠0, b[3]≠0)
-- base → base+116 (entry to CLZ)
-- ============================================================================

/-- When b ≠ 0 and b[3] ≠ 0, evm_div executes Phase A (ntaken) then Phase B (n=4).
    Execution: 8 + 16 = 24 instructions, base → base+116 (start of CLZ).
    Pre/postcondition shapes reflect frame structure from composition. -/
theorem evm_div_phaseAB_n4_spec (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0) :
    cpsTriple base (base + clzOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b3) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 32) ↦ₘ b0) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word))) := by
  have hA := evm_div_phaseA_ntaken_spec sp base b0 b1 b2 b3 v5 v10 hbnz
  have hAf := cpsTriple_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
     ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hA
  have hB := evm_div_phaseB_n4_spec sp base b1 b2 b3
    (b0 ||| b1 ||| b2 ||| b3) v6 v7 q0 q1 q2 q3 u5 u6 u7 nMem
    hb3nz
  have hBf := cpsTriple_frameR
    (((sp + 32) ↦ₘ b0))
    (by pcFree) hB
  have hAB := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAf hBf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hAB

-- ============================================================================
-- Section 10b: Phase B cascade step subsumption lemmas
-- ============================================================================

-- ADDI x5 x0 3 at base+76 (index 11 of phaseB)
private theorem addi_x5_3_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 76) (.ADDI .x5 .x0 3)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 11
    (by decide) (by decide)
  rw [bv64_4mul_11,
      show (base + phaseBOff : Word) + 44 = base + 76 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_divCode_of_phaseB_left base _ a i h1

-- BNE x7 x0 16 at base+80 (index 12 of phaseB)
private theorem bne_x7_16_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 80) (.BNE .x7 .x0 16)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 12
    (by decide) (by decide)
  rw [bv64_4mul_12,
      show (base + phaseBOff : Word) + 48 = base + 80 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_divCode_of_phaseB_left base _ a i h1

-- ADDI x5 x0 2 at base+84 (index 13 of phaseB)
private theorem addi_x5_2_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 84) (.ADDI .x5 .x0 2)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 13
    (by decide) (by decide)
  rw [bv64_4mul_13,
      show (base + phaseBOff : Word) + 52 = base + 84 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_divCode_of_phaseB_left base _ a i h1

-- BNE x6 x0 8 at base+88 (index 14 of phaseB)
private theorem bne_x6_8_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 88) (.BNE .x6 .x0 8)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 14
    (by decide) (by decide)
  rw [bv64_4mul_14,
      show (base + phaseBOff : Word) + 56 = base + 88 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_divCode_of_phaseB_left base _ a i h1

-- ADDI x5 x0 1 at base+92 (index 15 of phaseB)
private theorem addi_x5_1_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 92) (.ADDI .x5 .x0 1)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 15
    (by decide) (by decide)
  rw [bv64_4mul_15,
      show (base + phaseBOff : Word) + 60 = base + 92 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact sub_divCode_of_phaseB_left base _ a i h1

-- ============================================================================
-- Section 10c: Phase B cascade constants and address lemmas
-- ============================================================================

-- signExtend constants for cascade steps
-- `divK_se12_{1,2,3}` removed: use `signExtend12_{1,2,3}` from Rv64/Instructions.lean.
-- `signExtend13_{8,16}` moved to `Compose/Base.lean` (shared with MOD side).

-- nm1X8 = (n + signExtend12 4095) <<< 3 for each n value
private theorem divK_phaseB_n3_nm1_x8 :
    ((3 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (16 : Word) := by
  decide
private theorem divK_phaseB_n2_nm1_x8 :
    ((2 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (8 : Word) := by
  decide
private theorem divK_phaseB_n1_nm1_x8 :
    ((1 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (0 : Word) := by
  decide

-- Cascade address normalization
private theorem phB_step1_4 (base : Word) : (base + 76 : Word) + 4 = base + 80 := by bv_addr
private theorem phB_step1_8 (base : Word) : (base + 80 : Word) + 4 = base + 84 := by bv_addr
private theorem phB_step2_4 (base : Word) : (base + 84 : Word) + 4 = base + 88 := by bv_addr
private theorem phB_step2_8 (base : Word) : (base + 88 : Word) + 4 = base + 92 := by bv_addr
private theorem phB_fall_4 (base : Word) : (base + 92 : Word) + 4 = base + 96 := by bv_addr

-- Tail memory address normalization
private theorem phB_sp16_32 (sp : Word) : (sp + (16 : Word) + (32 : Word)) = sp + 48 := by bv_addr
private theorem phB_sp8_32 (sp : Word) : (sp + (8 : Word) + (32 : Word)) = sp + 40 := by bv_addr
private theorem phB_sp0_32 (sp : Word) : (sp + (0 : Word) + (32 : Word)) = sp + 32 := by bv_addr

-- ============================================================================
-- Section 10d: Phase B n=3 (b[3]=0, b[2]≠0)
-- init1 → init2 → ADDI x5=4 → BNE x10 ntaken → ADDI x5=3 → BNE x7 taken → tail
-- ============================================================================

/-- Phase B when b[3]=0, b[2]≠0 (n=3): zero scratch, load b[1..2], cascade to n=3, load b[2].
    Execution: init1(7) + init2(2) + step0(2) + step1(2) + tail(5) = 18 instrs.
    Exit at base+116 (start of CLZ). x5 = b[2] (leading limb), n = 3. -/
theorem evm_div_phaseB_n3_spec (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0) :
    cpsTriple (base + phaseBOff) (base + clzOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) **
       ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (3 : Word))) := by
  -- ---- init1 (base+32 → base+60)
  have hinit1_raw := divK_phaseB_init1_spec sp (base + phaseBOff) q0 q1 q2 q3 u5 u6 u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_divCode base) hinit1_raw
  have hinit1f := cpsTriple_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit1
  -- ---- init2 (base+60 → base+68)
  have hinit2_raw := divK_phaseB_init2_spec sp (base + 60) b1 b2 v6 v7
  simp only [phB_i2_8] at hinit2_raw
  have hinit2 := cpsTriple_extend_code (divK_phaseB_init2_code_sub_divCode base) hinit2_raw
  have hinit2f := cpsTriple_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit2
  have h12 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hinit1f hinit2f
  -- ---- Cascade step 0: ADDI x5=4 (base+68 → base+72)
  have haddi0_raw := addi_x0_spec_gen .x5 v5 4 (base + 68) (by nofun)
  simp only [phB_addi_4, signExtend12_4] at haddi0_raw
  have haddi0 := cpsTriple_extend_code (addi_x5_singleton_sub_divCode base) haddi0_raw
  have haddi0f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi0
  have h123 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 haddi0f
  -- ---- Cascade step 0: BNE x10 ntaken (base+72 → base+76, b3=0)
  have hbne0_raw := bne_spec_gen .x10 .x0 24 b3 (0 : Word) (base + 72)
  rw [show (base + 72 : Word) + signExtend13 24 = base + 96 from by
        rv64_addr, phB_bne_4] at hbne0_raw
  have hbne0_clean := cpsBranch_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _).mp h_rest).2)
  have hbne0 := cpsTriple_extend_code (bne_x10_singleton_sub_divCode base) hbne0_clean
  have hbne0f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne0
  have h1234 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hbne0f
  -- ---- Cascade step 1: ADDI x5=3 (base+76 → base+80)
  have haddi1_raw := addi_x0_spec_gen .x5 (4 : Word) 3 (base + 76) (by nofun)
  simp only [phB_step1_4, signExtend12_3] at haddi1_raw
  have haddi1 := cpsTriple_extend_code (addi_x5_3_sub_divCode base) haddi1_raw
  have haddi1f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi1
  have h12345 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234 haddi1f
  -- ---- Cascade step 1: BNE x7 taken (base+80 → base+96, b2≠0)
  have hbne1_raw := bne_spec_gen .x7 .x0 16 b2 (0 : Word) (base + 80)
  rw [show (base + 80 : Word) + signExtend13 16 = base + 96 from by
        rv64_addr, phB_step1_8] at hbne1_raw
  have hbne1_clean := cpsBranch_takenStripPure2 hbne1_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hb2nz)
  have hbne1 := cpsTriple_extend_code (bne_x7_16_sub_divCode base) hbne1_clean
  have hbne1f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (3 : Word)) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne1
  have h123456 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345 hbne1f
  -- ---- Tail (base+96 → base+116)
  have htail_raw := divK_phaseB_tail_spec sp (3 : Word) b2 nMem (base + 96)
  simp only [divK_phaseB_tail_pre_unfold, divK_phaseB_tail_post_unfold,
             phB_t_20, divK_phaseB_n3_nm1_x8, signExtend12_32, phB_sp16_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_divCode base) htail_raw
  have htailf := cpsTriple_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)))
    (by pcFree) htail
  have hphaseB := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123456 htailf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hphaseB

-- ============================================================================
-- Section 10e: Phase B n=2 (b[3]=b[2]=0, b[1]≠0)
-- init1 → init2 → ADDI x5=4 → BNE x10 ntaken → ADDI x5=3 → BNE x7 ntaken
-- → ADDI x5=2 → BNE x6 taken → tail
-- ============================================================================

/-- Phase B when b[3]=b[2]=0, b[1]≠0 (n=2): zero scratch, cascade to n=2, load b[1].
    Execution: init1(7) + init2(2) + 3×step(6) + tail(5) = 20 instrs.
    Exit at base+116. x5 = b[1] (leading limb), n = 2. -/
theorem evm_div_phaseB_n2_spec (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0) :
    cpsTriple (base + phaseBOff) (base + clzOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) **
       ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b1) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (2 : Word))) := by
  -- ---- init1 (base+32 → base+60)
  have hinit1_raw := divK_phaseB_init1_spec sp (base + phaseBOff) q0 q1 q2 q3 u5 u6 u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_divCode base) hinit1_raw
  have hinit1f := cpsTriple_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit1
  -- ---- init2 (base+60 → base+68)
  have hinit2_raw := divK_phaseB_init2_spec sp (base + 60) b1 b2 v6 v7
  simp only [phB_i2_8] at hinit2_raw
  have hinit2 := cpsTriple_extend_code (divK_phaseB_init2_code_sub_divCode base) hinit2_raw
  have hinit2f := cpsTriple_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit2
  have h12 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hinit1f hinit2f
  -- ---- Cascade step 0: ADDI x5=4 (base+68 → base+72)
  have haddi0_raw := addi_x0_spec_gen .x5 v5 4 (base + 68) (by nofun)
  simp only [phB_addi_4, signExtend12_4] at haddi0_raw
  have haddi0 := cpsTriple_extend_code (addi_x5_singleton_sub_divCode base) haddi0_raw
  have haddi0f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi0
  have h123 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 haddi0f
  -- ---- Cascade step 0: BNE x10 ntaken (base+72 → base+76, b3=0)
  have hbne0_raw := bne_spec_gen .x10 .x0 24 b3 (0 : Word) (base + 72)
  rw [show (base + 72 : Word) + signExtend13 24 = base + 96 from by
        rv64_addr, phB_bne_4] at hbne0_raw
  have hbne0_clean := cpsBranch_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _).mp h_rest).2)
  have hbne0 := cpsTriple_extend_code (bne_x10_singleton_sub_divCode base) hbne0_clean
  have hbne0f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne0
  have h1234 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hbne0f
  -- ---- Cascade step 1: ADDI x5=3 (base+76 → base+80)
  have haddi1_raw := addi_x0_spec_gen .x5 (4 : Word) 3 (base + 76) (by nofun)
  simp only [phB_step1_4, signExtend12_3] at haddi1_raw
  have haddi1 := cpsTriple_extend_code (addi_x5_3_sub_divCode base) haddi1_raw
  have haddi1f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi1
  have h12345 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234 haddi1f
  -- ---- Cascade step 1: BNE x7 ntaken (base+80 → base+84, b2=0)
  have hbne1_raw := bne_spec_gen .x7 .x0 16 b2 (0 : Word) (base + 80)
  rw [show (base + 80 : Word) + signExtend13 16 = base + 96 from by
        rv64_addr, phB_step1_8] at hbne1_raw
  have hbne1_clean := cpsBranch_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb2z ((sepConj_pure_right _).mp h_rest).2)
  have hbne1 := cpsTriple_extend_code (bne_x7_16_sub_divCode base) hbne1_clean
  have hbne1f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (3 : Word)) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne1
  have h123456 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345 hbne1f
  -- ---- Cascade step 2: ADDI x5=2 (base+84 → base+88)
  have haddi2_raw := addi_x0_spec_gen .x5 (3 : Word) 2 (base + 84) (by nofun)
  simp only [phB_step2_4, signExtend12_2] at haddi2_raw
  have haddi2 := cpsTriple_extend_code (addi_x5_2_sub_divCode base) haddi2_raw
  have haddi2f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) ** (.x6 ↦ᵣ b1) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi2
  have h1234567 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123456 haddi2f
  -- ---- Cascade step 2: BNE x6 taken (base+88 → base+96, b1≠0)
  have hbne2_raw := bne_spec_gen .x6 .x0 8 b1 (0 : Word) (base + 88)
  rw [show (base + 88 : Word) + signExtend13 8 = base + 96 from by
        rv64_addr, phB_step2_8] at hbne2_raw
  have hbne2_clean := cpsBranch_takenStripPure2 hbne2_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hb1nz)
  have hbne2 := cpsTriple_extend_code (bne_x6_8_sub_divCode base) hbne2_clean
  have hbne2f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne2
  have h12345678 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234567 hbne2f
  -- ---- Tail (base+96 → base+116)
  have htail_raw := divK_phaseB_tail_spec sp (2 : Word) b1 nMem (base + 96)
  simp only [divK_phaseB_tail_pre_unfold, divK_phaseB_tail_post_unfold,
             phB_t_20, divK_phaseB_n2_nm1_x8, signExtend12_32, phB_sp8_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_divCode base) htail_raw
  have htailf := cpsTriple_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)))
    (by pcFree) htail
  have hphaseB := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345678 htailf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hphaseB

-- ============================================================================
-- Section 10f: Phase B n=1 (b[3]=b[2]=b[1]=0)
-- init1 → init2 → ADDI x5=4 → BNE x10 ntaken → ADDI x5=3 → BNE x7 ntaken
-- → ADDI x5=2 → BNE x6 ntaken → ADDI x5=1 → tail
-- ============================================================================

/-- Phase B when b[3]=b[2]=b[1]=0 (n=1): zero scratch, cascade falls through all BNEs, load b[0].
    Execution: all 21 instructions of divK_phaseB.
    Exit at base+116. x5 = b[0] (leading limb), n = 1.
    Note: b[0] must be in precondition since the tail loads from sp+32. -/
theorem evm_div_phaseB_n1_spec (sp base : Word)
    (b0 b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0) :
    cpsTriple (base + phaseBOff) (base + clzOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) **
       ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (1 : Word))) := by
  -- ---- init1 (base+32 → base+60)
  have hinit1_raw := divK_phaseB_init1_spec sp (base + phaseBOff) q0 q1 q2 q3 u5 u6 u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_divCode base) hinit1_raw
  have hinit1f := cpsTriple_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit1
  -- ---- init2 (base+60 → base+68)
  have hinit2_raw := divK_phaseB_init2_spec sp (base + 60) b1 b2 v6 v7
  simp only [phB_i2_8] at hinit2_raw
  have hinit2 := cpsTriple_extend_code (divK_phaseB_init2_code_sub_divCode base) hinit2_raw
  have hinit2f := cpsTriple_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit2
  have h12 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hinit1f hinit2f
  -- ---- Cascade step 0: ADDI x5=4 (base+68 → base+72)
  have haddi0_raw := addi_x0_spec_gen .x5 v5 4 (base + 68) (by nofun)
  simp only [phB_addi_4, signExtend12_4] at haddi0_raw
  have haddi0 := cpsTriple_extend_code (addi_x5_singleton_sub_divCode base) haddi0_raw
  have haddi0f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi0
  have h123 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 haddi0f
  -- ---- Cascade step 0: BNE x10 ntaken (base+72 → base+76, b3=0)
  have hbne0_raw := bne_spec_gen .x10 .x0 24 b3 (0 : Word) (base + 72)
  rw [show (base + 72 : Word) + signExtend13 24 = base + 96 from by
        rv64_addr, phB_bne_4] at hbne0_raw
  have hbne0_clean := cpsBranch_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _).mp h_rest).2)
  have hbne0 := cpsTriple_extend_code (bne_x10_singleton_sub_divCode base) hbne0_clean
  have hbne0f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne0
  have h1234 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hbne0f
  -- ---- Cascade step 1: ADDI x5=3 (base+76 → base+80)
  have haddi1_raw := addi_x0_spec_gen .x5 (4 : Word) 3 (base + 76) (by nofun)
  simp only [phB_step1_4, signExtend12_3] at haddi1_raw
  have haddi1 := cpsTriple_extend_code (addi_x5_3_sub_divCode base) haddi1_raw
  have haddi1f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi1
  have h12345 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234 haddi1f
  -- ---- Cascade step 1: BNE x7 ntaken (base+80 → base+84, b2=0)
  have hbne1_raw := bne_spec_gen .x7 .x0 16 b2 (0 : Word) (base + 80)
  rw [show (base + 80 : Word) + signExtend13 16 = base + 96 from by
        rv64_addr, phB_step1_8] at hbne1_raw
  have hbne1_clean := cpsBranch_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb2z ((sepConj_pure_right _).mp h_rest).2)
  have hbne1 := cpsTriple_extend_code (bne_x7_16_sub_divCode base) hbne1_clean
  have hbne1f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (3 : Word)) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne1
  have h123456 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345 hbne1f
  -- ---- Cascade step 2: ADDI x5=2 (base+84 → base+88)
  have haddi2_raw := addi_x0_spec_gen .x5 (3 : Word) 2 (base + 84) (by nofun)
  simp only [phB_step2_4, signExtend12_2] at haddi2_raw
  have haddi2 := cpsTriple_extend_code (addi_x5_2_sub_divCode base) haddi2_raw
  have haddi2f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) ** (.x6 ↦ᵣ b1) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi2
  have h1234567 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123456 haddi2f
  -- ---- Cascade step 2: BNE x6 ntaken (base+88 → base+92, b1=0)
  have hbne2_raw := bne_spec_gen .x6 .x0 8 b1 (0 : Word) (base + 88)
  rw [show (base + 88 : Word) + signExtend13 8 = base + 96 from by
        rv64_addr, phB_step2_8] at hbne2_raw
  have hbne2_clean := cpsBranch_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb1z ((sepConj_pure_right _).mp h_rest).2)
  have hbne2 := cpsTriple_extend_code (bne_x6_8_sub_divCode base) hbne2_clean
  have hbne2f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne2
  have h12345678 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234567 hbne2f
  -- ---- Fallthrough: ADDI x5=1 (base+92 → base+96)
  have haddi3_raw := addi_x0_spec_gen .x5 (2 : Word) 1 (base + 92) (by nofun)
  simp only [phB_fall_4, signExtend12_1] at haddi3_raw
  have haddi3 := cpsTriple_extend_code (addi_x5_1_sub_divCode base) haddi3_raw
  have haddi3f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi3
  have h123456789 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345678 haddi3f
  -- ---- Tail (base+96 → base+116)
  have htail_raw := divK_phaseB_tail_spec sp (1 : Word) b0 nMem (base + 96)
  simp only [divK_phaseB_tail_pre_unfold, divK_phaseB_tail_post_unfold,
             phB_t_20, divK_phaseB_n1_nm1_x8, signExtend12_32, phB_sp0_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_divCode base) htail_raw
  have htailf := cpsTriple_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)))
    (by pcFree) htail
  have hphaseB := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123456789 htailf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hphaseB

end EvmAsm.Evm64
