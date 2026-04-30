/-
  EvmAsm.Evm64.DivMod.LoopBody.StoreLoop

  Extracted from `LoopBody.lean` (Sections 9b + 9c).

  `divK_store_loop_*_spec`: combined "store q[j] + ADDI j-1 + BGE" specs
  with the BGE branch eliminated based on the j-value (j=0: not-taken,
  j>0: taken). Both used by every `LoopBodyN{1..4}.lean`.

  Uses public helpers from `LoopBody.lean`:
  - `lb_sub`, `lb_sqj` (now public, made non-`private` for this split)
  - `divK_store_qj_spec` (re-exported via the LimbSpec.SubCarryStoreQj chain)
-/

import EvmAsm.Evm64.DivMod.LoopBody

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Section 9b: Store + loop exit for j=0 (cpsTripleWithin, BGE eliminated)
-- For j=0, j' = -1 < 0, so BGE is not taken → always exits to base+908.
-- ============================================================================

/-- For j=0, j' = signExtend12 4095, and slt j' 0 is true (j' < 0 signed). -/
private theorem j0_slt_zero :
    BitVec.slt ((0 : Word) + signExtend12 4095) 0 = true := by decide

/-- Store q[0] + loop exit at j=0. Since j' = -1 < 0, BGE is not taken,
    so this is a cpsTripleWithin (not cpsBranchWithin) to base+908. -/
theorem divK_store_loop_j0_spec_within
    (sp qHat v5Old v7Old qOld : Word)
    (base : Word) :
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    let j' := (0 : Word) + signExtend12 4095
    cpsTripleWithin 6 (base + storeLoopOff) (base + denormOff) (sharedDivModCode base)
      ((.x1 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ qOld))
      ((.x1 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ (0 : Word) <<< (3 : BitVec 6).toNat) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ qHat)) := by
  intro qAddr j'
  -- 1. Store q[j]: instrs [109]-[112] at base+884
  have SQ := divK_store_qj_spec_within sp (0 : Word) qHat v5Old v7Old qOld (base + storeLoopOff)
  dsimp only [] at SQ
  rw [lb_sqj] at SQ
  have SQe := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub 109 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 110 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 111 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub 112 _ _ (by decide) (by bv_addr) (by decide))))) SQ
  -- 2. ADDI x1 x1 4095 at base+900 (instr [113])
  have haddi := addi_spec_gen_same_within .x1 (0 : Word) 4095 (base + 900) (by nofun)
  rw [show (base + 900 : Word) + 4 = base + 904 from by bv_addr] at haddi
  have haddi_e := cpsTripleWithin_extend_code (hmono := by
    exact lb_sub 113 _ _ (by decide) (by bv_addr) (by decide)) haddi
  -- 3. BGE x1 x0 7736 at base+904 (instr [114])
  have hbge_raw := bge_spec_gen_within .x1 .x0 (7736 : BitVec 13) j' (0 : Word) (base + 904)
  rw [show (base + 904 : Word) + signExtend13 (7736 : BitVec 13) = base + loopBodyOff from by rv64_addr,
      show (base + 904 : Word) + 4 = base + denormOff from by bv_addr] at hbge_raw
  have hbge_ext := cpsBranchWithin_extend_code (hmono := by
    exact lb_sub 114 _ _ (by decide) (by bv_addr) (by decide)) hbge_raw
  -- 4. Eliminate taken branch: j' = -1 < 0, so BGE is not taken
  have hbge_exit_raw := cpsBranchWithin_ntakenPath hbge_ext
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
      exact hpure j0_slt_zero)
  -- Strip pure fact from not-taken postcondition
  have hbge_exit := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    hbge_exit_raw
  -- 5. Build store_qj + x0 frame → base+900
  have SQx0 : cpsTripleWithin 4 (base + storeLoopOff) (base + 900) (sharedDivModCode base)
      ((.x1 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ qOld))
      ((.x1 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ (0 : Word) <<< (3 : BitVec 6).toNat) ** (.x7 ↦ᵣ qAddr) **
       (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ qHat)) :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) SQe)
  -- 6. Frame ADDI with x0 (BGE needs x0), then frame both with remaining atoms
  have haddi_x0 := cpsTripleWithin_frameR
      (.x0 ↦ᵣ (0 : Word)) (by pcFree) haddi_e
  -- Compose ADDI+x0 → BGE exit (both have x1 ** x0)
  have addi_bge := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) haddi_x0 hbge_exit
  -- Frame with remaining atoms
  have addi_bge_framed := cpsTripleWithin_frameR
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ (0 : Word) <<< (3 : BitVec 6).toNat) ** (.x7 ↦ᵣ qAddr) **
       (qAddr ↦ₘ qHat))
      (by pcFree) addi_bge
  -- 7. Compose: store_qj → (ADDI → BGE exit)
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) SQx0 addi_bge_framed
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    full

/-- Store q[0] + loop exit at j=0. Since j' = -1 < 0, BGE is not taken,
    so this is a cpsTripleWithin (not cpsBranchWithin) to base+908. -/

theorem divK_store_loop_jgt0_spec_within
    (sp j qHat v5Old v7Old qOld : Word)
    (base : Word)
    (hj_pos : BitVec.slt (j + signExtend12 4095) 0 = false) :
    let jX8 := j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - jX8
    let j' := j + signExtend12 4095
    cpsTripleWithin 6 (base + storeLoopOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ qOld))
      ((.x1 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ jX8) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ qHat)) := by
  intro jX8 qAddr j'
  -- 1. Store q[j]: instrs [109]-[112] at base+884
  have SQ := divK_store_qj_spec_within sp j qHat v5Old v7Old qOld (base + storeLoopOff)
  dsimp only [] at SQ
  rw [lb_sqj] at SQ
  have SQe := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub 109 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 110 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 111 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub 112 _ _ (by decide) (by bv_addr) (by decide))))) SQ
  -- 2. ADDI x1 x1 4095 at base+900 (instr [113])
  have haddi := addi_spec_gen_same_within .x1 j 4095 (base + 900) (by nofun)
  rw [show (base + 900 : Word) + 4 = base + 904 from by bv_addr] at haddi
  have haddi_e := cpsTripleWithin_extend_code (hmono := by
    exact lb_sub 113 _ _ (by decide) (by bv_addr) (by decide)) haddi
  -- 3. BGE x1 x0 7736 at base+904 (instr [114])
  have hbge_raw := bge_spec_gen_within .x1 .x0 (7736 : BitVec 13) j' (0 : Word) (base + 904)
  rw [show (base + 904 : Word) + signExtend13 (7736 : BitVec 13) = base + loopBodyOff from by rv64_addr,
      show (base + 904 : Word) + 4 = base + denormOff from by bv_addr] at hbge_raw
  have hbge_ext := cpsBranchWithin_extend_code (hmono := by
    exact lb_sub 114 _ _ (by decide) (by bv_addr) (by decide)) hbge_raw
  -- 4. Eliminate not-taken branch: j' = j-1 ≥ 0, so BGE is taken
  have hbge_exit_raw := cpsBranchWithin_takenPath hbge_ext
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
      exact absurd hpure (by rw [hj_pos]; exact Bool.false_ne_true))
  -- Strip pure fact from taken postcondition
  have hbge_exit := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    hbge_exit_raw
  -- 5. Build store_qj + x0 frame → base+900
  have SQx0 : cpsTripleWithin 4 (base + storeLoopOff) (base + 900) (sharedDivModCode base)
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ qOld))
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ jX8) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ qHat)) :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) SQe)
  -- 6. Frame ADDI with x0, then frame both with remaining atoms
  have haddi_x0 := cpsTripleWithin_frameR
      (.x0 ↦ᵣ (0 : Word)) (by pcFree) haddi_e
  -- Compose ADDI+x0 → BGE exit (both have x1 ** x0)
  have addi_bge := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) haddi_x0 hbge_exit
  -- Frame with remaining atoms
  have addi_bge_framed := cpsTripleWithin_frameR
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ jX8) ** (.x7 ↦ᵣ qAddr) **
       (qAddr ↦ₘ qHat))
      (by pcFree) addi_bge
  -- 7. Compose: store_qj → (ADDI → BGE exit)
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) SQx0 addi_bge_framed
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    full

end EvmAsm.Evm64
