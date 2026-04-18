/-
  EvmAsm.Evm64.SignExtend.Compose

  Hierarchical composition of SIGNEXTEND CPS specs into full-program theorems.
  Composes the 6 execution paths through `evm_signextend` (48 instructions, 192 bytes):
  - No-change path 1 (high limbs nonzero): Phase A BNE taken → done
  - No-change path 2 (b[0] >= 31): Phase A BEQ taken → done
  - Body L (L=0..3, b < 31): Phase A ntaken → B → C(exit L) → body_L → done → exit
-/

import EvmAsm.Evm64.SignExtend.LimbSpec
import EvmAsm.Evm64.EvmWordArith
import EvmAsm.Rv64.AddrNorm

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se13_24 se13_60 se13_100 se13_156 se13_168 se21_36 se21_68 se21_96)

-- ============================================================================
-- Section 1: signextCode definition and helpers
-- ============================================================================

/-- The full evm_signextend code as a single CodeReq.ofProg block (48 instructions). -/
abbrev signextCode (base : Word) : CodeReq := CodeReq.ofProg base evm_signextend

-- `regIs_to_regOwn` lives in `Rv64/SepLogic.lean` (shared with the
-- Byte / Shift / SignExtend opcode files).

/-- If each half of a CodeReq union is subsumed by target, so is the union. -/
private theorem CodeReq_union_sub_both {cr1 cr2 target : CodeReq}
    (h1 : ∀ a i, cr1 a = some i → target a = some i)
    (h2 : ∀ a i, cr2 a = some i → target a = some i) :
    ∀ a i, (cr1.union cr2) a = some i → target a = some i := by
  intro a i h
  simp only [CodeReq.union] at h
  cases h1a : cr1 a with
  | none => simp [h1a] at h; exact h2 a i h
  | some v => simp [h1a] at h; subst h; exact h1 a v h1a

/-- A singleton at instruction k of evm_signextend is subsumed by signextCode. -/
private theorem singleton_sub_signextCode (base addr : Word) (instr : Instr) (k : Nat)
    (hk : k < evm_signextend.length)
    (h_addr : addr = base + BitVec.ofNat 64 (4 * k))
    (h_instr : evm_signextend.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i → signextCode base a = some i :=
  CodeReq.singleton_mono (h_instr ▸ CodeReq.ofProg_lookup_addr base evm_signextend k addr hk
    (by decide) h_addr)

-- ============================================================================
-- Section 2: Subsumption lemmas
-- ============================================================================

/-- Phase A code (union chain, 9 instrs at +0) is subsumed by signextCode. -/
private theorem phase_a_sub_signextCode (base : Word) :
    ∀ a i, signext_phase_a_code base a = some i → signextCode base a = some i := by
  unfold signext_phase_a_code
  apply CodeReq_union_sub_both
  · exact singleton_sub_signextCode base base (.LD .x5 .x12 8) 0
      (by decide) (by bv_omega) (by decide)
  · apply CodeReq_union_sub_both
    · unfold signext_ld_or_acc_code
      exact CodeReq.ofProg_mono_sub base (base + 4) evm_signextend (signext_ld_or_acc_prog 16) 1
        (by bv_omega) (by decide) (by decide) (by decide)
    · apply CodeReq_union_sub_both
      · unfold signext_ld_or_acc_code
        exact CodeReq.ofProg_mono_sub base (base + 12) evm_signextend (signext_ld_or_acc_prog 24) 3
          (by bv_omega) (by decide) (by decide) (by decide)
      · apply CodeReq_union_sub_both
        · exact singleton_sub_signextCode base (base + 20) (.BNE .x5 .x0 168) 5
            (by decide) (by bv_omega) (by decide)
        · apply CodeReq_union_sub_both
          · exact singleton_sub_signextCode base (base + 24) (.LD .x5 .x12 0) 6
              (by decide) (by bv_omega) (by decide)
          · apply CodeReq_union_sub_both
            · exact singleton_sub_signextCode base (base + 28) (.SLTIU .x10 .x5 31) 7
                (by decide) (by bv_omega) (by decide)
            · exact singleton_sub_signextCode base (base + 32) (.BEQ .x10 .x0 156) 8
                (by decide) (by bv_omega) (by decide)

/-- Phase B code (ofProg, 5 instrs at +36) is subsumed by signextCode. -/
private theorem phase_b_sub_signextCode (base : Word) :
    ∀ a i, signext_phase_b_code (base + 36) a = some i → signextCode base a = some i := by
  unfold signext_phase_b_code
  exact CodeReq.ofProg_mono_sub base (base + 36) evm_signextend signext_phase_b 9
    (by bv_omega) (by decide) (by decide) (by decide)

private theorem cascade_15_sub_signextCode (base : Word) :
    ∀ a i, CodeReq.ofProg (base + 60) (signext_cascade_step_prog 1 60) a = some i → signextCode base a = some i :=
  CodeReq.ofProg_mono_sub base (base + 60) evm_signextend (signext_cascade_step_prog 1 60) 15
    (by bv_omega) (by decide) (by decide) (by decide)

private theorem cascade_17_sub_signextCode (base : Word) :
    ∀ a i, CodeReq.ofProg (base + 68) (signext_cascade_step_prog 2 24) a = some i → signextCode base a = some i :=
  CodeReq.ofProg_mono_sub base (base + 68) evm_signextend (signext_cascade_step_prog 2 24) 17
    (by bv_omega) (by decide) (by decide) (by decide)

/-- Phase C code (union chain, 5 instrs at +56) is subsumed by signextCode. -/
private theorem phase_c_sub_signextCode (base : Word) :
    ∀ a i, signext_phase_c_code (base + 56) a = some i → signextCode base a = some i := by
  unfold signext_phase_c_code
  apply CodeReq_union_sub_both
  · exact singleton_sub_signextCode base (base + 56) (.BEQ .x5 .x0 100) 14
      (by decide) (by bv_omega) (by decide)
  · apply CodeReq_union_sub_both
    · unfold signext_cascade_step_code
      have : (base + 56 : Word) + 4 = base + 60 := by bv_omega
      rw [this]
      exact cascade_15_sub_signextCode base
    · unfold signext_cascade_step_code
      have : (base + 56 : Word) + 12 = base + 68 := by bv_omega
      rw [this]
      exact cascade_17_sub_signextCode base

/-- Body 3 code (ofProg, 5 instrs at +76) is subsumed by signextCode. -/
private theorem body_3_sub_signextCode (base : Word) :
    ∀ a i, signext_body_3_code (base + 76) 96 a = some i → signextCode base a = some i := by
  unfold signext_body_3_code
  exact CodeReq.ofProg_mono_sub base (base + 76) evm_signextend (signext_body_3_prog 96) 19
    (by bv_omega) (by decide) (by decide) (by decide)

/-- Body 2 code (ofProg, 7 instrs at +96) is subsumed by signextCode. -/
private theorem body_2_sub_signextCode (base : Word) :
    ∀ a i, signext_body_2_code (base + 96) 68 a = some i → signextCode base a = some i := by
  unfold signext_body_2_code
  exact CodeReq.ofProg_mono_sub base (base + 96) evm_signextend (signext_body_2_prog 68) 24
    (by bv_omega) (by decide) (by decide) (by decide)

/-- Body 1 code (ofProg, 8 instrs at +124) is subsumed by signextCode. -/
private theorem body_1_sub_signextCode (base : Word) :
    ∀ a i, signext_body_1_code (base + 124) 36 a = some i → signextCode base a = some i := by
  unfold signext_body_1_code
  exact CodeReq.ofProg_mono_sub base (base + 124) evm_signextend (signext_body_1_prog 36) 31
    (by bv_omega) (by decide) (by decide) (by decide)

/-- Body 0 code (ofProg, 8 instrs at +156) is subsumed by signextCode. -/
private theorem body_0_sub_signextCode (base : Word) :
    ∀ a i, signext_body_0_code (base + 156) a = some i → signextCode base a = some i := by
  unfold signext_body_0_code
  exact CodeReq.ofProg_mono_sub base (base + 156) evm_signextend signext_body_0 39
    (by bv_omega) (by decide) (by decide) (by decide)

/-- Done code (singleton, 1 instr at +188) is subsumed by signextCode. -/
private theorem done_sub_signextCode (base : Word) :
    ∀ a i, CodeReq.singleton (base + 188) (.ADDI .x12 .x12 32) a = some i → signextCode base a = some i :=
  singleton_sub_signextCode base (base + 188) (.ADDI .x12 .x12 32) 47
    (by decide) (by bv_omega) (by decide)

-- Individual instruction subsumption helpers (for Phase A raw composition)

private theorem ld_b1_sub_signextCode (base : Word) :
    ∀ a i, CodeReq.singleton base (.LD .x5 .x12 8) a = some i → signextCode base a = some i :=
  singleton_sub_signextCode base base (.LD .x5 .x12 8) 0
    (by decide) (by bv_omega) (by decide)

private theorem ld_or_16_sub_signextCode (base : Word) :
    ∀ a i, signext_ld_or_acc_code 16 (base + 4) a = some i → signextCode base a = some i := by
  unfold signext_ld_or_acc_code
  exact CodeReq.ofProg_mono_sub base (base + 4) evm_signextend (signext_ld_or_acc_prog 16) 1
    (by bv_omega) (by decide) (by decide) (by decide)

private theorem ld_or_24_sub_signextCode (base : Word) :
    ∀ a i, signext_ld_or_acc_code 24 (base + 12) a = some i → signextCode base a = some i := by
  unfold signext_ld_or_acc_code
  exact CodeReq.ofProg_mono_sub base (base + 12) evm_signextend (signext_ld_or_acc_prog 24) 3
    (by bv_omega) (by decide) (by decide) (by decide)

private theorem bne_sub_signextCode (base : Word) :
    ∀ a i, CodeReq.singleton (base + 20) (.BNE .x5 .x0 168) a = some i → signextCode base a = some i :=
  singleton_sub_signextCode base (base + 20) (.BNE .x5 .x0 168) 5
    (by decide) (by bv_omega) (by decide)

private theorem ld_b0_sub_signextCode (base : Word) :
    ∀ a i, CodeReq.singleton (base + 24) (.LD .x5 .x12 0) a = some i → signextCode base a = some i :=
  singleton_sub_signextCode base (base + 24) (.LD .x5 .x12 0) 6
    (by decide) (by bv_omega) (by decide)

private theorem sltiu_sub_signextCode (base : Word) :
    ∀ a i, CodeReq.singleton (base + 28) (.SLTIU .x10 .x5 31) a = some i → signextCode base a = some i :=
  singleton_sub_signextCode base (base + 28) (.SLTIU .x10 .x5 31) 7
    (by decide) (by bv_omega) (by decide)

private theorem beq_sub_signextCode (base : Word) :
    ∀ a i, CodeReq.singleton (base + 32) (.BEQ .x10 .x0 156) a = some i → signextCode base a = some i :=
  singleton_sub_signextCode base (base + 32) (.BEQ .x10 .x0 156) 8
    (by decide) (by bv_omega) (by decide)

-- ============================================================================
-- Section 3: Address normalization lemmas
-- ============================================================================

private theorem se_off_4 (base : Word) : (base + 4 : Word) + 8 = base + 12 := by bv_omega
private theorem se_off_12 (base : Word) : (base + 12 : Word) + 8 = base + 20 := by bv_omega
private theorem se_off_20 (base : Word) : (base + 20 : Word) + 4 = base + 24 := by bv_omega
private theorem se_off_24 (base : Word) : (base + 24 : Word) + 4 = base + 28 := by bv_omega
private theorem se_off_28 (base : Word) : (base + 28 : Word) + 4 = base + 32 := by bv_omega
private theorem se_off_32 (base : Word) : (base + 32 : Word) + 4 = base + 36 := by bv_omega
private theorem se_bne_target (base : Word) : (base + 20 : Word) + signExtend13 168 = base + 188 := by
  rw [se13_168]; bv_omega
private theorem se_beq_target (base : Word) : (base + 32 : Word) + signExtend13 156 = base + 188 := by
  rw [se13_156]; bv_omega
-- Phase C exit addresses
private theorem se_c_e0 (base : Word) : (base + 56 : Word) + signExtend13 100 = base + 156 := by
  rw [se13_100]; bv_omega
private theorem se_c_e1 (base : Word) : ((base + 56 : Word) + 8) + signExtend13 60 = base + 124 := by
  rw [se13_60]; bv_omega
private theorem se_c_e2 (base : Word) : ((base + 56 : Word) + 16) + signExtend13 24 = base + 96 := by
  rw [se13_24]; bv_omega
private theorem se_c_e3 (base : Word) : (base + 56 : Word) + 20 = base + 76 := by bv_omega
-- Body exit addresses (JAL targets)
private theorem se_body3_exit (base : Word) : ((base + 76 : Word) + 16) + signExtend21 96 = base + 188 := by
  rw [se21_96]; bv_omega
private theorem se_body2_exit (base : Word) : ((base + 96 : Word) + 24) + signExtend21 68 = base + 188 := by
  rw [se21_68]; bv_omega
private theorem se_body1_exit (base : Word) : ((base + 124 : Word) + 28) + signExtend21 36 = base + 188 := by
  rw [se21_36]; bv_omega
private theorem se_done_exit (base : Word) : (base + 188 : Word) + 4 = base + 192 := by bv_omega

-- ============================================================================
-- Section 4: No-change path 1 — high limbs nonzero
-- ============================================================================

/-- No-change path via BNE taken: high b limbs are nonzero → b >= 31 → x unchanged.
    Execution: LD b1 → LD/OR b2 → LD/OR b3 → BNE(taken) → done. -/
theorem signext_nochange_high_spec (sp base : Word)
    (b0 b1 b2 b3 v0 v1 v2 v3 r5 r10 : Word)
    (hhigh : b1 ||| b2 ||| b3 ≠ 0) :
    cpsTriple base (base + 192) (signextCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) := by
  -- Step 1: LD x5 x12 8 at base → extend to signextCode
  have h1 := cpsTriple_extend_code (ld_b1_sub_signextCode base)
    (ld_spec_gen .x5 .x12 sp r5 b1 8 base (by nofun))
  simp only [signExtend12_8] at h1
  -- Step 2: LD/OR at base+4
  have h2 := cpsTriple_extend_code (ld_or_16_sub_signextCode base)
    (signext_ld_or_acc_spec sp b1 r10 b2 16 (base + 4))
  simp only [signExtend12_16] at h2
  rw [se_off_4] at h2
  -- Step 3: LD/OR at base+12
  have h3 := cpsTriple_extend_code (ld_or_24_sub_signextCode base)
    (signext_ld_or_acc_spec sp (b1 ||| b2) b2 b3 24 (base + 12))
  simp only [signExtend12_24] at h3
  rw [se_off_12] at h3
  -- Frame + compose linear chain
  have h1f := cpsTriple_frame_left base (base + 4) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
     (sp ↦ₘ b0) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h1
  have h2f := cpsTriple_frame_left (base + 4) (base + 12) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h2
  have h12 := cpsTriple_seq_with_perm_same_cr base (base + 4) (base + 12) _
    _ _ _ _
    (fun h hp => by xperm_hyp hp) h1f h2f
  have h3f := cpsTriple_frame_left (base + 12) (base + 20) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h3
  have h123 := cpsTriple_seq_with_perm_same_cr base (base + 12) (base + 20) _
    _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 h3f
  -- Step 4: BNE at base+20 → extend, eliminate ntaken
  have hbne_raw := bne_spec_gen .x5 .x0 168 (b1 ||| b2 ||| b3) (0 : Word) (base + 20)
  rw [se_bne_target, se_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code (bne_sub_signextCode base) hbne_raw
  have hbne_taken := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hhigh)
  -- Frame BNE
  have hbne_framed := cpsTriple_frame_left (base + 20) (base + 188) _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbne_taken
  -- Compose → BNE
  have hAB := cpsTriple_seq_with_perm_same_cr base (base + 20) (base + 188) _
    _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hbne_framed
  -- Step 5: Done (base+188 → base+192) → extend
  have hdone := cpsTriple_extend_code (done_sub_signextCode base)
    (signext_done_spec sp (base + 188))
  rw [se_done_exit] at hdone
  have hdone_framed := cpsTriple_frame_left (base + 188) (base + 192) _ _ _
    ((.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ b3) **
     (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hdone
  have hfull := cpsTriple_seq_with_perm_same_cr base (base + 188) (base + 192) _
    _ _ _ _
    (fun h hp => by xperm_hyp hp) hAB hdone_framed
  -- Final: weaken regs to regOwn + perm
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      simp only [signExtend12_32] at hq
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
           ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
         ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
        from by xperm) h).mp w1)
    hfull

/-- No-change path via BEQ taken: b1=b2=b3=0 but b[0] >= 31 → x unchanged.
    Execution: LD b1 → LD/OR b2 → LD/OR b3 → BNE(ntaken) → LD b0 → SLTIU → BEQ(taken) → done. -/
theorem signext_nochange_geq31_spec (sp base : Word)
    (b0 b1 b2 b3 v0 v1 v2 v3 r5 r10 : Word)
    (hlow : b1 ||| b2 ||| b3 = 0)
    (hlarge : BitVec.ult b0 (signExtend12 (31 : BitVec 12)) = false) :
    cpsTriple base (base + 192) (signextCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) := by
  -- Steps 1-3: Same linear chain
  have h1 := cpsTriple_extend_code (ld_b1_sub_signextCode base)
    (ld_spec_gen .x5 .x12 sp r5 b1 8 base (by nofun))
  simp only [signExtend12_8] at h1
  have h2 := cpsTriple_extend_code (ld_or_16_sub_signextCode base)
    (signext_ld_or_acc_spec sp b1 r10 b2 16 (base + 4))
  simp only [signExtend12_16] at h2; rw [se_off_4] at h2
  have h3 := cpsTriple_extend_code (ld_or_24_sub_signextCode base)
    (signext_ld_or_acc_spec sp (b1 ||| b2) b2 b3 24 (base + 12))
  simp only [signExtend12_24] at h3; rw [se_off_12] at h3
  have h1f := cpsTriple_frame_left base (base + 4) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
     (sp ↦ₘ b0) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h1
  have h2f := cpsTriple_frame_left (base + 4) (base + 12) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h2
  have h12 := cpsTriple_seq_with_perm_same_cr base (base + 4) (base + 12) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1f h2f
  have h3f := cpsTriple_frame_left (base + 12) (base + 20) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h3
  have h123 := cpsTriple_seq_with_perm_same_cr base (base + 12) (base + 20) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 h3f
  -- Step 4: BNE at base+20 → eliminate TAKEN (b1|||b2|||b3 = 0)
  have hbne_raw := bne_spec_gen .x5 .x0 168 (b1 ||| b2 ||| b3) (0 : Word) (base + 20)
  rw [se_bne_target, se_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code (bne_sub_signextCode base) hbne_raw
  have hbne_ntaken := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _ _ _).mp h_rest).2 hlow)
  have hbne_framed := cpsTriple_frame_left (base + 20) (base + 24) _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbne_ntaken
  have h1234 := cpsTriple_seq_with_perm_same_cr base (base + 20) (base + 24) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hbne_framed
  -- Step 5: LD x5 x12 0 at base+24
  have hld_raw := ld_spec_gen .x5 .x12 sp (b1 ||| b2 ||| b3) b0 0 (base + 24) (by nofun)
  simp only [signExtend12_0] at hld_raw
  rw [show sp + (0 : Word) = sp from by bv_omega, se_off_24] at hld_raw
  have hld := cpsTriple_extend_code (ld_b0_sub_signextCode base) hld_raw
  -- Step 6: SLTIU at base+28
  have hsltiu_raw := sltiu_spec_gen .x10 .x5 b3 b0 31 (base + 28) (by nofun)
  rw [se_off_28] at hsltiu_raw
  have hsltiu := cpsTriple_extend_code (sltiu_sub_signextCode base) hsltiu_raw
  have hld_f := cpsTriple_frame_left (base + 24) (base + 28) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ b3) **
     ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hld
  have hsltiu_f := cpsTriple_frame_left (base + 28) (base + 32) _ _ _
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hsltiu
  have h56 := cpsTriple_seq_with_perm_same_cr (base + 24) (base + 28) (base + 32) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hld_f hsltiu_f
  have h123456 := cpsTriple_seq_with_perm_same_cr base (base + 24) (base + 32) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234 h56
  -- Step 7: BEQ at base+32 → eliminate ntaken (sltiu_val = 0 since b0 >= 31)
  let sltiu_val := (if BitVec.ult b0 (signExtend12 (31 : BitVec 12)) then (1 : Word) else (0 : Word))
  have hbeq_raw := beq_spec_gen .x10 .x0 156 sltiu_val (0 : Word) (base + 32)
  rw [se_beq_target, se_off_32] at hbeq_raw
  have hbeq := cpsBranch_extend_code (beq_sub_signextCode base) hbeq_raw
  have hsltiu_eq : sltiu_val = (0 : Word) := by
    simp only [sltiu_val, hlarge]; decide
  have hbeq_taken := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbeq
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact ((sepConj_pure_right _ _ _).mp h_rest).2 hsltiu_eq)
  have hbeq_framed := cpsTriple_frame_left (base + 32) (base + 188) _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) **
     (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbeq_taken
  have h1234567 := cpsTriple_seq_with_perm_same_cr base (base + 32) (base + 188) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123456 hbeq_framed
  -- Step 8: Done (base+188 → base+192)
  have hdone := cpsTriple_extend_code (done_sub_signextCode base)
    (signext_done_spec sp (base + 188))
  rw [se_done_exit] at hdone
  have hdone_framed := cpsTriple_frame_left (base + 188) (base + 192) _ _ _
    ((.x5 ↦ᵣ b0) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ sltiu_val) **
     (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hdone
  have hfull := cpsTriple_seq_with_perm_same_cr base (base + 188) (base + 192) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234567 hdone_framed
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      simp only [signExtend12_32] at hq
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ b0) ** (.x10 ↦ᵣ sltiu_val) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
           ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
         ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
        from by xperm) h).mp w1)
    hfull

-- ============================================================================
-- Section 5: Body path helpers
-- ============================================================================

/-- Strip a pure fact from a cpsTriple's precondition and use it
    to convert the postcondition. -/
private theorem cpsTriple_strip_pure_and_convert
    {entry exit_ : Word} {cr : CodeReq}
    {P Q Q' : Assertion} {fact : Prop}
    (hbody : cpsTriple entry exit_ cr P Q)
    (hpost : fact → ∀ h, Q h → Q' h) :
    cpsTriple entry exit_ cr (P ** ⌜fact⌝) Q' := by
  intro R hR s hcr hPFR hpc
  have hfact : fact := by
    obtain ⟨hp, _, hpq⟩ := hPFR
    obtain ⟨h1, _, _, _, hPF, _⟩ := hpq
    exact ((sepConj_pure_right P fact h1).1 hPF).2
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hPFR
    exact ⟨hp, hcompat, by
      obtain ⟨h1, h2, hd, hunion, hPF, hR_⟩ := hpq
      exact ⟨h1, h2, hd, hunion, ((sepConj_pure_right P fact h1).1 hPF).1, hR_⟩⟩
  obtain ⟨k, s', hstep, hpc', hQR⟩ := hbody R hR s hcr hPR hpc
  exact ⟨k, s', hstep, hpc', by
    obtain ⟨hp', hcompat', hpq'⟩ := hQR
    exact ⟨hp', hcompat', sepConj_mono_left (hpost hfact) hp' hpq'⟩⟩

-- `cpsNBranch_extend_code` and `cpsNBranch_frame_left` live in
-- `Rv64/CPSSpec.lean` (shared across Evm64 opcode compositions).

-- ============================================================================
-- Section 6: Body path composition (b < 31)
-- ============================================================================

/-- Body path: b < 31 → raw-limb cpsTriple producing `signextend b x` limbs.
    Composes Phase A ntaken → B → C → body_L → done. -/
theorem signext_body_spec (sp base : Word)
    (b x : EvmWord) (r5 r6 r10 : Word)
    (hhigh : b.getLimb 1 ||| b.getLimb 2 ||| b.getLimb 3 = 0)
    (hsmall : BitVec.ult (b.getLimb 0) (signExtend12 (31 : BitVec 12)) = true) :
    cpsTriple base (base + 192) (signextCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ b.getLimb 0) ** ((sp + 8) ↦ₘ b.getLimb 1) **
       ((sp + 16) ↦ₘ b.getLimb 2) ** ((sp + 24) ↦ₘ b.getLimb 3) **
       ((sp + 32) ↦ₘ x.getLimb 0) ** ((sp + 40) ↦ₘ x.getLimb 1) **
       ((sp + 48) ↦ₘ x.getLimb 2) ** ((sp + 56) ↦ₘ x.getLimb 3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ b.getLimb 0) ** ((sp + 8) ↦ₘ b.getLimb 1) **
       ((sp + 16) ↦ₘ b.getLimb 2) ** ((sp + 24) ↦ₘ b.getLimb 3) **
       ((sp + 32) ↦ₘ (EvmWord.signextend b x).getLimb 0) **
       ((sp + 40) ↦ₘ (EvmWord.signextend b x).getLimb 1) **
       ((sp + 48) ↦ₘ (EvmWord.signextend b x).getLimb 2) **
       ((sp + 56) ↦ₘ (EvmWord.signextend b x).getLimb 3)) := by
  set b0 := b.getLimb 0; set b1 := b.getLimb 1
  set b2 := b.getLimb 2; set b3 := b.getLimb 3
  set v0 := x.getLimb 0; set v1 := x.getLimb 1
  set v2 := x.getLimb 2; set v3 := x.getLimb 3
  -- Phase A: base → base+36 (same as no-change geq31 path but BEQ ntaken)
  have h1 := cpsTriple_extend_code (ld_b1_sub_signextCode base)
    (ld_spec_gen .x5 .x12 sp r5 b1 8 base (by nofun))
  simp only [signExtend12_8] at h1
  have h2 := cpsTriple_extend_code (ld_or_16_sub_signextCode base)
    (signext_ld_or_acc_spec sp b1 r10 b2 16 (base + 4))
  simp only [signExtend12_16] at h2; rw [se_off_4] at h2
  have h3 := cpsTriple_extend_code (ld_or_24_sub_signextCode base)
    (signext_ld_or_acc_spec sp (b1 ||| b2) b2 b3 24 (base + 12))
  simp only [signExtend12_24] at h3; rw [se_off_12] at h3
  have h1f := cpsTriple_frame_left base (base + 4) _ _ _
    ((.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) ** (sp ↦ₘ b0) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) (by pcFree) h1
  have h2f := cpsTriple_frame_left (base + 4) (base + 12) _ _ _
    ((.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) (by pcFree) h2
  have h12 := cpsTriple_seq_with_perm_same_cr base (base + 4) (base + 12) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1f h2f
  have h3f := cpsTriple_frame_left (base + 12) (base + 20) _ _ _
    ((.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) (by pcFree) h3
  have h123 := cpsTriple_seq_with_perm_same_cr base (base + 12) (base + 20) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 h3f
  -- BNE ntaken
  have hbne_raw := bne_spec_gen .x5 .x0 168 (b1 ||| b2 ||| b3) (0 : Word) (base + 20)
  rw [se_bne_target, se_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code (bne_sub_signextCode base) hbne_raw
  have hbne_nt := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne
    (fun hp hQt => by obtain ⟨_, _, _, _, _, h_rest⟩ := hQt; exact ((sepConj_pure_right _ _ _).mp h_rest).2 hhigh)
  have hbne_f := cpsTriple_frame_left (base + 20) (base + 24) _ _ _
    ((.x6 ↦ᵣ r6) ** (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) (by pcFree) hbne_nt
  have h1234 := cpsTriple_seq_with_perm_same_cr base (base + 20) (base + 24) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hbne_f
  -- LD b0
  have hld_raw := ld_spec_gen .x5 .x12 sp (b1 ||| b2 ||| b3) b0 0 (base + 24) (by nofun)
  simp only [signExtend12_0] at hld_raw; rw [show sp + (0 : Word) = sp from by bv_omega, se_off_24] at hld_raw
  have hld := cpsTriple_extend_code (ld_b0_sub_signextCode base) hld_raw
  -- SLTIU
  have hsltiu_raw := sltiu_spec_gen .x10 .x5 b3 b0 31 (base + 28) (by nofun)
  rw [se_off_28] at hsltiu_raw
  have hsltiu := cpsTriple_extend_code (sltiu_sub_signextCode base) hsltiu_raw
  have hld_f := cpsTriple_frame_left (base + 24) (base + 28) _ _ _
    ((.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ b3) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) (by pcFree) hld
  have hsltiu_f := cpsTriple_frame_left (base + 28) (base + 32) _ _ _
    ((.x6 ↦ᵣ r6) ** (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) (by pcFree) hsltiu
  have h56 := cpsTriple_seq_with_perm_same_cr (base + 24) (base + 28) (base + 32) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hld_f hsltiu_f
  have h123456 := cpsTriple_seq_with_perm_same_cr base (base + 24) (base + 32) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234 h56
  -- BEQ ntaken (sltiu_val = 1 since b0 < 31)
  let sltiu_val := (if BitVec.ult b0 (signExtend12 (31 : BitVec 12)) then (1 : Word) else (0 : Word))
  have hsltiu_eq : sltiu_val = (1 : Word) := by simp only [sltiu_val, hsmall]; decide
  have hbeq_raw := beq_spec_gen .x10 .x0 156 sltiu_val (0 : Word) (base + 32)
  rw [se_beq_target, se_off_32] at hbeq_raw
  have hbeq := cpsBranch_extend_code (beq_sub_signextCode base) hbeq_raw
  have hbeq_nt := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbeq
    (fun hp hQt => by obtain ⟨_, _, _, _, _, h_rest⟩ := hQt; have := ((sepConj_pure_right _ _ _).mp h_rest).2; simp [hsltiu_eq] at this)
  have hbeq_f := cpsTriple_frame_left (base + 32) (base + 36) _ _ _
    ((.x6 ↦ᵣ r6) ** (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) ** (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) (by pcFree) hbeq_nt
  have hphaseA := cpsTriple_seq_with_perm_same_cr base (base + 32) (base + 36) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123456 hbeq_f
  -- Phase B: base+36 → base+56
  let byte_in_limb := b0 &&& signExtend12 (7 : BitVec 12)
  let byte_shift := byte_in_limb <<< (3 : BitVec 6).toNat
  let shift_amount := (56 : Word) - byte_shift
  let limb_idx := b0 >>> (3 : BitVec 6).toNat
  have hphaseB := cpsTriple_extend_code (phase_b_sub_signextCode base)
    (signext_phase_b_spec b0 r6 sltiu_val (base + 36))
  rw [show (base + 36 : Word) + 20 = base + 56 from by bv_omega] at hphaseB
  have hphaseB_f := cpsTriple_frame_left (base + 36) (base + 56) _ _ _
    ((.x12 ↦ᵣ sp) ** (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) (by pcFree) hphaseB
  have hphaseAB := cpsTriple_seq_with_perm_same_cr base (base + 36) (base + 56) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hphaseA hphaseB_f
  -- Phase C with pure dispatch facts
  have hphaseC_raw := signext_phase_c_spec_pure limb_idx byte_shift (base + 56)
    (base + 156) (base + 124) (base + 96) (base + 76)
    (se_c_e0 base) (se_c_e1 base) (se_c_e2 base) (se_c_e3 base)
  have hphaseC := cpsNBranch_extend_code (phase_c_sub_signextCode base) hphaseC_raw
  -- Body specs + done, extended to signextCode
  have hbody3 := cpsTriple_extend_code (body_3_sub_signextCode base)
    (signext_body_3_spec sp limb_idx shift_amount v3 (base + 76) (base + 188) 96 (se_body3_exit base))
  have hbody2 := cpsTriple_extend_code (body_2_sub_signextCode base)
    (signext_body_2_spec sp limb_idx ((0 : Word) + signExtend12 2) shift_amount v2 v3 (base + 96) (base + 188) 68 (se_body2_exit base))
  have hbody1 := cpsTriple_extend_code (body_1_sub_signextCode base)
    (signext_body_1_spec sp limb_idx ((0 : Word) + signExtend12 1) shift_amount v1 v2 v3 (base + 124) (base + 188) 36 (se_body1_exit base))
  have hbody0 := cpsTriple_extend_code (body_0_sub_signextCode base)
    (signext_body_0_spec sp limb_idx byte_shift shift_amount v0 v1 v2 v3 (base + 156))
  rw [show (base + 156 : Word) + 32 = base + 188 from by bv_omega] at hbody0
  have hdone := cpsTriple_extend_code (done_sub_signextCode base) (signext_done_spec sp (base + 188))
  rw [se_done_exit] at hdone
  -- Frame bodies with b-mem + x0
  let bmem := (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3)
  have hbody3_f := cpsTriple_frame_left _ _ _ _ _ ((.x0 ↦ᵣ (0 : Word)) ** bmem **
    ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2)) (by pcFree) hbody3
  have hbody2_f := cpsTriple_frame_left _ _ _ _ _ ((.x0 ↦ᵣ (0 : Word)) ** bmem **
    ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1)) (by pcFree) hbody2
  have hbody1_f := cpsTriple_frame_left _ _ _ _ _ ((.x0 ↦ᵣ (0 : Word)) ** bmem **
    ((sp + 32) ↦ₘ v0)) (by pcFree) hbody1
  have hbody0_f := cpsTriple_frame_left _ _ _ _ _ ((.x0 ↦ᵣ (0 : Word)) ** bmem) (by pcFree) hbody0
  -- Compose each body with done (body: base+X → base+188, done: base+188 → base+192)
  -- Body 3 + done
  have hdone3_f := cpsTriple_frame_left (base + 188) (base + 192) _ _ _
    ((.x5 ↦ᵣ (BitVec.sshiftRight (v3 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64))) **
     (.x6 ↦ᵣ shift_amount) **
     (.x0 ↦ᵣ (0 : Word)) ** bmem **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) **
     ((sp + 56) ↦ₘ (BitVec.sshiftRight (v3 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64))))
    (by pcFree) hdone
  have hbd3 := cpsTriple_seq_with_perm_same_cr (base + 76) (base + 188) (base + 192) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody3_f hdone3_f
  -- Body 2 + done
  have hdone2_f := cpsTriple_frame_left (base + 188) (base + 192) _ _ _
    ((.x5 ↦ᵣ (BitVec.sshiftRight (v2 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64))) **
     (.x6 ↦ᵣ shift_amount) **
     (.x10 ↦ᵣ (BitVec.sshiftRight (BitVec.sshiftRight (v2 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)) **
     (.x0 ↦ᵣ (0 : Word)) ** bmem **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) **
     ((sp + 48) ↦ₘ (BitVec.sshiftRight (v2 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64))) **
     ((sp + 56) ↦ₘ (BitVec.sshiftRight (BitVec.sshiftRight (v2 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)))
    (by pcFree) hdone
  have hbd2 := cpsTriple_seq_with_perm_same_cr (base + 96) (base + 188) (base + 192) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody2_f hdone2_f
  -- Body 1 + done
  have hdone1_f := cpsTriple_frame_left (base + 188) (base + 192) _ _ _
    ((.x5 ↦ᵣ (BitVec.sshiftRight (v1 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64))) **
     (.x6 ↦ᵣ shift_amount) **
     (.x10 ↦ᵣ (BitVec.sshiftRight (BitVec.sshiftRight (v1 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)) **
     (.x0 ↦ᵣ (0 : Word)) ** bmem **
     ((sp + 32) ↦ₘ v0) **
     ((sp + 40) ↦ₘ (BitVec.sshiftRight (v1 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64))) **
     ((sp + 48) ↦ₘ (BitVec.sshiftRight (BitVec.sshiftRight (v1 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)) **
     ((sp + 56) ↦ₘ (BitVec.sshiftRight (BitVec.sshiftRight (v1 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)))
    (by pcFree) hdone
  have hbd1 := cpsTriple_seq_with_perm_same_cr (base + 124) (base + 188) (base + 192) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody1_f hdone1_f
  -- Body 0 + done
  have hdone0_f := cpsTriple_frame_left (base + 188) (base + 192) _ _ _
    ((.x5 ↦ᵣ (BitVec.sshiftRight (v0 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64))) **
     (.x6 ↦ᵣ shift_amount) **
     (.x10 ↦ᵣ (BitVec.sshiftRight (BitVec.sshiftRight (v0 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)) **
     (.x0 ↦ᵣ (0 : Word)) ** bmem **
     ((sp + 32) ↦ₘ (BitVec.sshiftRight (v0 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64))) **
     ((sp + 40) ↦ₘ (BitVec.sshiftRight (BitVec.sshiftRight (v0 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)) **
     ((sp + 48) ↦ₘ (BitVec.sshiftRight (BitVec.sshiftRight (v0 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)) **
     ((sp + 56) ↦ₘ (BitVec.sshiftRight (BitVec.sshiftRight (v0 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)))
    (by pcFree) hdone
  have hbd0 := cpsTriple_seq_with_perm_same_cr (base + 156) (base + 188) (base + 192) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody0_f hdone0_f
  -- Address normalization: done spec produces signExtend12 32, goal needs 32
  have hse32 : sp + signExtend12 (32 : BitVec 12) = sp + 32 := by rw [signExtend12_32]
  -- Helper: weaken body+done postconditions to regOwn + concrete mem values
  -- For bodies 0,1,2 (which have x10 in postcondition):
  have body_post_weaken : ∀ (r5v r6v r10v m32 m40 m48 m56 : Word),
      ∀ h, ((.x12 ↦ᵣ (sp + signExtend12 32)) ** (.x5 ↦ᵣ r5v) ** (.x6 ↦ᵣ r6v) **
            (.x10 ↦ᵣ r10v) **
            (.x0 ↦ᵣ (0 : Word)) ** bmem **
            ((sp + 32) ↦ₘ m32) ** ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56)) h →
           ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) **
            (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
            bmem **
            ((sp + 32) ↦ₘ m32) ** ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56)) h := by
    intro r5v r6v r10v m32 m40 m48 m56 h hp
    rw [hse32] at hp
    have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x5 _)) h hp
    have w2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 _))) h w1
    have w3 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)))) h w2
    xperm_hyp w3
  -- Apply weakening to each body+done
  have hbd0_w := cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => hp) (fun h hq => body_post_weaken _ _ _ _ _ _ _ h (by xperm_hyp hq)) hbd0
  have hbd1_w := cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => hp) (fun h hq => body_post_weaken _ _ _ _ _ _ _ h (by xperm_hyp hq)) hbd1
  have hbd2_w := cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => hp) (fun h hq => body_post_weaken _ _ _ _ _ _ _ h (by xperm_hyp hq)) hbd2
  -- Body 3 has no x10 — need to introduce regOwn .x10 from x10 in Phase C frame
  -- After merge, the precondition will include (.x10 ↦ᵣ _) from Phase C exit post.
  -- So we use cpsTriple_of_forall_regIs_to_regOwn to absorb x10 in precondition
  -- Or rather: the body3+done postcondition doesn't have x10. But x10 is in the frame from Phase C.
  -- So after merging, x10 will appear as part of the frame (from Phase C exit post).
  -- When we frame hbd3 for merging, x10 is part of the external frame.
  -- So body_3 post just needs (.x12 ↦ᵣ sp+32) ** (.x5 ↦ᵣ _) ** (.x6 ↦ᵣ _) ** mem
  -- and the x10 from Phase C exit is carried in the frame.
  -- After hbd3_w (via cpsTriple_consequence), we just need to weaken x5, x6, and keep everything else.
  -- Then x10 from the Phase C frame gets weakened to regOwn .x10 separately in the merge step.
  -- Actually, the simpler approach: frame hbd3 with (.x10 ↦ᵣ _) from Phase C exit, then weaken.
  -- But the way cpsNBranch_merge works is: for each exit (addr, Q), prove cpsTriple addr exit_ cr Q R.
  -- Q is (phase_c_exit_post ** F). So Q already contains (.x10 ↦ᵣ ...).
  -- The body specs don't touch x10 (for body_3) so x10 persists in the frame.
  -- So hbd3 postcondition doesn't mention x10, but after framing for merge, x10 will be in the frame.
  -- This means I need a body3 weakening that includes x10 from the frame.
  -- Let me just add x10 to the body3 weakening as well.
  have body3_post_weaken : ∀ (r5v r6v m56 x10v : Word),
      ∀ h, ((.x12 ↦ᵣ (sp + signExtend12 32)) ** (.x5 ↦ᵣ r5v) ** (.x6 ↦ᵣ r6v) **
            ((sp + 56) ↦ₘ m56) **
            (.x10 ↦ᵣ x10v) **
            (.x0 ↦ᵣ (0 : Word)) ** bmem **
            ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2)) h →
           ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) **
            (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
            bmem **
            ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ m56)) h := by
    intro r5v r6v m56 x10v h hp
    rw [hse32] at hp
    -- Reorder to put x5, x6, x10 first for weakening
    have hp' := (congrFun (show _ = ((.x5 ↦ᵣ r5v) ** (.x6 ↦ᵣ r6v) ** (.x10 ↦ᵣ x10v) **
      (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) ** bmem **
      ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ m56))
      from by xperm) h).mp hp
    have w1 := sepConj_mono_left (regIs_to_regOwn .x5 _) h hp'
    have w2 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 _)) h w1
    have w3 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _))) h w2
    exact (congrFun (show _ = _ from by xperm) h).mp w3
  -- signextend bridge: connect body outputs to (EvmWord.signextend b x).getLimb i
  -- Key facts
  -- Key arithmetic facts
  have hb0_lt31 : b0.toNat < 31 := by
    rw [signExtend12_31] at hsmall
    exact BitVec.lt_def.mp (of_decide_eq_true hsmall)
  -- High limbs of b are zero
  have hb12_b3 := BitVec.or_eq_zero_iff.mp hhigh
  have hb1b2 := BitVec.or_eq_zero_iff.mp hb12_b3.1
  have hb1_zero : b1 = 0 := hb1b2.1
  have hb2_zero : b2 = 0 := hb1b2.2
  have hb3_zero : b3 = 0 := hb12_b3.2
  -- b.toNat = b0.toNat (since high limbs are zero)
  have hb0_eq_b : b0.toNat = b.toNat := by
    have hdecomp := EvmWord.toNat_eq_limb_sum b
    change b0.toNat = b.toNat
    rw [hdecomp]
    simp only [b1, b2, b3] at hb1_zero hb2_zero hb3_zero
    simp [b0, hb1_zero, hb2_zero, hb3_zero]
  have hnotge : ¬ b.toNat ≥ 31 := by omega
  -- limb_idx.toNat = b.toNat / 8
  have hlimb_idx_eq : limb_idx.toNat = b.toNat / 8 := by
    show (b0 >>> (3 : BitVec 6).toNat).toNat = b.toNat / 8
    have h3 : (3 : BitVec 6).toNat = 3 := by decide
    rw [h3, BitVec.toNat_ushiftRight, hb0_eq_b]
    simp [Nat.shiftRight_eq_div_pow]
  -- shift_amount.toNat % 64 = 56 - (b.toNat % 8) * 8
  have hsa_mod : shift_amount.toNat % 64 = 56 - (b.toNat % 8) * 8 := by
    show ((56 : Word) - byte_shift).toNat % 64 = 56 - (b.toNat % 8) * 8
    have h3 : (3 : BitVec 6).toNat = 3 := by decide
    -- byte_shift = (b0 &&& 7) <<< 3
    have hbs : byte_shift = (b0 &&& signExtend12 (7 : BitVec 12)) <<< (3 : BitVec 6).toNat := rfl
    rw [h3] at hbs
    -- b0.toNat < 31 → we can compute everything via bv_omega style
    -- (b0 &&& 7).toNat = b0.toNat % 8
    have h7 : signExtend12 (7 : BitVec 12) = (7 : Word) := by decide
    have hand : (b0 &&& (7 : Word)).toNat = b0.toNat % 8 := by
      rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod b0.toNat 3
    -- ((b0 &&& 7) <<< 3).toNat = (b0.toNat % 8) * 8
    have hm8 : b0.toNat % 8 < 8 := Nat.mod_lt _ (by omega)
    have hshift_val : byte_shift.toNat = (b0.toNat % 8) * 8 := by
      rw [hbs, h7]; bv_omega
    -- 56 - byte_shift fits in Word and the mod 64 is identity
    have h56_sub : ((56 : Word) - byte_shift).toNat = 56 - (b0.toNat % 8) * 8 := by
      rw [hbs, h7]; bv_omega
    rw [h56_sub, hb0_eq_b]
    have hm8 : b.toNat % 8 < 8 := Nat.mod_lt _ (by omega)
    omega
  -- getLimbN = getLimb for in-range indices
  have hlimb_idx_lt4 : limb_idx.toNat < 4 := by rw [hlimb_idx_eq]; omega
  have hLN_eq : x.getLimbN (b.toNat / 8) = x.getLimb ⟨b.toNat / 8, by omega⟩ :=
    EvmWord.getLimbN_lt x (b.toNat / 8) (by omega)
  -- signextLimb and signextFill in terms of body output
  -- signextLimb (x.getLimbN (b.toNat/8)) (BitVec.ofNat 64 (56-(b.toNat%8)*8))
  --   = sshiftRight (getLimbN <<< sa_mod) sa_mod
  -- where sa = BitVec.ofNat 64 (56-(b.toNat%8)*8), sa.toNat % 64 = 56-(b.toNat%8)*8
  -- This equals the body output: sshiftRight (v_target <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)
  -- when v_target = x.getLimb target_idx and shift_amount.toNat % 64 = sa.toNat % 64
  -- Common target postcondition
  let resultPost :=
    (.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) **
    (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
    bmem **
    ((sp + 32) ↦ₘ (EvmWord.signextend b x).getLimb 0) **
    ((sp + 40) ↦ₘ (EvmWord.signextend b x).getLimb 1) **
    ((sp + 48) ↦ₘ (EvmWord.signextend b x).getLimb 2) **
    ((sp + 56) ↦ₘ (EvmWord.signextend b x).getLimb 3)
  -- The sa_nat for BitVec.ofNat matches shift_amount.toNat % 64
  have hsa_ofNat : (BitVec.ofNat 64 (56 - (b.toNat % 8) * 8)).toNat % 64 = shift_amount.toNat % 64 := by
    rw [hsa_mod]
    simp [BitVec.toNat_ofNat]
    have : b.toNat % 8 < 8 := Nat.mod_lt _ (by omega)
    omega
  -- Body 0 bridge: limb_idx = 0 → outputs match signextend getLimb
  have hbd0_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbd0_w (fun (hli : limb_idx = 0) h hq => by
      have hL : b.toNat / 8 = 0 := by
        have := congrArg BitVec.toNat hli; rw [hlimb_idx_eq] at this; simpa using this
      have hv0_eq : v0 = x.getLimbN (b.toNat / 8) := by rw [hL]; exact rfl
      have heq0 := EvmWord.signextend_getLimb_target b x hnotge (0 : Fin 4) (by simp [hL])
      have heq1 := EvmWord.signextend_getLimb_above b x hnotge (1 : Fin 4) (by simp [hL])
      have heq2 := EvmWord.signextend_getLimb_above b x hnotge (2 : Fin 4) (by simp [hL])
      have heq3 := EvmWord.signextend_getLimb_above b x hnotge (3 : Fin 4) (by simp [hL])
      simp only [EvmWord.signextLimb, EvmWord.signextFill] at heq0 heq1 heq2 heq3
      rw [hsa_ofNat, hL] at heq0 heq1 heq2 heq3
      rw [hv0_eq] at hq
      show resultPost h
      simp only [resultPost, heq0, heq1, heq2, heq3]
      rw [hL] at hq; exact hq)
  -- Body 1 bridge: limb_idx = signExtend12 1 → outputs match signextend getLimb
  have hbd1_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbd1_w (fun (hli : limb_idx = (0 : Word) + signExtend12 1) h hq => by
      have hL : b.toNat / 8 = 1 := by
        have := congrArg BitVec.toNat hli; rw [hlimb_idx_eq] at this
        simp only [show ((0 : Word) + signExtend12 1).toNat = 1 from by decide] at this; exact this
      have hv1_eq : v1 = x.getLimbN (b.toNat / 8) := by rw [hL]; exact rfl
      have heq0 := EvmWord.signextend_getLimb_below b x hnotge (0 : Fin 4) (by simp [hL])
      have heq1 := EvmWord.signextend_getLimb_target b x hnotge (1 : Fin 4) (by simp [hL])
      have heq2 := EvmWord.signextend_getLimb_above b x hnotge (2 : Fin 4) (by simp [hL])
      have heq3 := EvmWord.signextend_getLimb_above b x hnotge (3 : Fin 4) (by simp [hL])
      simp only [EvmWord.signextLimb, EvmWord.signextFill] at heq1 heq2 heq3
      rw [hsa_ofNat, hL] at heq1 heq2 heq3
      rw [hv1_eq] at hq
      show resultPost h
      simp only [resultPost, heq0, heq1, heq2, heq3]
      rw [hL] at hq; exact hq)
  -- Body 2 bridge: limb_idx = signExtend12 2 → outputs match signextend getLimb
  have hbd2_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbd2_w (fun (hli : limb_idx = (0 : Word) + signExtend12 2) h hq => by
      have hL : b.toNat / 8 = 2 := by
        have := congrArg BitVec.toNat hli; rw [hlimb_idx_eq] at this
        simp only [show ((0 : Word) + signExtend12 2).toNat = 2 from by decide] at this; exact this
      have hv2_eq : v2 = x.getLimbN (b.toNat / 8) := by rw [hL]; exact rfl
      have heq0 := EvmWord.signextend_getLimb_below b x hnotge (0 : Fin 4) (by simp [hL])
      have heq1 := EvmWord.signextend_getLimb_below b x hnotge (1 : Fin 4) (by simp [hL])
      have heq2 := EvmWord.signextend_getLimb_target b x hnotge (2 : Fin 4) (by simp [hL])
      have heq3 := EvmWord.signextend_getLimb_above b x hnotge (3 : Fin 4) (by simp [hL])
      simp only [EvmWord.signextLimb, EvmWord.signextFill] at heq2 heq3
      rw [hsa_ofNat, hL] at heq2 heq3
      rw [hv2_eq] at hq
      show resultPost h
      simp only [resultPost, heq0, heq1, heq2, heq3]
      rw [hL] at hq; exact hq)
  -- Body 3 bridge: limb_idx ≠ 0,1,2 → limb_idx = 3 → outputs match signextend getLimb
  -- Body 3 doesn't have x10, so we frame it from Phase C exit 3's (.x10 ↦ᵣ (0 + signExtend12 2))
  have hbd3_x10 := cpsTriple_frame_left _ _ _ _ _ ((.x10 ↦ᵣ ((0 : Word) + signExtend12 2))) (by pcFree) hbd3
  have hbd3_w := cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => hp) (fun h hq => body3_post_weaken _ _ _ _ h (by xperm_hyp hq)) hbd3_x10
  have hbd3_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbd3_w (fun (hli : limb_idx ≠ 0 ∧ limb_idx ≠ (0 : Word) + signExtend12 1 ∧ limb_idx ≠ (0 : Word) + signExtend12 2) h hq => by
      have hL : b.toNat / 8 = 3 := by
        obtain ⟨h0, h1, h2⟩ := hli
        have hn0 : limb_idx.toNat ≠ 0 :=
          fun hc => h0 (BitVec.eq_of_toNat_eq (by simpa using hc))
        have hn1 : limb_idx.toNat ≠ 1 :=
          fun hc => h1 (BitVec.eq_of_toNat_eq (by
            show limb_idx.toNat = ((0 : Word) + signExtend12 1).toNat
            simp only [show ((0 : Word) + signExtend12 1).toNat = 1 from by decide]; exact hc))
        have hn2 : limb_idx.toNat ≠ 2 :=
          fun hc => h2 (BitVec.eq_of_toNat_eq (by
            show limb_idx.toNat = ((0 : Word) + signExtend12 2).toNat
            simp only [show ((0 : Word) + signExtend12 2).toNat = 2 from by decide]; exact hc))
        omega
      have hv3_eq : v3 = x.getLimbN (b.toNat / 8) := by rw [hL]; exact rfl
      have heq0 := EvmWord.signextend_getLimb_below b x hnotge (0 : Fin 4) (by simp [hL])
      have heq1 := EvmWord.signextend_getLimb_below b x hnotge (1 : Fin 4) (by simp [hL])
      have heq2 := EvmWord.signextend_getLimb_below b x hnotge (2 : Fin 4) (by simp [hL])
      have heq3 := EvmWord.signextend_getLimb_target b x hnotge (3 : Fin 4) (by simp [hL])
      simp only [EvmWord.signextLimb] at heq3
      rw [hsa_ofNat, hL] at heq3
      rw [hv3_eq] at hq
      show resultPost h
      simp only [resultPost, heq0, heq1, heq2, heq3]
      rw [hL] at hq; exact hq)
  -- Frame Phase C with the full frame
  let phaseC_frame := (.x6 ↦ᵣ shift_amount) ** (.x12 ↦ᵣ sp) ** bmem **
    ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)
  have hphaseC_framed := cpsNBranch_frame_left
    (F := phaseC_frame) (by pcFree) hphaseC
  simp only [List.map] at hphaseC_framed
  -- Merge Phase C exits with body+done specs
  have hphaseCD := cpsNBranch_merge (base + 56) (base + 192) (signextCode base) _ _ _ hphaseC_framed
    (fun exit hmem => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- Exit 0: limb_idx = 0 → body_0 at base+156
        exact cpsTriple_consequence _ _ _ _ _ _ _
          (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hbd0_ev
      · -- Exit 1: limb_idx = 1 → body_1 at base+124
        exact cpsTriple_consequence _ _ _ _ _ _ _
          (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hbd1_ev
      · -- Exit 2: limb_idx = 2 → body_2 at base+96
        exact cpsTriple_consequence _ _ _ _ _ _ _
          (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hbd2_ev
      · -- Exit 3: limb_idx ≠ 0,1,2 → body_3 at base+76
        exact cpsTriple_consequence _ _ _ _ _ _ _
          (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hbd3_ev)
  -- Flatten hphaseAB postcondition for composition
  have hphaseAB' : cpsTriple base (base + 56) (signextCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x5 ↦ᵣ limb_idx) ** (.x6 ↦ᵣ shift_amount) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ byte_shift) **
       (.x12 ↦ᵣ sp) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      hphaseAB
  -- Final: Phase AB -> Phase CD
  have hfull := cpsTriple_seq_with_perm_same_cr base (base + 56) (base + 192) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hphaseAB' hphaseCD
  -- Final consequence: permute to match goal shape
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hfull

end EvmAsm.Evm64
