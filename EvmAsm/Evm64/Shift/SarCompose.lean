/-
  EvmAsm.Evm64.Shift.SarCompose

  Hierarchical composition of SAR CPS specs into a single full-program theorem.
  Composes the 5 execution paths through `evm_sar` (95 instructions, 380 bytes):
  - Sign-fill path (shift ≥ 256): Phase A taken → sign_fill_path
  - Body L (L=0..3, shift < 256): Phase A ntaken → B → C(exit L) → body_L → exit

  Mirrors ShlCompose.lean/Compose.lean with SAR body specs and bridge lemmas.
-/

import EvmAsm.Evm64.Shift.SarSpec
import EvmAsm.Evm64.Shift.ComposeBase
import EvmAsm.Evm64.SpAddr
import Mathlib.Tactic.Set

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm
  (zero_add_se12_1_toNat zero_add_se12_2_toNat bv6_toNat_6 bv64_toNat_63 word_add_zero)

-- ============================================================================
-- Section 1: sarCode definition and helpers
-- ============================================================================

-- `shr_phase_b_len` lives in `ComposeBase` (shared with SHR/SHL).
-- SAR-specific length lemmas remain local.
private theorem sar_phase_a_len : sar_phase_a.length = 9 := by decide
private theorem sar_phase_c_len : sar_phase_c.length = 5 := by decide
private theorem sar_body_3_prog_len : (sar_body_3_prog 268).length = 8 := by decide
private theorem sar_body_2_prog_len : (sar_body_2_prog 212).length = 14 := by decide
private theorem sar_body_1_prog_len : (sar_body_1_prog 132).length = 20 := by decide
private theorem sar_body_0_prog_len : (sar_body_0_prog 32).length = 25 := by decide
private theorem sar_sign_fill_path_len : sar_sign_fill_path.length = 7 := by decide

/-- Skip one ofProg block in a right-nested union via range disjointness. -/
local macro "skipBlock" : tactic =>
  `(tactic| apply CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
        simp only [sar_phase_a_len, shr_phase_b_len, sar_phase_c_len,
          sar_body_3_prog_len, sar_body_2_prog_len, sar_body_1_prog_len,
          sar_body_0_prog_len, sar_sign_fill_path_len] at hk1 hk2
        bv_omega)))

/-- The full evm_sar code split into 8 per-phase CodeReq.ofProg blocks. -/
abbrev sarCode (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base sar_phase_a,                      -- block 0: 9 instrs at +0
    CodeReq.ofProg (base + 36) shr_phase_b,               -- block 1: 7 instrs at +36
    CodeReq.ofProg (base + 64) sar_phase_c,               -- block 2: 5 instrs at +64
    CodeReq.ofProg (base + 84) (sar_body_3_prog 268),     -- block 3: 8 instrs at +84
    CodeReq.ofProg (base + 116) (sar_body_2_prog 212),    -- block 4: 14 instrs at +116
    CodeReq.ofProg (base + 172) (sar_body_1_prog 132),    -- block 5: 20 instrs at +172
    CodeReq.ofProg (base + 252) (sar_body_0_prog 32),     -- block 6: 25 instrs at +252
    CodeReq.ofProg (base + 352) sar_sign_fill_path         -- block 7: 7 instrs at +352
  ]

-- `regIs_to_regOwn`, `CodeReq_union_sub_both`, `singleton_sub_ofProg` now live
-- in `EvmAsm.Evm64.Shift.ComposeBase` (shared across SHR/SHL/SAR).

-- ============================================================================
-- Section 2: Subsumption lemmas (via unionAll structural reasoning)
-- ============================================================================

-- Phase A individual instruction subsumption (via ofProg sar_phase_a, 9-element list)

private theorem ld_s1_sub_sarCode {base : Word} :
    ∀ a i, CodeReq.singleton base (.LD .x5 .x12 8) a = some i → sarCode base a = some i := by
  intro a i h
  have h1 := singleton_sub_ofProg base base sar_phase_a (.LD .x5 .x12 8) 0
    (by decide) (by decide) (by bv_omega) (by decide) a i h
  unfold sarCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

private theorem ld_or_16_sub_sarCode {base : Word} :
    ∀ a i, shr_ld_or_acc_code 16 (base + 4) a = some i → sarCode base a = some i := by
  intro a i h; unfold shr_ld_or_acc_code at h
  have h1 := CodeReq.ofProg_mono_sub base (base + 4) sar_phase_a (shr_ld_or_acc_prog 16) 1
    (by bv_omega) (by decide) (by decide) (by decide) a i h
  unfold sarCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

private theorem ld_or_24_sub_sarCode {base : Word} :
    ∀ a i, shr_ld_or_acc_code 24 (base + 12) a = some i → sarCode base a = some i := by
  intro a i h; unfold shr_ld_or_acc_code at h
  have h1 := CodeReq.ofProg_mono_sub base (base + 12) sar_phase_a (shr_ld_or_acc_prog 24) 3
    (by bv_omega) (by decide) (by decide) (by decide) a i h
  unfold sarCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

private theorem bne_sub_sarCode {base : Word} :
    ∀ a i, CodeReq.singleton (base + 20) (.BNE .x5 .x0 332) a = some i → sarCode base a = some i := by
  intro a i h
  have h1 := singleton_sub_ofProg base (base + 20) sar_phase_a (.BNE .x5 .x0 332) 5
    (by decide) (by decide) (by bv_omega) (by decide) a i h
  unfold sarCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

private theorem ld_s0_sub_sarCode {base : Word} :
    ∀ a i, CodeReq.singleton (base + 24) (.LD .x5 .x12 0) a = some i → sarCode base a = some i := by
  intro a i h
  have h1 := singleton_sub_ofProg base (base + 24) sar_phase_a (.LD .x5 .x12 0) 6
    (by decide) (by decide) (by bv_omega) (by decide) a i h
  unfold sarCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

private theorem sltiu_sub_sarCode {base : Word} :
    ∀ a i, CodeReq.singleton (base + 28) (.SLTIU .x10 .x5 256) a = some i → sarCode base a = some i := by
  intro a i h
  have h1 := singleton_sub_ofProg base (base + 28) sar_phase_a (.SLTIU .x10 .x5 256) 7
    (by decide) (by decide) (by bv_omega) (by decide) a i h
  unfold sarCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

private theorem beq_sub_sarCode {base : Word} :
    ∀ a i, CodeReq.singleton (base + 32) (.BEQ .x10 .x0 320) a = some i → sarCode base a = some i := by
  intro a i h
  have h1 := singleton_sub_ofProg base (base + 32) sar_phase_a (.BEQ .x10 .x0 320) 8
    (by decide) (by decide) (by bv_omega) (by decide) a i h
  unfold sarCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

/-- Phase B code (ofProg, 7 instrs at +36) is subsumed by sarCode (block 1). -/
private theorem phase_b_sub_sarCode {base : Word} :
    ∀ a i, shr_phase_b_code (base + 36) a = some i → sarCode base a = some i := by
  unfold shr_phase_b_code sarCode; simp only [CodeReq.unionAll_cons]
  skipBlock
  exact CodeReq.union_mono_left _ _

-- Phase C subsumption (SAR-specific offsets)

/-- SAR Phase C code (union chain, 5 instrs at +64). -/
abbrev sar_phase_c_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.BEQ .x5 .x0 188))
  (CodeReq.union (shr_cascade_step_code 1 100 (base + 4))
  (shr_cascade_step_code 2 36 (base + 12)))

-- Bridge: sar_phase_c_code (union chain) ⊆ ofProg sar_phase_c (5-element list)
private theorem sar_phase_c_code_sub_ofProg {base : Word} :
    ∀ a i, sar_phase_c_code base a = some i →
      (CodeReq.ofProg base sar_phase_c) a = some i := by
  unfold sar_phase_c_code shr_cascade_step_code
  apply CodeReq_union_sub_both
  · exact singleton_sub_ofProg base base sar_phase_c (.BEQ .x5 .x0 188) 0
      (by decide) (by decide) (by bv_omega) (by decide)
  · apply CodeReq_union_sub_both
    · exact CodeReq.ofProg_mono_sub base (base + 4) sar_phase_c (shr_cascade_step_prog 1 100) 1
        (by bv_omega) (by decide) (by decide) (by decide)
    · exact CodeReq.ofProg_mono_sub base (base + 12) sar_phase_c (shr_cascade_step_prog 2 36) 3
        (by bv_omega) (by decide) (by decide) (by decide)

private theorem ofProg_phase_c_sub_sarCode {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + 64) sar_phase_c) a = some i → sarCode base a = some i := by
  unfold sarCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- SAR Phase C code is subsumed by sarCode (block 2). -/
private theorem sar_phase_c_sub_sarCode {base : Word} :
    ∀ a i, sar_phase_c_code (base + 64) a = some i → sarCode base a = some i := by
  intro a i h
  exact ofProg_phase_c_sub_sarCode a i (sar_phase_c_code_sub_ofProg a i h)

-- Body subsumption lemmas

/-- SAR Body 3 code (8 instrs at +84) is subsumed by sarCode (block 3). -/
private theorem sar_body_3_sub_sarCode {base : Word} :
    ∀ a i, sar_body_3_code (base + 84) 268 a = some i → sarCode base a = some i := by
  unfold sar_body_3_code sarCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- SAR Body 2 code (14 instrs at +116) is subsumed by sarCode (block 4). -/
private theorem sar_body_2_sub_sarCode {base : Word} :
    ∀ a i, sar_body_2_code (base + 116) 212 a = some i → sarCode base a = some i := by
  unfold sar_body_2_code sarCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- SAR Body 1 code (20 instrs at +172) is subsumed by sarCode (block 5). -/
private theorem sar_body_1_sub_sarCode {base : Word} :
    ∀ a i, sar_body_1_code (base + 172) 132 a = some i → sarCode base a = some i := by
  unfold sar_body_1_code sarCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- SAR Body 0 code (25 instrs at +252) is subsumed by sarCode (block 6). -/
private theorem sar_body_0_sub_sarCode {base : Word} :
    ∀ a i, sar_body_0_code (base + 252) 32 a = some i → sarCode base a = some i := by
  unfold sar_body_0_code sarCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

-- Bridge: sar_sign_fill_path_code (union chain) ⊆ ofProg sar_sign_fill_path (7-element list)
private theorem sign_fill_code_sub_ofProg {base : Word} :
    ∀ a i, sar_sign_fill_path_code base a = some i →
      (CodeReq.ofProg base sar_sign_fill_path) a = some i := by
  unfold sar_sign_fill_path_code
  apply CodeReq_union_sub_both
  · exact singleton_sub_ofProg base base sar_sign_fill_path (.LD .x5 .x12 56) 0
      (by decide) (by decide) (by bv_omega) (by decide)
  · apply CodeReq_union_sub_both
    · exact singleton_sub_ofProg base (base + 4) sar_sign_fill_path (.SRAI .x5 .x5 63) 1
        (by decide) (by decide) (by bv_omega) (by decide)
    · apply CodeReq_union_sub_both
      · exact singleton_sub_ofProg base (base + 8) sar_sign_fill_path (.ADDI .x12 .x12 32) 2
          (by decide) (by decide) (by bv_omega) (by decide)
      · apply CodeReq_union_sub_both
        · exact singleton_sub_ofProg base (base + 12) sar_sign_fill_path (.SD .x12 .x5 0) 3
            (by decide) (by decide) (by bv_omega) (by decide)
        · apply CodeReq_union_sub_both
          · exact singleton_sub_ofProg base (base + 16) sar_sign_fill_path (.SD .x12 .x5 8) 4
              (by decide) (by decide) (by bv_omega) (by decide)
          · apply CodeReq_union_sub_both
            · exact singleton_sub_ofProg base (base + 20) sar_sign_fill_path (.SD .x12 .x5 16) 5
                (by decide) (by decide) (by bv_omega) (by decide)
            · exact singleton_sub_ofProg base (base + 24) sar_sign_fill_path (.SD .x12 .x5 24) 6
                (by decide) (by decide) (by bv_omega) (by decide)

private theorem ofProg_sign_fill_sub_sarCode {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + 352) sar_sign_fill_path) a = some i → sarCode base a = some i := by
  unfold sarCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Sign-fill path code (7 instrs at +352) is subsumed by sarCode (block 7). -/
private theorem sign_fill_sub_sarCode {base : Word} :
    ∀ a i, sar_sign_fill_path_code (base + 352) a = some i → sarCode base a = some i := by
  intro a i h
  exact ofProg_sign_fill_sub_sarCode a i (sign_fill_code_sub_ofProg a i h)

-- ============================================================================
-- Section 3: Address normalization lemmas
-- ============================================================================

private theorem sar_off_4 {base : Word} : (base + 4 : Word) + 8 = base + 12 := by bv_omega
private theorem sar_off_12 {base : Word} : (base + 12 : Word) + 8 = base + 20 := by bv_omega
private theorem sar_off_20 {base : Word} : (base + 20 : Word) + 4 = base + 24 := by bv_omega
private theorem sar_off_24 {base : Word} : (base + 24 : Word) + 4 = base + 28 := by bv_omega
private theorem sar_off_28 {base : Word} : (base + 28 : Word) + 4 = base + 32 := by bv_omega
private theorem sar_off_32 {base : Word} : (base + 32 : Word) + 4 = base + 36 := by bv_omega
private theorem sar_off_36_28 {base : Word} : (base + 36 : Word) + 28 = base + 64 := by bv_omega
private theorem sar_off_352_28 {base : Word} : (base + 352 : Word) + 28 = base + 380 := by bv_omega
private theorem sar_bne_target {base : Word} : (base + 20 : Word) + signExtend13 332 = base + 352 := by
  rv64_addr
private theorem sar_beq_target {base : Word} : (base + 32 : Word) + signExtend13 320 = base + 352 := by
  rv64_addr
-- Phase C exit addresses
private theorem sar_c_e0 {base : Word} : (base + 64 : Word) + signExtend13 188 = base + 252 := by
  rv64_addr
private theorem sar_c_e1 {base : Word} : ((base + 64 : Word) + 8) + signExtend13 100 = base + 172 := by
  rv64_addr
private theorem sar_c_e2 {base : Word} : ((base + 64 : Word) + 16) + signExtend13 36 = base + 116 := by
  rv64_addr
private theorem sar_c_e3 {base : Word} : (base + 64 : Word) + 20 = base + 84 := by bv_omega
-- Body exit addresses (JAL targets → base+380)
private theorem sar_body3_exit {base : Word} : ((base + 84 : Word) + 28) + signExtend21 268 = base + 380 := by
  rv64_addr
private theorem sar_body2_exit {base : Word} : ((base + 116 : Word) + 52) + signExtend21 212 = base + 380 := by
  rv64_addr
private theorem sar_body1_exit {base : Word} : ((base + 172 : Word) + 76) + signExtend21 132 = base + 380 := by
  rv64_addr
private theorem sar_body0_exit {base : Word} : ((base + 252 : Word) + 96) + signExtend21 32 = base + 380 := by
  rv64_addr

-- ============================================================================
-- Section 4: Sign-fill path composition
-- ============================================================================

/-- Sign-fill via BNE taken: high shift limbs are nonzero → shift ≥ 256 → result is sign extension.
    Execution: LD s1 → LD/OR s2 → LD/OR s3 → BNE(taken) → sign_fill_path. -/
theorem evm_sar_sign_fill_high_spec (sp base : Word)
    {s0 s1 s2 s3 v0 v1 v2 v3 : Word} (r5 r10 : Word)
    (hhigh : s1 ||| s2 ||| s3 ≠ 0) :
    let sign_ext := BitVec.sshiftRight v3 63
    cpsTriple base (base + 380) (sarCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ sign_ext) ** ((sp + 40) ↦ₘ sign_ext) **
       ((sp + 48) ↦ₘ sign_ext) ** ((sp + 56) ↦ₘ sign_ext)) := by
  intro sign_ext
  -- Step 1: LD x5 x12 8 at base → extend to sarCode
  have h1 := cpsTriple_extend_code ld_s1_sub_sarCode
    (ld_spec_gen .x5 .x12 sp r5 s1 8 base (by nofun))
  simp only [signExtend12_8] at h1
  -- Step 2: LD/OR at base+4 → extend to sarCode
  have h2 := cpsTriple_extend_code ld_or_16_sub_sarCode
    (shr_ld_or_acc_spec sp s1 r10 s2 16 (base + 4))
  simp only [signExtend12_16] at h2
  rw [sar_off_4] at h2
  -- Step 3: LD/OR at base+12 → extend to sarCode
  have h3 := cpsTriple_extend_code ld_or_24_sub_sarCode
    (shr_ld_or_acc_spec sp (s1 ||| s2) s2 s3 24 (base + 12))
  simp only [signExtend12_24] at h3
  rw [sar_off_12] at h3
  -- Frame and compose LD → LD/OR → LD/OR
  have h1f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
     (sp ↦ₘ s0) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h1
  have h2f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h2
  have h12 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1f h2f
  have h3f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h3
  have h123 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 h3f
  -- Step 4: BNE at base+20 → extend to sarCode, eliminate ntaken
  have hbne_raw := bne_spec_gen .x5 .x0 332 (s1 ||| s2 ||| s3) (0 : Word) (base + 20)
  rw [sar_bne_target, sar_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code bne_sub_sarCode hbne_raw
  -- Eliminate ntaken path (s1|||s2|||s3 = 0 contradicts hhigh)
  have hbne_taken := cpsBranch_takenStripPure2 hbne
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hhigh)
  -- Frame BNE with remaining state
  have hbne_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ s3) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbne_taken
  -- Compose linear chain → BNE(taken)
  have hAB := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hbne_framed
  -- Step 5: Sign-fill path (base+352 → base+380) → extend to sarCode
  have hsfp := cpsTriple_extend_code sign_fill_sub_sarCode
    (sar_sign_fill_path_spec sp (s1 ||| s2 ||| s3) s3 v0 v1 v2 v3 (base + 352))
  rw [sar_off_352_28] at hsfp
  -- Frame sign-fill path with remaining state
  have hsfp_framed := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) hsfp
  -- Compose AB → sign-fill: no address normalization needed (sign-fill uses sp+40 etc. directly)
  have hABS := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAB hsfp_framed
  -- Final: weaken regs to regOwn
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ sign_ext) ** (.x10 ↦ᵣ s3) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
           ((sp + 32) ↦ₘ sign_ext) ** ((sp + 40) ↦ₘ sign_ext) ** ((sp + 48) ↦ₘ sign_ext) ** ((sp + 56) ↦ₘ sign_ext))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
         ((sp + 32) ↦ₘ sign_ext) ** ((sp + 40) ↦ₘ sign_ext) ** ((sp + 48) ↦ₘ sign_ext) ** ((sp + 56) ↦ₘ sign_ext))
        from by xperm) h).mp w1)
    hABS

/-- Sign-fill via BEQ taken: s1=s2=s3=0 but s0 ≥ 256 → result is sign extension. -/
theorem evm_sar_sign_fill_large_spec (sp base : Word)
    {s0 s1 s2 s3 v0 v1 v2 v3 : Word} (r5 r10 : Word)
    (hlow : s1 ||| s2 ||| s3 = 0)
    (hlarge : BitVec.ult s0 (signExtend12 (256 : BitVec 12)) = false) :
    let sign_ext := BitVec.sshiftRight v3 63
    cpsTriple base (base + 380) (sarCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ sign_ext) ** ((sp + 40) ↦ₘ sign_ext) **
       ((sp + 48) ↦ₘ sign_ext) ** ((sp + 56) ↦ₘ sign_ext)) := by
  intro sign_ext
  -- Steps 1-3: Same linear chain as sign_fill_high (LD s1 → LD/OR s2 → LD/OR s3)
  have h1 := cpsTriple_extend_code ld_s1_sub_sarCode
    (ld_spec_gen .x5 .x12 sp r5 s1 8 base (by nofun))
  simp only [signExtend12_8] at h1
  have h2 := cpsTriple_extend_code ld_or_16_sub_sarCode
    (shr_ld_or_acc_spec sp s1 r10 s2 16 (base + 4))
  simp only [signExtend12_16] at h2; rw [sar_off_4] at h2
  have h3 := cpsTriple_extend_code ld_or_24_sub_sarCode
    (shr_ld_or_acc_spec sp (s1 ||| s2) s2 s3 24 (base + 12))
  simp only [signExtend12_24] at h3; rw [sar_off_12] at h3
  -- Frame + compose linear chain
  have h1f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
     (sp ↦ₘ s0) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h1
  have h2f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h2
  have h12 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1f h2f
  have h3f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h3
  have h123 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h12 h3f
  -- Step 4: BNE at base+20 offset 332 → eliminate TAKEN (s1|||s2|||s3 = 0 contradicts ≠ 0)
  have hbne_raw := bne_spec_gen .x5 .x0 332 (s1 ||| s2 ||| s3) (0 : Word) (base + 20)
  rw [sar_bne_target, sar_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code bne_sub_sarCode hbne_raw
  have hbne_ntaken := cpsBranch_ntakenStripPure2 hbne
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hlow)
  -- Frame BNE(ntaken) with remaining state
  have hbne_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ s3) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbne_ntaken
  -- Compose linear → BNE(ntaken)
  have h1234 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h123 hbne_framed
  -- Step 5: LD x5 x12 0 at base+24 → extend to sarCode
  have hld_raw := ld_spec_gen .x5 .x12 sp (s1 ||| s2 ||| s3) s0 0 (base + 24) (by nofun)
  simp only [signExtend12_0] at hld_raw
  rw [word_add_zero, sar_off_24] at hld_raw
  have hld := cpsTriple_extend_code ld_s0_sub_sarCode hld_raw
  -- Step 6: SLTIU at base+28 → extend to sarCode
  have hsltiu_raw := sltiu_spec_gen .x10 .x5 s3 s0 256 (base + 28) (by nofun)
  rw [sar_off_28] at hsltiu_raw
  have hsltiu := cpsTriple_extend_code sltiu_sub_sarCode hsltiu_raw
  -- Frame + compose LD → SLTIU
  have hld_f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ s3) **
     ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hld
  have hsltiu_f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hsltiu
  have h56 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hld_f hsltiu_f
  -- Compose h1234 → h56
  have h123456 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1234 h56
  -- Step 7: BEQ at base+32 offset 320 → eliminate ntaken (sltiuVal = 0 since s0 ≥ 256)
  let sltiuVal := (if BitVec.ult s0 (signExtend12 (256 : BitVec 12)) then (1 : Word) else (0 : Word))
  have hbeq_raw := beq_spec_gen .x10 .x0 320 sltiuVal (0 : Word) (base + 32)
  rw [sar_beq_target, sar_off_32] at hbeq_raw
  have hbeq := cpsBranch_extend_code beq_sub_sarCode hbeq_raw
  -- sltiuVal = 0 (since s0 ≥ 256 → ult is false)
  have hsltiu_eq : sltiuVal = (0 : Word) := by
    simp only [sltiuVal, hlarge]; decide
  -- Eliminate ntaken: ntaken postcondition has ⌜sltiuVal ≠ 0⌝, but sltiuVal = 0
  have hbeq_taken := cpsBranch_takenStripPure2 hbeq
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact ((sepConj_pure_right _).mp h_rest).2 hsltiu_eq)
  -- Frame BEQ(taken) with remaining state
  have hbeq_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbeq_taken
  -- Compose h123456 → BEQ(taken)
  have h1234567 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h123456 hbeq_framed
  -- Step 8: Sign-fill path (base+352 → base+380)
  have hsfp := cpsTriple_extend_code sign_fill_sub_sarCode
    (sar_sign_fill_path_spec sp s0 sltiuVal v0 v1 v2 v3 (base + 352))
  rw [sar_off_352_28] at hsfp
  have hsfp_framed := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) hsfp
  -- Compose → SFP
  have hfull := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1234567 hsfp_framed
  -- Final: weaken regs to regOwn
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (BitVec.sshiftRight v3 63)) ** (.x10 ↦ᵣ sltiuVal) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
           ((sp + 32) ↦ₘ (BitVec.sshiftRight v3 63)) ** ((sp + 40) ↦ₘ (BitVec.sshiftRight v3 63)) **
           ((sp + 48) ↦ₘ (BitVec.sshiftRight v3 63)) ** ((sp + 56) ↦ₘ (BitVec.sshiftRight v3 63)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
         ((sp + 32) ↦ₘ (BitVec.sshiftRight v3 63)) ** ((sp + 40) ↦ₘ (BitVec.sshiftRight v3 63)) **
         ((sp + 48) ↦ₘ (BitVec.sshiftRight v3 63)) ** ((sp + 56) ↦ₘ (BitVec.sshiftRight v3 63)))
        from by xperm) h).mp w1)
    hfull

-- ============================================================================
-- Section 5: Phase C spec (SAR-specific offsets)
-- ============================================================================

/-- SAR Phase C cascade dispatch. Same structure as SHR but with SAR exit addresses. -/
theorem sar_phase_c_spec_pure (v5 v10 : Word) (base : Word)
    (e0 e1 e2 e3 : Word)
    (he0 : base + signExtend13 188 = e0)
    (he1 : (base + 8) + signExtend13 100 = e1)
    (he2 : (base + 16) + signExtend13 36 = e2)
    (he3 : base + 20 = e3) :
    let code := sar_phase_c_code base
    cpsNBranch base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      [(e0, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 = 0⌝),
       (e1, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 = (0 : Word) + signExtend12 1⌝),
       (e2, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 = (0 : Word) + signExtend12 2⌝),
       (e3, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) **
            ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1 ∧ v5 ≠ (0 : Word) + signExtend12 2⌝)] := by
  have hc1 : ((base + 4 : Word) + 4) + signExtend13 100 = e1 := by
    rw [show (base + 4 : Word) + 4 = base + 8 from by bv_addr]; exact he1
  have hc2 : ((base + 12 : Word) + 4) + signExtend13 36 = e2 := by
    rw [show (base + 12 : Word) + 4 = base + 16 from by bv_addr]; exact he2
  let cr_beq0 := CodeReq.singleton base (.BEQ .x5 .x0 188)
  let cr_cs1 := shr_cascade_step_code 1 100 (base + 4)
  let cr_cs2 := shr_cascade_step_code 2 36 (base + 12)
  have hd_beq0_cs1 : cr_beq0.Disjoint cr_cs1 :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have hd_beq0_cs2 : cr_beq0.Disjoint cr_cs2 :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have hd_cs1_cs2 : cr_cs1.Disjoint cr_cs2 :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.singleton (by bv_omega)))
  -- Step 0: BEQ x5 x0 188
  have beq0_raw := beq_spec_gen .x5 .x0 188 v5 (0 : Word) base
  rw [he0] at beq0_raw
  have beq0f : cpsBranch base cr_beq0
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      e0 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 = 0⌝)
      (base + 4) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 ≠ 0⌝) :=
    cpsBranch_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranch_frameR (.x10 ↦ᵣ v10) (by pcFree) beq0_raw)
  -- Step 1: cascade step at base+4
  have cs1_raw := shr_cascade_step_spec_pure v5 v10 1 100 (base + 4) e1 hc1
  rw [show (base + 4 : Word) + 8 = base + 12 from by bv_addr] at cs1_raw
  have cs1f := cpsBranch_frameR (⌜v5 ≠ (0 : Word)⌝) pcFree_pure cs1_raw
  have cs1_clean : cpsBranch (base + 4) cr_cs1
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 ≠ (0 : Word)⌝)
      e1 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 = (0 : Word) + signExtend12 1⌝)
      (base + 12) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1⌝) :=
    cpsBranch_weaken
      (fun h hp => (congrFun (show _ = _ from by xperm) h).mp hp)
      (fun h hp => (sepConj_pure_right h).1 hp |>.1)
      (fun h hp => by
        have ⟨hinner, hne0⟩ := (sepConj_pure_right h).1 hp
        have hne1 := sepConj_extract_pure_end3 h hinner
        have hregs := sepConj_strip_pure_end3 h hinner
        exact (congrFun (show _ = _ from by xperm) h).mp
          ((sepConj_pure_right h).2 (And.intro hregs (And.intro hne0 hne1))))
      cs1f
  -- Step 2: cascade step at base+12
  have cs2_raw := shr_cascade_step_spec_pure v5 ((0 : Word) + signExtend12 1) 2 36 (base + 12) e2 hc2
  rw [show (base + 12 : Word) + 8 = base + 20 from by bv_addr] at cs2_raw
  have cs2f := cpsBranch_frameR
    (⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1⌝) pcFree_pure cs2_raw
  have cs2_clean : cpsBranch (base + 12) cr_cs2
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1⌝)
      e2 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 = (0 : Word) + signExtend12 2⌝)
      (base + 20) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1 ∧ v5 ≠ (0 : Word) + signExtend12 2⌝) :=
    cpsBranch_weaken
      (fun h hp => (congrFun (show _ = _ from by xperm) h).mp hp)
      (fun h hp => (sepConj_pure_right h).1 hp |>.1)
      (fun h hp => by
        have ⟨hinner, ⟨hne0, hne1⟩⟩ := (sepConj_pure_right h).1 hp
        have hne2 := sepConj_extract_pure_end3 h hinner
        have hregs := sepConj_strip_pure_end3 h hinner
        exact (congrFun (show _ = _ from by xperm) h).mp
          ((sepConj_pure_right h).2 (And.intro hregs (And.intro hne0 (And.intro hne1 hne2)))))
      cs2f
  -- Fallthrough at base+20
  have ft := cpsNBranch_refl (base + 20)
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1 ∧ v5 ≠ (0 : Word) + signExtend12 2⌝)
    _ (fun _ hp => hp)
  have hunion_empty : ∀ (cr : CodeReq), cr.union CodeReq.empty = cr := by
    intro cr; funext a; simp only [CodeReq.union, CodeReq.empty]; cases cr a <;> rfl
  -- Chain cs2_clean + ft
  have n3 := cpsBranch_cons_cpsNBranch (CodeReq.Disjoint.empty_right cr_cs2) cs2_clean ft
  -- Chain cs1_clean + n3
  have hd_cs1_rest : cr_cs1.Disjoint (cr_cs2.union CodeReq.empty) := by
    rw [hunion_empty]; exact hd_cs1_cs2
  have n2 := cpsBranch_cons_cpsNBranch_with_perm hd_cs1_rest
    (fun h hp => by xperm_hyp hp) cs1_clean n3
  -- Chain beq0f + n2
  have hd_beq0_rest : cr_beq0.Disjoint (cr_cs1.union (cr_cs2.union CodeReq.empty)) := by
    rw [hunion_empty]; exact CodeReq.Disjoint.union_right hd_beq0_cs1 hd_beq0_cs2
  have n1 := cpsBranch_cons_cpsNBranch_with_perm hd_beq0_rest
    (fun h hp => by xperm_hyp hp) beq0f n2
  -- Simplify CR and match goal
  have hcr_eq : cr_beq0.union (cr_cs1.union (cr_cs2.union CodeReq.empty)) = sar_phase_c_code base := by
    simp only [hunion_empty]; rfl
  intro code
  have n1_rw := hcr_eq ▸ n1
  exact cpsNBranch_weaken_posts (cpsNBranch_weaken_pre (fun h hp => by xperm_hyp hp) n1_rw)
    (fun ex hmem => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, List.Mem.head _, rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))), he3.symm, fun h hp => by xperm_hyp hp⟩)

-- ============================================================================
-- Section 6: Helpers for body path composition
-- ============================================================================

-- `cpsNBranch_extend_code` and `cpsNBranch_frameR` live in
-- `Rv64/CPSSpec.lean` (shared).

-- `cpsTriple_strip_pure_and_convert` lives in `Rv64/CPSSpec.lean` (shared).

-- ============================================================================
-- Section 7: SAR Bridge lemmas
-- ============================================================================

-- Merge limb bridge: identical formula to SHR, but for sshiftRight result.
open EvmWord in
private theorem sar_bridge_merge (value : EvmWord) (s0 : Word)
    (result : EvmWord) (hresult : result = BitVec.sshiftRight value s0.toNat)
    (L : Nat) (i : Fin 4)
    (hL : (s0 >>> (6 : BitVec 6).toNat).toNat = L)
    (hiL : i.val + L < 3) (hiL1 : i.val + L + 1 < 4) :
    let bs := s0 &&& signExtend12 63
    let as_ := (64 : Word) - bs
    let mask := (0 : Word) - (if BitVec.ult (0 : Word) bs then (1 : Word) else 0)
    (value.getLimb ⟨i.val + L, by omega⟩ >>> (bs.toNat % 64)) |||
    ((value.getLimb ⟨i.val + L + 1, by omega⟩ <<< (as_.toNat % 64)) &&& mask) =
    getLimb result i := by
  intro bs as_ mask; rw [hresult]
  have hbs_val : bs.toNat = s0.toNat % 64 := by
    simp only [bs, signExtend12_63]
    rw [BitVec.toNat_and, bv64_toNat_63]
    exact Nat.and_two_pow_sub_one_eq_mod s0.toNat 6
  have hbs_lt : bs.toNat < 64 := by omega
  have hL_div : s0.toNat / 64 = L := by
    rw [← hL, bv6_toNat_6]; simp [BitVec.toNat_ushiftRight]; omega
  -- sshiftRight agrees with ushiftRight for merge limbs
  rw [getLimb_sshiftRight_eq_ushiftRight (by omega)]
  rw [getLimb_ushiftRight, hL_div,
      getLimbN_lt value (i.val + L) (by omega),
      getLimbN_lt value (i.val + L + 1) hiL1]
  by_cases hmod0 : s0.toNat % 64 = 0
  · have hmask : mask = 0 := by
      simp only [mask]; have : BitVec.ult (0 : Word) bs = false := by simp [BitVec.ult]; omega
      rw [this]; simp
    simp [hmod0, hmask, show bs.toNat % 64 = 0 from by omega]
  · have hmask : mask = BitVec.allOnes 64 := by
      simp only [mask]; have : BitVec.ult (0 : Word) bs = true := by simp [BitVec.ult]; omega
      rw [this, if_pos rfl]
      show (0 : Word) - 1 = BitVec.allOnes 64; decide
    rw [show bs.toNat % 64 = s0.toNat % 64 from by omega,
        show as_.toNat % 64 = 64 - s0.toNat % 64 from by
          have : as_.toNat = 64 - bs.toNat := by simp only [as_]; bv_omega
          rw [this, hbs_val]; omega,
        hmask, if_neg hmod0]

-- Last limb bridge: for the highest non-zero limb (i+L = 3, SRA instead of SRL).
open EvmWord in
private theorem sar_bridge_last (value : EvmWord) (s0 : Word)
    (result : EvmWord) (hresult : result = BitVec.sshiftRight value s0.toNat)
    (L : Nat) (i : Fin 4)
    (hL : (s0 >>> (6 : BitVec 6).toNat).toNat = L)
    (hiL : i.val + L = 3) :
    let bs := s0 &&& signExtend12 63
    BitVec.sshiftRight (value.getLimb ⟨3, by omega⟩) (bs.toNat % 64) = getLimb result i := by
  intro bs; rw [hresult]
  have hbs_val : bs.toNat = s0.toNat % 64 := by
    simp only [bs, signExtend12_63]
    rw [BitVec.toNat_and, bv64_toNat_63]
    exact Nat.and_two_pow_sub_one_eq_mod s0.toNat 6
  have hL_div : s0.toNat / 64 = L := by
    rw [← hL, bv6_toNat_6]; simp [BitVec.toNat_ushiftRight]; omega
  rw [getLimb_sshiftRight_last (by omega)]
  congr 1; omega

-- Sign limb bridge: for limbs beyond the shift (i+L >= 4, sign extension).
open EvmWord in
private theorem sar_bridge_sign (value : EvmWord) (s0 : Word)
    (result : EvmWord) (hresult : result = BitVec.sshiftRight value s0.toNat)
    (L : Nat) (i : Fin 4)
    (hL : (s0 >>> (6 : BitVec 6).toNat).toNat = L)
    (hiL : i.val + L ≥ 4)
    (bs : Word) (hbs : bs = s0 &&& signExtend12 63) :
    BitVec.sshiftRight (BitVec.sshiftRight (value.getLimb ⟨3, by omega⟩) (bs.toNat % 64)) 63 =
    getLimb result i := by
  rw [hresult]
  have hL_div : s0.toNat / 64 = L := by
    rw [← hL, bv6_toNat_6]; simp [BitVec.toNat_ushiftRight]; omega
  -- getLimb (sshiftRight value n) i = sshiftRight (getLimb value 3) 63 for sign limbs
  rw [getLimb_sshiftRight_sign' (by omega)]
  -- sshiftRight (sshiftRight x bs) 63 = sshiftRight x 63 when bs < 64
  -- Both give sign extension (all bits = MSB of x)
  have hbs_val : bs.toNat = s0.toNat % 64 := by
    subst hbs; simp only [signExtend12_63]
    rw [BitVec.toNat_and, bv64_toNat_63]
    exact Nat.and_two_pow_sub_one_eq_mod s0.toNat 6
  simp only [getLimb]
  ext j
  rename_i hj
  simp only [BitVec.getElem_sshiftRight, BitVec.getElem_extractLsb']
  by_cases h63 : (63 : Nat) + j < 64
  · -- j = 0
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [show (63 + 0 : Nat) < 64 from by omega, dite_true]
    by_cases hbs63 : bs.toNat % 64 + (63 + 0) < 64
    · rw [dif_pos hbs63]; congr 1; omega
    · rw [dif_neg hbs63]
      simp only [BitVec.msb, BitVec.getMsbD, BitVec.getLsbD_extractLsb',
                 show (0 : Nat) < 64 from by omega, show (64 : Nat) - 1 - 0 < 64 from by omega,
                 decide_true, Bool.true_and]
  · -- j >= 1: both sides give msb
    rw [dif_neg h63, dif_neg h63]
    simp [BitVec.msb_sshiftRight]

-- ============================================================================
-- Section 8: Body path composition with evmWordIs postcondition
-- ============================================================================

open EvmWord in
/-- Body path: shift < 256 → result is `sshiftRight value shift.toNat`.
    Composes Phase A ntaken → B → C → body_L → exit and uses
    bridge lemmas to connect per-limb results to the 256-bit arithmetic shift. -/
theorem evm_sar_body_evmWord_spec (sp base : Word)
    (shift value : EvmWord) (r5 r6 r7 r10 r11 : Word)
    (hhigh_zero : shift.getLimb 1 ||| shift.getLimb 2 ||| shift.getLimb 3 = 0)
    (hlt_s0 : BitVec.ult (shift.getLimb 0) (signExtend12 (256 : BitVec 12)) = true)
    (hlt : shift.toNat < 256) :
    cpsTriple base (base + 380) (sarCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
       evmWordIs sp shift ** evmWordIs (sp + 32) value)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
       evmWordIs sp shift ** evmWordIs (sp + 32) (BitVec.sshiftRight value shift.toNat)) := by
  -- Abbreviate shift/value/result limbs
  set s0 := shift.getLimb 0
  set s1 := shift.getLimb 1
  set s2 := shift.getLimb 2
  set s3 := shift.getLimb 3
  set v0 := value.getLimb 0
  set v1 := value.getLimb 1
  set v2 := value.getLimb 2
  set v3 := value.getLimb 3
  set result := BitVec.sshiftRight value shift.toNat
  -- Reduce evmWordIs to raw memIs using suffices
  suffices h_raw : cpsTriple base (base + 380) (sarCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ getLimb result 0) ** ((sp + 40) ↦ₘ getLimb result 1) **
       ((sp + 48) ↦ₘ getLimb result 2) ** ((sp + 56) ↦ₘ getLimb result 3)) by
    exact cpsTriple_weaken
      (fun h hp => by
        unfold evmWordIs at hp
        simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
                   ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3] at hp
        simp only [spAddr32_8, spAddr32_16, spAddr32_24] at hp
        xperm_hyp hp)
      (fun h hq => by
        unfold evmWordIs
        simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
                   ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
        simp only [spAddr32_8, spAddr32_16, spAddr32_24]
        xperm_hyp hq)
      h_raw
  -- Now prove h_raw in flat raw memIs form
  -- Address normalization for sp+32 region
  have ha40 : sp + 40 = (sp + 32 : Word) + 8 := by bv_omega
  have ha48 : sp + 48 = (sp + 32 : Word) + 16 := by bv_omega
  have ha56 : sp + 56 = (sp + 32 : Word) + 24 := by bv_omega
  -- Phase A: linear chain base -> base+36
  have h1 := cpsTriple_extend_code ld_s1_sub_sarCode
    (ld_spec_gen .x5 .x12 sp r5 s1 8 base (by nofun))
  simp only [signExtend12_8] at h1
  have h2 := cpsTriple_extend_code ld_or_16_sub_sarCode
    (shr_ld_or_acc_spec sp s1 r10 s2 16 (base + 4))
  simp only [signExtend12_16] at h2; rw [sar_off_4] at h2
  have h3 := cpsTriple_extend_code ld_or_24_sub_sarCode
    (shr_ld_or_acc_spec sp (s1 ||| s2) s2 s3 24 (base + 12))
  simp only [signExtend12_24] at h3; rw [sar_off_12] at h3
  have h1f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
     (sp ↦ₘ s0) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h1
  have h2f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h2
  have h12 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1f h2f
  have h3f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h3
  have h123 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h12 h3f
  -- BNE at base+20: eliminate TAKEN (s1|||s2|||s3=0 contradicts ne 0)
  have hbne_raw := bne_spec_gen .x5 .x0 332 (s1 ||| s2 ||| s3) (0 : Word) (base + 20)
  rw [sar_bne_target, sar_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code bne_sub_sarCode hbne_raw
  have hbne_ntaken := cpsBranch_ntakenStripPure2 hbne
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hhigh_zero)
  have hbne_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ s3) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbne_ntaken
  have h1234 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h123 hbne_framed
  -- LD x5 x12 0 at base+24
  have hld_raw := ld_spec_gen .x5 .x12 sp (s1 ||| s2 ||| s3) s0 0 (base + 24) (by nofun)
  simp only [signExtend12_0] at hld_raw
  rw [word_add_zero, sar_off_24] at hld_raw
  have hld := cpsTriple_extend_code ld_s0_sub_sarCode hld_raw
  -- SLTIU at base+28
  have hsltiu_raw := sltiu_spec_gen .x10 .x5 s3 s0 256 (base + 28) (by nofun)
  rw [sar_off_28] at hsltiu_raw
  have hsltiu := cpsTriple_extend_code sltiu_sub_sarCode hsltiu_raw
  have hld_f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ s3) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
     ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hld
  have hsltiu_f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hsltiu
  have h56 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hld_f hsltiu_f
  have h123456 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1234 h56
  -- BEQ at base+32: eliminate TAKEN (sltiuVal=1 since s0<256, so 1=0 is absurd)
  let sltiuVal := (if BitVec.ult s0 (signExtend12 (256 : BitVec 12)) then (1 : Word) else (0 : Word))
  have hsltiu_eq : sltiuVal = (1 : Word) := by simp only [sltiuVal, hlt_s0]; decide
  have hbeq_raw := beq_spec_gen .x10 .x0 320 sltiuVal (0 : Word) (base + 32)
  rw [sar_beq_target, sar_off_32] at hbeq_raw
  have hbeq := cpsBranch_extend_code beq_sub_sarCode hbeq_raw
  have hbeq_ntaken := cpsBranch_ntakenStripPure2 hbeq
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      have heq := ((sepConj_pure_right _).mp h_rest).2
      simp [hsltiu_eq] at heq)
  have hbeq_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbeq_ntaken
  have hphaseA := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h123456 hbeq_framed
  -- Phase B: base+36 -> base+64
  let bitShift := s0 &&& signExtend12 63
  let limbShift := s0 >>> (6 : BitVec 6).toNat
  let cond := if BitVec.ult (0 : Word) bitShift then (1 : Word) else 0
  let mask := (0 : Word) - cond
  let antiShift := (64 : Word) - bitShift
  have hphaseB_raw := shr_phase_b_spec s0 sp r6 r7 r11 (base + 36)
  have hphaseB := cpsTriple_extend_code phase_b_sub_sarCode hphaseB_raw
  rw [sar_off_36_28] at hphaseB
  simp only [signExtend12_32] at hphaseB
  have hphaseB_f := cpsTriple_frameR
    ((.x10 ↦ᵣ sltiuVal) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hphaseB
  have hphaseAB := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hphaseA hphaseB_f
  -- Phase C: cascade dispatch at base+64 (with pure dispatch facts)
  have hphaseC_raw := sar_phase_c_spec_pure limbShift sltiuVal (base + 64)
    (base + 252) (base + 172) (base + 116) (base + 84)
    sar_c_e0 sar_c_e1 sar_c_e2 sar_c_e3
  have hphaseC := cpsNBranch_extend_code sar_phase_c_sub_sarCode hphaseC_raw
  -- Body specs extended to sarCode
  have hbody3 := cpsTriple_extend_code sar_body_3_sub_sarCode
    (sar_body_3_spec (sp + 32) limbShift ((0 : Word) + signExtend12 2) bitShift antiShift mask
      v0 v1 v2 v3 (base + 84) (base + 380) 268 sar_body3_exit)
  have hbody2 := cpsTriple_extend_code sar_body_2_sub_sarCode
    (sar_body_2_spec (sp + 32) limbShift ((0 : Word) + signExtend12 2) bitShift antiShift mask
      v0 v1 v2 v3 (base + 116) (base + 380) 212 sar_body2_exit)
  have hbody1 := cpsTriple_extend_code sar_body_1_sub_sarCode
    (sar_body_1_spec (sp + 32) limbShift ((0 : Word) + signExtend12 1) bitShift antiShift mask
      v0 v1 v2 v3 (base + 172) (base + 380) 132 sar_body1_exit)
  have hbody0 := cpsTriple_extend_code sar_body_0_sub_sarCode
    (sar_body_0_spec (sp + 32) limbShift sltiuVal bitShift antiShift mask
      v0 v1 v2 v3 (base + 252) (base + 380) 32 sar_body0_exit)
  -- Frame each body with (x0=0 ** shiftMem)
  have hbody3_f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) hbody3
  have hbody2_f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) hbody2
  have hbody1_f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) hbody1
  have hbody0_f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) hbody0
  have ha40' : (sp + 32 : Word) + 8 = sp + 40 := by bv_omega
  have ha48' : (sp + 32 : Word) + 16 = sp + 48 := by bv_omega
  have ha56' : (sp + 32 : Word) + 24 = sp + 56 := by bv_omega
  simp only [ha40', ha48', ha56'] at hbody3_f hbody2_f hbody1_f hbody0_f
  -- Helper: weaken regs to regOwn while keeping concrete mem values
  have body_post_weaken : ∀ {r5v r6v r7v r10v r11v m32 m40 m48 m56 : Word},
      ∀ h, ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r5v) ** (.x6 ↦ᵣ r6v) ** (.x7 ↦ᵣ r7v) **
            (.x10 ↦ᵣ r10v) ** (.x11 ↦ᵣ r11v) **
            ((sp + 32) ↦ₘ m32) ** ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56) **
            (.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3)) h →
           ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
            (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
            (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
            ((sp + 32) ↦ₘ m32) ** ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56)) h := by
    intro r5v r6v r7v r10v r11v m32 m40 m48 m56 h hp
    have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x5 _)) h hp
    have w2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 _))) h w1
    have w3 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x7 _)))) h w2
    have w4 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _))))) h w3
    have w5 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x11 _)))))) h w4
    exact (congrFun (show _ = _ from by xperm) h).mp w5
  -- Apply weakening to each body (keep concrete mem values)
  have hbody0_w := cpsTriple_weaken
    (fun h hp => hp) (fun h hq => body_post_weaken h (by xperm_hyp hq)) hbody0_f
  have hbody1_w := cpsTriple_weaken
    (fun h hp => hp) (fun h hq => body_post_weaken h (by xperm_hyp hq)) hbody1_f
  have hbody2_w := cpsTriple_weaken
    (fun h hp => hp) (fun h hq => body_post_weaken h (by xperm_hyp hq)) hbody2_f
  have hbody3_w := cpsTriple_weaken
    (fun h hp => hp) (fun h hq => body_post_weaken h (by xperm_hyp hq)) hbody3_f
  -- Bitvector bridge: common facts
  have hshift_toNat : shift.toNat = s0.toNat :=
    EvmWord.toNat_eq_getLimb0_of_high_zero hhigh_zero
  -- Body bridge specs: use cpsTriple_strip_pure_and_convert to thread pure dispatch fact
  let resultPost :=
    (.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
     (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ getLimb result 0) ** ((sp + 40) ↦ₘ getLimb result 1) **
     ((sp + 48) ↦ₘ getLimb result 2) ** ((sp + 56) ↦ₘ getLimb result 3)
  -- Body 0 (L=0): merge(0,1,2) + last(3)
  have hbody0_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbody0_w (fun (hls : limbShift = 0) h hq => by
      have hresult : result = BitVec.sshiftRight value s0.toNat := by
        show BitVec.sshiftRight value shift.toNat = BitVec.sshiftRight value s0.toNat; congr 1
      have hL : (s0 >>> (6 : BitVec 6).toNat).toNat = 0 := congrArg BitVec.toNat hls
      have eq0 := sar_bridge_merge value s0 result hresult 0 0 hL (by omega) (by omega)
      have eq1 := sar_bridge_merge value s0 result hresult 0 1 hL (by omega) (by omega)
      have eq2 := sar_bridge_merge value s0 result hresult 0 2 hL (by omega) (by omega)
      have eq3 := sar_bridge_last value s0 result hresult 0 3 hL (by omega)
      show ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
           (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
           ((sp + 32) ↦ₘ getLimb result 0) ** ((sp + 40) ↦ₘ getLimb result 1) **
           ((sp + 48) ↦ₘ getLimb result 2) ** ((sp + 56) ↦ₘ getLimb result 3)) h
      rw [← eq0, ← eq1, ← eq2, ← eq3]; exact hq)
  -- Body 1 (L=1): merge(0,1) + last(2) + sign(3)
  have hbody1_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbody1_w (fun (hls : limbShift = (0 : Word) + signExtend12 1) h hq => by
      have hresult : result = BitVec.sshiftRight value s0.toNat := by
        show BitVec.sshiftRight value shift.toNat = BitVec.sshiftRight value s0.toNat; congr 1
      have hL : (s0 >>> (6 : BitVec 6).toNat).toNat = 1 := by
        have := congrArg BitVec.toNat hls
        simp only [zero_add_se12_1_toNat] at this
        exact this
      have eq0 := sar_bridge_merge value s0 result hresult 1 0 hL (by omega) (by omega)
      have eq1 := sar_bridge_merge value s0 result hresult 1 1 hL (by omega) (by omega)
      have eq2 := sar_bridge_last value s0 result hresult 1 2 hL (by omega)
      have eq3 := sar_bridge_sign value s0 result hresult 1 3 hL (by omega) bitShift rfl
      show ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
           (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
           ((sp + 32) ↦ₘ getLimb result 0) ** ((sp + 40) ↦ₘ getLimb result 1) **
           ((sp + 48) ↦ₘ getLimb result 2) ** ((sp + 56) ↦ₘ getLimb result 3)) h
      rw [← eq0, ← eq1, ← eq2, ← eq3]; exact hq)
  -- Body 2 (L=2): merge(0) + last(1) + sign(2,3)
  have hbody2_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbody2_w (fun (hls : limbShift = (0 : Word) + signExtend12 2) h hq => by
      have hresult : result = BitVec.sshiftRight value s0.toNat := by
        show BitVec.sshiftRight value shift.toNat = BitVec.sshiftRight value s0.toNat; congr 1
      have hL : (s0 >>> (6 : BitVec 6).toNat).toNat = 2 := by
        have := congrArg BitVec.toNat hls
        simp only [zero_add_se12_2_toNat] at this
        exact this
      have eq0 := sar_bridge_merge value s0 result hresult 2 0 hL (by omega) (by omega)
      have eq1 := sar_bridge_last value s0 result hresult 2 1 hL (by omega)
      have eq2 := sar_bridge_sign value s0 result hresult 2 2 hL (by omega) bitShift rfl
      have eq3 := sar_bridge_sign value s0 result hresult 2 3 hL (by omega) bitShift rfl
      show ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
           (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
           ((sp + 32) ↦ₘ getLimb result 0) ** ((sp + 40) ↦ₘ getLimb result 1) **
           ((sp + 48) ↦ₘ getLimb result 2) ** ((sp + 56) ↦ₘ getLimb result 3)) h
      rw [← eq0, ← eq1, ← eq2, ← eq3]; exact hq)
  -- Body 3 (L=3): last(0) + sign(1,2,3)
  have hbody3_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbody3_w (fun (hls : limbShift ≠ 0 ∧ limbShift ≠ (0 : Word) + signExtend12 1 ∧
                limbShift ≠ (0 : Word) + signExtend12 2) h hq => by
      have hresult : result = BitVec.sshiftRight value s0.toNat := by
        show BitVec.sshiftRight value shift.toNat = BitVec.sshiftRight value s0.toNat; congr 1
      have hL : (s0 >>> (6 : BitVec 6).toNat).toNat = 3 := by
        obtain ⟨h0, h1, h2⟩ := hls
        have hlt4 : limbShift.toNat < 4 := by
          show (s0 >>> (6 : BitVec 6).toNat).toNat < 4
          rw [bv6_toNat_6]; simp [BitVec.toNat_ushiftRight]; omega
        have hn0 : limbShift.toNat ≠ 0 :=
          fun hc => h0 (BitVec.eq_of_toNat_eq (by simpa using hc))
        have hn1 : limbShift.toNat ≠ 1 :=
          fun hc => h1 (BitVec.eq_of_toNat_eq (by
            show limbShift.toNat = ((0 : Word) + signExtend12 1).toNat
            simp only [zero_add_se12_1_toNat]
            exact hc))
        have hn2 : limbShift.toNat ≠ 2 :=
          fun hc => h2 (BitVec.eq_of_toNat_eq (by
            show limbShift.toNat = ((0 : Word) + signExtend12 2).toNat
            simp only [zero_add_se12_2_toNat]
            exact hc))
        show limbShift.toNat = 3; omega
      have eq0 := sar_bridge_last value s0 result hresult 3 0 hL (by omega)
      have eq1 := sar_bridge_sign value s0 result hresult 3 1 hL (by omega) bitShift rfl
      have eq2 := sar_bridge_sign value s0 result hresult 3 2 hL (by omega) bitShift rfl
      have eq3 := sar_bridge_sign value s0 result hresult 3 3 hL (by omega) bitShift rfl
      show ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
           (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
           ((sp + 32) ↦ₘ getLimb result 0) ** ((sp + 40) ↦ₘ getLimb result 1) **
           ((sp + 48) ↦ₘ getLimb result 2) ** ((sp + 56) ↦ₘ getLimb result 3)) h
      rw [← eq0, ← eq1, ← eq2, ← eq3]; exact hq)
  -- Frame Phase C and merge with body specs
  have hphaseC_framed := cpsNBranch_frameR
    (F := (.x6 ↦ᵣ bitShift) ** (.x7 ↦ᵣ antiShift) ** (.x11 ↦ᵣ mask) ** (.x12 ↦ᵣ (sp + 32)) **
          (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
          ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hphaseC
  simp only [List.map] at hphaseC_framed
  -- Merge Phase C + bodies
  have hphaseCD := cpsNBranch_merge hphaseC_framed
    (fun exit hmem => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact cpsTriple_weaken
          (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hbody0_ev
      · exact cpsTriple_weaken
          (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hbody1_ev
      · exact cpsTriple_weaken
          (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hbody2_ev
      · exact cpsTriple_weaken
          (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hbody3_ev)
  -- Flatten hphaseAB postcondition for composition
  have hphaseAB' : cpsTriple base (base + 64) (sarCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x5 ↦ᵣ limbShift) ** (.x6 ↦ᵣ bitShift) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ mask) ** (.x7 ↦ᵣ antiShift) ** (.x12 ↦ᵣ (sp + 32)) **
       (.x10 ↦ᵣ sltiuVal) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) :=
    cpsTriple_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      hphaseAB
  -- Final: Phase AB -> Phase CD
  exact cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hphaseAB' hphaseCD

end EvmAsm.Evm64
