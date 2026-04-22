/-
  EvmAsm.Evm64.Shift.ShlCompose

  Hierarchical composition of SHL CPS specs into a single full-program theorem.
  Composes the 5 execution paths through `evm_shl` (90 instructions, 360 bytes):
  - Zero path (shift ≥ 256): Phase A taken → zero_path
  - Body L (L=0..3, shift < 256): Phase A ntaken → B → C(exit L) → body_L → exit

  Mirrors Compose.lean (SHR) with SHL body specs and bridge lemmas.
-/

import EvmAsm.Evm64.Shift.ShlSpec
import EvmAsm.Evm64.Shift.ComposeBase
import EvmAsm.Evm64.SpAddr
import Mathlib.Tactic.Set

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm
  (zero_add_se12_1_toNat zero_add_se12_2_toNat bv6_toNat_6 bv64_toNat_63 word_add_zero)

-- ============================================================================
-- Section 1: shlCode definition and helpers
-- ============================================================================

-- Shared SHR sub-program length lemmas live in `ComposeBase`.
-- SHL-specific body length lemmas remain local.
private theorem shl_body_3_prog_len : (shl_body_3_prog 252).length = 7 := by decide
private theorem shl_body_2_prog_len : (shl_body_2_prog 200).length = 13 := by decide
private theorem shl_body_1_prog_len : (shl_body_1_prog 124).length = 19 := by decide
private theorem shl_body_0_prog_len : (shl_body_0_prog 24).length = 25 := by decide

/-- Skip one ofProg block in a right-nested union via range disjointness. -/
local macro "skipBlock" : tactic =>
  `(tactic| apply CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
        simp only [shr_phase_a_len, shr_phase_b_len, shr_phase_c_len,
          shl_body_3_prog_len, shl_body_2_prog_len, shl_body_1_prog_len,
          shl_body_0_prog_len, shr_zero_path_len] at hk1 hk2
        bv_omega)))

/-- The full evm_shl code split into 8 per-phase CodeReq.ofProg blocks. -/
abbrev shlCode (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base shr_phase_a,                      -- block 0 (shared with SHR)
    CodeReq.ofProg (base + 36) shr_phase_b,               -- block 1 (shared)
    CodeReq.ofProg (base + 64) shr_phase_c,               -- block 2 (shared)
    CodeReq.ofProg (base + 84) (shl_body_3_prog 252),     -- block 3
    CodeReq.ofProg (base + 112) (shl_body_2_prog 200),    -- block 4
    CodeReq.ofProg (base + 164) (shl_body_1_prog 124),    -- block 5
    CodeReq.ofProg (base + 240) (shl_body_0_prog 24),     -- block 6
    CodeReq.ofProg (base + 340) shr_zero_path              -- block 7 (shared)
  ]

-- `regIs_to_regOwn`, `CodeReq_union_sub_both`, `singleton_sub_ofProg` now live
-- in `EvmAsm.Evm64.Shift.ComposeBase` (shared across SHR/SHL/SAR).

-- ============================================================================
-- Section 2: Subsumption lemmas (via unionAll structural reasoning)
-- ============================================================================

-- Phase A union-chain ⊆ ofProg bridge (`shr_phase_a_code_sub_ofProg`) is shared
-- and lives in `ComposeBase`.

/-- Phase B code (ofProg, 7 instrs at +36) is subsumed by shlCode (block 1). -/
private theorem phase_b_sub_shlCode (base : Word) :
    ∀ a i, shr_phase_b_code (base + 36) a = some i → shlCode base a = some i := by
  unfold shr_phase_b_code shlCode; simp only [CodeReq.unionAll_cons]
  skipBlock
  exact CodeReq.union_mono_left _ _

-- Phase C union-chain ⊆ ofProg bridge (`shr_phase_c_code_sub_ofProg`) is shared
-- and lives in `ComposeBase`.

private theorem ofProg_phase_c_sub_shlCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 64) shr_phase_c) a = some i → shlCode base a = some i := by
  unfold shlCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Phase C code (union chain, 5 instrs at +64) is subsumed by shlCode (block 2). -/
private theorem phase_c_sub_shlCode (base : Word) :
    ∀ a i, shr_phase_c_code (base + 64) a = some i → shlCode base a = some i := by
  intro a i h
  exact ofProg_phase_c_sub_shlCode base a i (shr_phase_c_code_sub_ofProg a i h)

/-- SHL Body 3 code (7 instrs at +84) is subsumed by shlCode (block 3). -/
private theorem shl_body_3_sub_shlCode (base : Word) :
    ∀ a i, shl_body_3_code (base + 84) 252 a = some i → shlCode base a = some i := by
  unfold shl_body_3_code shlCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- SHL Body 2 code (13 instrs at +112) is subsumed by shlCode (block 4). -/
private theorem shl_body_2_sub_shlCode (base : Word) :
    ∀ a i, shl_body_2_code (base + 112) 200 a = some i → shlCode base a = some i := by
  unfold shl_body_2_code shlCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- SHL Body 1 code (19 instrs at +164) is subsumed by shlCode (block 5). -/
private theorem shl_body_1_sub_shlCode (base : Word) :
    ∀ a i, shl_body_1_code (base + 164) 124 a = some i → shlCode base a = some i := by
  unfold shl_body_1_code shlCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- SHL Body 0 code (25 instrs at +240) is subsumed by shlCode (block 6). -/
private theorem shl_body_0_sub_shlCode (base : Word) :
    ∀ a i, shl_body_0_code (base + 240) 24 a = some i → shlCode base a = some i := by
  unfold shl_body_0_code shlCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Zero path code (ofProg, 5 instrs at +340) is subsumed by shlCode (block 7). -/
private theorem zero_path_sub_shlCode (base : Word) :
    ∀ a i, shr_zero_path_code (base + 340) a = some i → shlCode base a = some i := by
  unfold shr_zero_path_code shlCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

-- Individual instruction subsumption helpers (for phase A raw composition)

private theorem ld_s1_sub_shlCode (base : Word) :
    ∀ a i, CodeReq.singleton base (.LD .x5 .x12 8) a = some i → shlCode base a = some i := by
  intro a i h
  have h1 := singleton_sub_ofProg base base shr_phase_a (.LD .x5 .x12 8) 0
    (by decide) (by decide) (by bv_omega) (by decide) a i h
  unfold shlCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

private theorem ld_or_16_sub_shlCode (base : Word) :
    ∀ a i, shr_ld_or_acc_code 16 (base + 4) a = some i → shlCode base a = some i := by
  intro a i h; unfold shr_ld_or_acc_code at h
  have h1 := CodeReq.ofProg_mono_sub base (base + 4) shr_phase_a (shr_ld_or_acc_prog 16) 1
    (by bv_omega) (by decide) (by decide) (by decide) a i h
  unfold shlCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

private theorem ld_or_24_sub_shlCode (base : Word) :
    ∀ a i, shr_ld_or_acc_code 24 (base + 12) a = some i → shlCode base a = some i := by
  intro a i h; unfold shr_ld_or_acc_code at h
  have h1 := CodeReq.ofProg_mono_sub base (base + 12) shr_phase_a (shr_ld_or_acc_prog 24) 3
    (by bv_omega) (by decide) (by decide) (by decide) a i h
  unfold shlCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

private theorem bne_sub_shlCode (base : Word) :
    ∀ a i, CodeReq.singleton (base + 20) (.BNE .x5 .x0 320) a = some i → shlCode base a = some i := by
  intro a i h
  have h1 := singleton_sub_ofProg base (base + 20) shr_phase_a (.BNE .x5 .x0 320) 5
    (by decide) (by decide) (by bv_omega) (by decide) a i h
  unfold shlCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

private theorem ld_s0_sub_shlCode (base : Word) :
    ∀ a i, CodeReq.singleton (base + 24) (.LD .x5 .x12 0) a = some i → shlCode base a = some i := by
  intro a i h
  have h1 := singleton_sub_ofProg base (base + 24) shr_phase_a (.LD .x5 .x12 0) 6
    (by decide) (by decide) (by bv_omega) (by decide) a i h
  unfold shlCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

private theorem sltiu_sub_shlCode (base : Word) :
    ∀ a i, CodeReq.singleton (base + 28) (.SLTIU .x10 .x5 256) a = some i → shlCode base a = some i := by
  intro a i h
  have h1 := singleton_sub_ofProg base (base + 28) shr_phase_a (.SLTIU .x10 .x5 256) 7
    (by decide) (by decide) (by bv_omega) (by decide) a i h
  unfold shlCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

private theorem beq_sub_shlCode (base : Word) :
    ∀ a i, CodeReq.singleton (base + 32) (.BEQ .x10 .x0 308) a = some i → shlCode base a = some i := by
  intro a i h
  have h1 := singleton_sub_ofProg base (base + 32) shr_phase_a (.BEQ .x10 .x0 308) 8
    (by decide) (by decide) (by bv_omega) (by decide) a i h
  unfold shlCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _ a i h1

-- ============================================================================
-- Section 3: Address normalization lemmas
-- ============================================================================

private theorem shl_off_4 {base : Word} : (base + 4 : Word) + 8 = base + 12 := by bv_omega
private theorem shl_off_12 {base : Word} : (base + 12 : Word) + 8 = base + 20 := by bv_omega
private theorem shl_off_20 {base : Word} : (base + 20 : Word) + 4 = base + 24 := by bv_omega
private theorem shl_off_24 {base : Word} : (base + 24 : Word) + 4 = base + 28 := by bv_omega
private theorem shl_off_28 {base : Word} : (base + 28 : Word) + 4 = base + 32 := by bv_omega
private theorem shl_off_32 {base : Word} : (base + 32 : Word) + 4 = base + 36 := by bv_omega
private theorem shl_off_36_28 {base : Word} : (base + 36 : Word) + 28 = base + 64 := by bv_omega
private theorem shl_off_340_20 {base : Word} : (base + 340 : Word) + 20 = base + 360 := by bv_omega
private theorem shl_bne_target {base : Word} : (base + 20 : Word) + signExtend13 320 = base + 340 := by
  rv64_addr
private theorem shl_beq_target {base : Word} : (base + 32 : Word) + signExtend13 308 = base + 340 := by
  rv64_addr
-- Phase C exit addresses
private theorem shl_c_e0 (base : Word) : (base + 64 : Word) + signExtend13 176 = base + 240 := by
  rv64_addr
private theorem shl_c_e1 (base : Word) : ((base + 64 : Word) + 8) + signExtend13 92 = base + 164 := by
  rv64_addr
private theorem shl_c_e2 (base : Word) : ((base + 64 : Word) + 16) + signExtend13 32 = base + 112 := by
  rv64_addr
private theorem shl_c_e3 (base : Word) : (base + 64 : Word) + 20 = base + 84 := by bv_omega
-- Body exit addresses (JAL targets)
private theorem shl_body3_exit (base : Word) : ((base + 84 : Word) + 24) + signExtend21 252 = base + 360 := by
  rv64_addr
private theorem shl_body2_exit (base : Word) : ((base + 112 : Word) + 48) + signExtend21 200 = base + 360 := by
  rv64_addr
private theorem shl_body1_exit (base : Word) : ((base + 164 : Word) + 72) + signExtend21 124 = base + 360 := by
  rv64_addr
private theorem shl_body0_exit (base : Word) : ((base + 240 : Word) + 96) + signExtend21 24 = base + 360 := by
  rv64_addr

-- ============================================================================
-- Section 4: Zero path composition
-- ============================================================================

/-- Zero path via BNE taken: high shift limbs are nonzero → shift ≥ 256 → result is zero. -/
theorem evm_shl_zero_high_spec (sp base : Word)
    (s0 s1 s2 s3 v0 v1 v2 v3 r5 r10 : Word)
    (hhigh : s1 ||| s2 ||| s3 ≠ 0) :
    cpsTriple base (base + 360) (shlCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  -- Step 1: LD x5 x12 8 at base → extend to shlCode
  have h1 := cpsTriple_extend_code (ld_s1_sub_shlCode base)
    (ld_spec_gen .x5 .x12 sp r5 s1 8 base (by nofun))
  simp only [signExtend12_8] at h1
  -- Step 2: LD/OR at base+4 → extend to shlCode
  have h2 := cpsTriple_extend_code (ld_or_16_sub_shlCode base)
    (shr_ld_or_acc_spec sp s1 r10 s2 16 (base + 4))
  simp only [signExtend12_16] at h2
  rw [shl_off_4] at h2
  -- Step 3: LD/OR at base+12 → extend to shlCode
  have h3 := cpsTriple_extend_code (ld_or_24_sub_shlCode base)
    (shr_ld_or_acc_spec sp (s1 ||| s2) s2 s3 24 (base + 12))
  simp only [signExtend12_24] at h3
  rw [shl_off_12] at h3
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
  -- Step 4: BNE at base+20 → extend to shlCode, eliminate ntaken
  have hbne_raw := bne_spec_gen .x5 .x0 320 (s1 ||| s2 ||| s3) (0 : Word) (base + 20)
  rw [shl_bne_target, shl_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code (bne_sub_shlCode base) hbne_raw
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
  -- Step 5: Zero path (base+340 → base+360) → extend to shlCode
  have hzp := cpsTriple_extend_code (zero_path_sub_shlCode base)
    (shr_zero_path_spec sp v0 v1 v2 v3 (base + 340))
  rw [shl_off_340_20] at hzp
  -- Frame zero path with remaining state
  have hzp_framed := cpsTriple_frameR
    ((.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ s3) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) hzp
  -- Address normalization lemmas
  have ha40 : sp + 40 = (sp + 32 : Word) + 8 := by bv_omega
  have ha48 : sp + 48 = (sp + 32 : Word) + 16 := by bv_omega
  have ha56 : sp + 56 = (sp + 32 : Word) + 24 := by bv_omega
  have ha40' : (sp + 32 : Word) + 8 = sp + 40 := by bv_omega
  have ha48' : (sp + 32 : Word) + 16 = sp + 48 := by bv_omega
  have ha56' : (sp + 32 : Word) + 24 = sp + 56 := by bv_omega
  -- Compose AB → ZP: normalize addresses in perm callback
  have hABZ := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      simp only [ha40, ha48, ha56] at hp
      xperm_hyp hp) hAB hzp_framed
  -- Final: normalize addresses back + weaken regs to regOwn
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      simp only [ha40', ha48', ha56'] at hq
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (.x10 ↦ᵣ s3) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    hABZ

/-- Zero path via BEQ taken: s1=s2=s3=0 but s0 ≥ 256 → result is zero. -/
theorem evm_shl_zero_large_spec (sp base : Word)
    (s0 s1 s2 s3 v0 v1 v2 v3 r5 r10 : Word)
    (hlow : s1 ||| s2 ||| s3 = 0)
    (hlarge : BitVec.ult s0 (signExtend12 (256 : BitVec 12)) = false) :
    cpsTriple base (base + 360) (shlCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  -- Steps 1-3: Same linear chain as zero_high
  have h1 := cpsTriple_extend_code (ld_s1_sub_shlCode base)
    (ld_spec_gen .x5 .x12 sp r5 s1 8 base (by nofun))
  simp only [signExtend12_8] at h1
  have h2 := cpsTriple_extend_code (ld_or_16_sub_shlCode base)
    (shr_ld_or_acc_spec sp s1 r10 s2 16 (base + 4))
  simp only [signExtend12_16] at h2; rw [shl_off_4] at h2
  have h3 := cpsTriple_extend_code (ld_or_24_sub_shlCode base)
    (shr_ld_or_acc_spec sp (s1 ||| s2) s2 s3 24 (base + 12))
  simp only [signExtend12_24] at h3; rw [shl_off_12] at h3
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
  -- Step 4: BNE at base+20 → eliminate TAKEN (s1|||s2|||s3 = 0 contradicts ≠ 0)
  have hbne_raw := bne_spec_gen .x5 .x0 320 (s1 ||| s2 ||| s3) (0 : Word) (base + 20)
  rw [shl_bne_target, shl_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code (bne_sub_shlCode base) hbne_raw
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
  -- Step 5: LD x5 x12 0 at base+24 → extend to shlCode
  have hld_raw := ld_spec_gen .x5 .x12 sp (s1 ||| s2 ||| s3) s0 0 (base + 24) (by nofun)
  simp only [signExtend12_0] at hld_raw
  rw [word_add_zero, shl_off_24] at hld_raw
  have hld := cpsTriple_extend_code (ld_s0_sub_shlCode base) hld_raw
  -- Step 6: SLTIU at base+28 → extend to shlCode
  have hsltiu_raw := sltiu_spec_gen .x10 .x5 s3 s0 256 (base + 28) (by nofun)
  rw [shl_off_28] at hsltiu_raw
  have hsltiu := cpsTriple_extend_code (sltiu_sub_shlCode base) hsltiu_raw
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
  -- Step 7: BEQ at base+32 → eliminate ntaken (sltiuVal = 0 since s0 ≥ 256)
  let sltiuVal := (if BitVec.ult s0 (signExtend12 (256 : BitVec 12)) then (1 : Word) else (0 : Word))
  have hbeq_raw := beq_spec_gen .x10 .x0 308 sltiuVal (0 : Word) (base + 32)
  rw [shl_beq_target, shl_off_32] at hbeq_raw
  have hbeq := cpsBranch_extend_code (beq_sub_shlCode base) hbeq_raw
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
  -- Step 8: Zero path (base+340 → base+360)
  have hzp := cpsTriple_extend_code (zero_path_sub_shlCode base)
    (shr_zero_path_spec sp v0 v1 v2 v3 (base + 340))
  rw [shl_off_340_20] at hzp
  have hzp_framed := cpsTriple_frameR
    ((.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ sltiuVal) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) hzp
  -- Address normalization lemmas
  have ha40 : sp + 40 = (sp + 32 : Word) + 8 := by bv_omega
  have ha48 : sp + 48 = (sp + 32 : Word) + 16 := by bv_omega
  have ha56 : sp + 56 = (sp + 32 : Word) + 24 := by bv_omega
  have ha40' : (sp + 32 : Word) + 8 = sp + 40 := by bv_omega
  have ha48' : (sp + 32 : Word) + 16 = sp + 48 := by bv_omega
  have ha56' : (sp + 32 : Word) + 24 = sp + 56 := by bv_omega
  -- Compose → ZP: normalize addresses in perm callback
  have hfull := cpsTriple_seq_perm_same_cr (fun h hp => by
      simp only [ha40, ha48, ha56] at hp
      xperm_hyp hp) h1234567 hzp_framed
  -- Final: normalize addresses back + weaken regs to regOwn
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      simp only [ha40', ha48', ha56'] at hq
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ s0) ** (.x10 ↦ᵣ sltiuVal) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    hfull

-- ============================================================================
-- Section 5: Bridge lemmas
-- ============================================================================

-- Helpers for extending code requirements to cpsNBranch

-- `cpsNBranch_extend_code` and `cpsNBranch_frameR` live in
-- `Rv64/CPSSpec.lean` (shared).

-- `cpsTriple_strip_pure_and_convert` lives in `Rv64/CPSSpec.lean` (shared).

-- ============================================================================
-- SHL Bridge lemmas: connect per-limb body outputs to getLimb (value <<< n)
-- ============================================================================

-- Merge limb bridge: for limbs i where i > L (i-L and i-L-1 are both valid source limbs).
open EvmWord in
private theorem shl_bridge_merge (value : EvmWord) (s0 : Word)
    (result : EvmWord) (hresult : result = value <<< s0.toNat)
    (L : Nat) (i : Fin 4)
    (hL : (s0 >>> (6 : BitVec 6).toNat).toNat = L)
    (hiL : i.val ≥ L + 1) (hiLsub : i.val - L < 4) (hiLsub1 : i.val - L - 1 < 4) :
    let bs := s0 &&& signExtend12 63
    let as_ := (64 : Word) - bs
    let mask := (0 : Word) - (if BitVec.ult (0 : Word) bs then (1 : Word) else 0)
    (value.getLimb ⟨i.val - L, by omega⟩ <<< (bs.toNat % 64)) |||
    ((value.getLimb ⟨i.val - L - 1, by omega⟩ >>> (as_.toNat % 64)) &&& mask) =
    getLimb result i := by
  intro bs as_ mask; rw [hresult]
  have hbs_val : bs.toNat = s0.toNat % 64 := by
    simp only [bs, signExtend12_63]
    rw [BitVec.toNat_and, bv64_toNat_63]
    exact Nat.and_two_pow_sub_one_eq_mod s0.toNat 6
  have hbs_lt : bs.toNat < 64 := by omega
  have hL_div : s0.toNat / 64 = L := by
    rw [← hL, bv6_toNat_6]; simp [BitVec.toNat_ushiftRight]; omega
  -- Use getLimb_shiftLeft: i*64 >= s0.toNat since i >= L+1 and s0.toNat = L*64 + bs < (L+1)*64
  rw [getLimb_shiftLeft (by omega), hL_div,
      getLimbN_lt value (i.val - L) hiLsub,
      getLimbN_lt value (i.val - L - 1) hiLsub1]
  -- Now match the masks and shift amounts
  by_cases hmod0 : s0.toNat % 64 = 0
  · -- bs = 0 case: mask = 0, helper mask = 0
    have hmask : mask = 0 := by
      simp only [mask]; have : BitVec.ult (0 : Word) bs = false := by simp [BitVec.ult]; omega
      rw [this]; simp
    simp [hmod0, hmask, show bs.toNat % 64 = 0 from by omega]
  · -- bs > 0 case: mask = allOnes 64, helper mask = allOnes 64
    have hmask : mask = BitVec.allOnes 64 := by
      simp only [mask]; have : BitVec.ult (0 : Word) bs = true := by simp [BitVec.ult]; omega
      rw [this, if_pos rfl]
      show (0 : Word) - 1 = BitVec.allOnes 64; decide
    rw [show bs.toNat % 64 = s0.toNat % 64 from by omega,
        show as_.toNat % 64 = 64 - s0.toNat % 64 from by
          have : as_.toNat = 64 - bs.toNat := by simp only [as_]; bv_omega
          rw [this, hbs_val]; omega,
        hmask, if_neg hmod0]

-- First limb bridge: for the lowest non-zero limb (i = L, only SLL).
open EvmWord in
private theorem shl_bridge_first (value : EvmWord) (s0 : Word)
    (result : EvmWord) (hresult : result = value <<< s0.toNat)
    (L : Nat) (i : Fin 4)
    (hL : (s0 >>> (6 : BitVec 6).toNat).toNat = L)
    (hiL : i.val = L) :
    let bs := s0 &&& signExtend12 63
    value.getLimb ⟨0, by omega⟩ <<< (bs.toNat % 64) = getLimb result i := by
  intro bs; rw [hresult]
  have hbs_val : bs.toNat = s0.toNat % 64 := by
    simp only [bs, signExtend12_63]
    rw [BitVec.toNat_and, bv64_toNat_63]
    exact Nat.and_two_pow_sub_one_eq_mod s0.toNat 6
  have hL_div : s0.toNat / 64 = L := by
    rw [← hL, bv6_toNat_6]; simp [BitVec.toNat_ushiftRight]; omega
  -- Use getLimb_shiftLeft_eq_div: i.val = n / 64
  rw [getLimb_shiftLeft_eq_div (by omega)]
  -- getLimbN v 0 = getLimb v ⟨0, _⟩
  rw [getLimbN_lt value 0 (by omega)]
  -- Shift amounts match: bs.toNat % 64 = s0.toNat % 64
  congr 1; omega

-- Zero limb bridge: for limbs below the shift (i < L, result is 0).
open EvmWord in
private theorem shl_bridge_zero (value : EvmWord) (s0 : Word)
    (result : EvmWord) (hresult : result = value <<< s0.toNat)
    (L : Nat) (i : Fin 4)
    (hL : (s0 >>> (6 : BitVec 6).toNat).toNat = L)
    (hiL : i.val < L) :
    getLimb result i = 0 := by
  rw [hresult]
  have hL_div : s0.toNat / 64 = L := by
    rw [← hL, bv6_toNat_6]; simp [BitVec.toNat_ushiftRight]; omega
  -- Use getLimb_shiftLeft_low: (i+1)*64 <= s0.toNat since i < L and s0.toNat >= L*64
  exact getLimb_shiftLeft_low (by omega)

-- ============================================================================
-- Section 6: Body path composition with evmWordIs postcondition
-- ============================================================================

open EvmWord in
/-- Body path: shift < 256 → result is `value <<< shift.toNat`.
    Composes Phase A ntaken → B → C → body_L → exit and uses
    bridge lemmas to connect per-limb results to the 256-bit shift. -/
theorem evm_shl_body_evmWord_spec (sp base : Word)
    (shift value : EvmWord) (r5 r6 r7 r10 r11 : Word)
    (hhigh_zero : shift.getLimb 1 ||| shift.getLimb 2 ||| shift.getLimb 3 = 0)
    (hlt_s0 : BitVec.ult (shift.getLimb 0) (signExtend12 (256 : BitVec 12)) = true)
    (hlt : shift.toNat < 256) :
    cpsTriple base (base + 360) (shlCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
       evmWordIs sp shift ** evmWordIs (sp + 32) value)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
       evmWordIs sp shift ** evmWordIs (sp + 32) (value <<< shift.toNat)) := by
  -- Abbreviate shift/value/result limbs
  set s0 := shift.getLimb 0
  set s1 := shift.getLimb 1
  set s2 := shift.getLimb 2
  set s3 := shift.getLimb 3
  set v0 := value.getLimb 0
  set v1 := value.getLimb 1
  set v2 := value.getLimb 2
  set v3 := value.getLimb 3
  set result := value <<< shift.toNat
  -- Reduce evmWordIs to raw memIs using suffices
  suffices h_raw : cpsTriple base (base + 360) (shlCode base)
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
  have h1 := cpsTriple_extend_code (ld_s1_sub_shlCode base)
    (ld_spec_gen .x5 .x12 sp r5 s1 8 base (by nofun))
  simp only [signExtend12_8] at h1
  have h2 := cpsTriple_extend_code (ld_or_16_sub_shlCode base)
    (shr_ld_or_acc_spec sp s1 r10 s2 16 (base + 4))
  simp only [signExtend12_16] at h2; rw [shl_off_4] at h2
  have h3 := cpsTriple_extend_code (ld_or_24_sub_shlCode base)
    (shr_ld_or_acc_spec sp (s1 ||| s2) s2 s3 24 (base + 12))
  simp only [signExtend12_24] at h3; rw [shl_off_12] at h3
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
  have hbne_raw := bne_spec_gen .x5 .x0 320 (s1 ||| s2 ||| s3) (0 : Word) (base + 20)
  rw [shl_bne_target, shl_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code (bne_sub_shlCode base) hbne_raw
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
  rw [word_add_zero, shl_off_24] at hld_raw
  have hld := cpsTriple_extend_code (ld_s0_sub_shlCode base) hld_raw
  -- SLTIU at base+28
  have hsltiu_raw := sltiu_spec_gen .x10 .x5 s3 s0 256 (base + 28) (by nofun)
  rw [shl_off_28] at hsltiu_raw
  have hsltiu := cpsTriple_extend_code (sltiu_sub_shlCode base) hsltiu_raw
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
  have hbeq_raw := beq_spec_gen .x10 .x0 308 sltiuVal (0 : Word) (base + 32)
  rw [shl_beq_target, shl_off_32] at hbeq_raw
  have hbeq := cpsBranch_extend_code (beq_sub_shlCode base) hbeq_raw
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
  have hphaseB := cpsTriple_extend_code (phase_b_sub_shlCode base) hphaseB_raw
  rw [shl_off_36_28] at hphaseB
  simp only [signExtend12_32] at hphaseB
  have hphaseB_f := cpsTriple_frameR
    ((.x10 ↦ᵣ sltiuVal) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hphaseB
  have hphaseAB := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hphaseA hphaseB_f
  -- Phase C: cascade dispatch at base+64 (with pure dispatch facts)
  have hphaseC_raw := shr_phase_c_spec_pure limbShift sltiuVal (base + 64)
    (base + 240) (base + 164) (base + 112) (base + 84)
    (shl_c_e0 base) (shl_c_e1 base) (shl_c_e2 base) (shl_c_e3 base)
  have hphaseC := cpsNBranch_extend_code (phase_c_sub_shlCode base) hphaseC_raw
  -- Body specs extended to shlCode
  have hbody3 := cpsTriple_extend_code (shl_body_3_sub_shlCode base)
    (shl_body_3_spec (sp + 32) limbShift ((0 : Word) + signExtend12 2) bitShift antiShift mask
      v0 v1 v2 v3 (base + 84) (base + 360) 252 (shl_body3_exit base))
  have hbody2 := cpsTriple_extend_code (shl_body_2_sub_shlCode base)
    (shl_body_2_spec (sp + 32) limbShift ((0 : Word) + signExtend12 2) bitShift antiShift mask
      v0 v1 v2 v3 (base + 112) (base + 360) 200 (shl_body2_exit base))
  have hbody1 := cpsTriple_extend_code (shl_body_1_sub_shlCode base)
    (shl_body_1_spec (sp + 32) limbShift ((0 : Word) + signExtend12 1) bitShift antiShift mask
      v0 v1 v2 v3 (base + 164) (base + 360) 124 (shl_body1_exit base))
  have hbody0 := cpsTriple_extend_code (shl_body_0_sub_shlCode base)
    (shl_body_0_spec (sp + 32) limbShift sltiuVal bitShift antiShift mask
      v0 v1 v2 v3 (base + 240) (base + 360) 24 (shl_body0_exit base))
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
  have body_post_weaken : ∀ (r5v r6v r7v r10v r11v m32 m40 m48 m56 : Word),
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
    (fun h hp => hp) (fun h hq => body_post_weaken _ _ _ _ _ _ _ _ _ h (by xperm_hyp hq)) hbody0_f
  have hbody1_w := cpsTriple_weaken
    (fun h hp => hp) (fun h hq => body_post_weaken _ _ _ _ _ _ _ _ _ h (by xperm_hyp hq)) hbody1_f
  have hbody2_w := cpsTriple_weaken
    (fun h hp => hp) (fun h hq => body_post_weaken _ _ _ _ _ _ _ _ _ h (by xperm_hyp hq)) hbody2_f
  have hbody3_w := cpsTriple_weaken
    (fun h hp => hp) (fun h hq => body_post_weaken _ _ _ _ _ _ _ _ _ h (by xperm_hyp hq)) hbody3_f
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
  -- Body 0 (L=0): first(i=0), merge(i=1,2,3)
  have hbody0_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbody0_w (fun (hls : limbShift = 0) h hq => by
      have hresult : result = value <<< s0.toNat := by
        show value <<< shift.toNat = value <<< s0.toNat; congr 1
      have hL : (s0 >>> (6 : BitVec 6).toNat).toNat = 0 := congrArg BitVec.toNat hls
      have eq0 := shl_bridge_first value s0 result hresult 0 0 hL (by omega)
      have eq1 := shl_bridge_merge value s0 result hresult 0 1 hL (by omega) (by omega) (by omega)
      have eq2 := shl_bridge_merge value s0 result hresult 0 2 hL (by omega) (by omega) (by omega)
      have eq3 := shl_bridge_merge value s0 result hresult 0 3 hL (by omega) (by omega) (by omega)
      show ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
           (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
           ((sp + 32) ↦ₘ getLimb result 0) ** ((sp + 40) ↦ₘ getLimb result 1) **
           ((sp + 48) ↦ₘ getLimb result 2) ** ((sp + 56) ↦ₘ getLimb result 3)) h
      rw [← eq0, ← eq1, ← eq2, ← eq3]; exact hq)
  -- Body 1 (L=1): zero(i=0), first(i=1), merge(i=2,3)
  have hbody1_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbody1_w (fun (hls : limbShift = (0 : Word) + signExtend12 1) h hq => by
      have hresult : result = value <<< s0.toNat := by
        show value <<< shift.toNat = value <<< s0.toNat; congr 1
      have hL : (s0 >>> (6 : BitVec 6).toNat).toNat = 1 := by
        have := congrArg BitVec.toNat hls
        simp only [zero_add_se12_1_toNat] at this
        exact this
      have eq0 := shl_bridge_zero value s0 result hresult 1 0 hL (by omega)
      have eq1 := shl_bridge_first value s0 result hresult 1 1 hL (by omega)
      have eq2 := shl_bridge_merge value s0 result hresult 1 2 hL (by omega) (by omega) (by omega)
      have eq3 := shl_bridge_merge value s0 result hresult 1 3 hL (by omega) (by omega) (by omega)
      show ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
           (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
           ((sp + 32) ↦ₘ getLimb result 0) ** ((sp + 40) ↦ₘ getLimb result 1) **
           ((sp + 48) ↦ₘ getLimb result 2) ** ((sp + 56) ↦ₘ getLimb result 3)) h
      rw [← eq1, ← eq2, ← eq3, eq0]; exact hq)
  -- Body 2 (L=2): zero(i=0,1), first(i=2), merge(i=3)
  have hbody2_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbody2_w (fun (hls : limbShift = (0 : Word) + signExtend12 2) h hq => by
      have hresult : result = value <<< s0.toNat := by
        show value <<< shift.toNat = value <<< s0.toNat; congr 1
      have hL : (s0 >>> (6 : BitVec 6).toNat).toNat = 2 := by
        have := congrArg BitVec.toNat hls
        simp only [zero_add_se12_2_toNat] at this
        exact this
      have eq0 := shl_bridge_zero value s0 result hresult 2 0 hL (by omega)
      have eq1 := shl_bridge_zero value s0 result hresult 2 1 hL (by omega)
      have eq2 := shl_bridge_first value s0 result hresult 2 2 hL (by omega)
      have eq3 := shl_bridge_merge value s0 result hresult 2 3 hL (by omega) (by omega) (by omega)
      show ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
           (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
           ((sp + 32) ↦ₘ getLimb result 0) ** ((sp + 40) ↦ₘ getLimb result 1) **
           ((sp + 48) ↦ₘ getLimb result 2) ** ((sp + 56) ↦ₘ getLimb result 3)) h
      rw [← eq2, ← eq3, eq0, eq1]; exact hq)
  -- Body 3 (L=3): zero(i=0,1,2), first(i=3)
  have hbody3_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbody3_w (fun (hls : limbShift ≠ 0 ∧ limbShift ≠ (0 : Word) + signExtend12 1 ∧
                limbShift ≠ (0 : Word) + signExtend12 2) h hq => by
      have hresult : result = value <<< s0.toNat := by
        show value <<< shift.toNat = value <<< s0.toNat; congr 1
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
      have eq0 := shl_bridge_zero value s0 result hresult 3 0 hL (by omega)
      have eq1 := shl_bridge_zero value s0 result hresult 3 1 hL (by omega)
      have eq2 := shl_bridge_zero value s0 result hresult 3 2 hL (by omega)
      have eq3 := shl_bridge_first value s0 result hresult 3 3 hL (by omega)
      show ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
           (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
           ((sp + 32) ↦ₘ getLimb result 0) ** ((sp + 40) ↦ₘ getLimb result 1) **
           ((sp + 48) ↦ₘ getLimb result 2) ** ((sp + 56) ↦ₘ getLimb result 3)) h
      rw [← eq3, eq0, eq1, eq2]; exact hq)
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
  have hphaseAB' : cpsTriple base (base + 64) (shlCode base)
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
