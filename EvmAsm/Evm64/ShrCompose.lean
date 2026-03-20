/-
  EvmAsm.Evm64.ShrCompose

  Hierarchical composition of SHR CPS specs into a single full-program theorem.
  Composes the 5 execution paths through `evm_shr` (90 instructions, 360 bytes):
  - Zero path (shift ≥ 256): Phase A taken → zero_path
  - Body L (L=0..3, shift < 256): Phase A ntaken → B → C(exit L) → body_L → exit
-/

import EvmAsm.Evm64.ShrSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Section 1: shrCode definition and helpers
-- ============================================================================

/-- The full evm_shr code as a single CodeReq.ofProg block (90 instructions). -/
abbrev shrCode (base : Addr) : CodeReq := CodeReq.ofProg base evm_shr

/-- Weaken concrete register to existential ownership. -/
private theorem regIs_to_regOwn (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  fun _ hp => ⟨v, hp⟩

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

/-- A singleton at instruction k of evm_shr is subsumed by shrCode. -/
private theorem singleton_sub_shrCode (base addr : Addr) (instr : Instr) (k : Nat)
    (hk : k < evm_shr.length)
    (h_addr : addr = base + BitVec.ofNat 64 (4 * k))
    (h_instr : evm_shr.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i → shrCode base a = some i :=
  CodeReq.singleton_mono (h_instr ▸ CodeReq.ofProg_lookup_addr base evm_shr k addr hk
    (by native_decide) h_addr)

-- ============================================================================
-- Section 2: Subsumption lemmas
-- ============================================================================

/-- Phase A code (union chain, 9 instrs at +0) is subsumed by shrCode. -/
private theorem phase_a_sub_shrCode (base : Addr) :
    ∀ a i, shr_phase_a_code base a = some i → shrCode base a = some i := by
  unfold shr_phase_a_code
  apply CodeReq_union_sub_both
  · -- singleton base (.LD .x5 .x12 8) → instr 0
    exact singleton_sub_shrCode base base (.LD .x5 .x12 8) 0
      (by native_decide) (by bv_omega) (by native_decide)
  · apply CodeReq_union_sub_both
    · -- shr_ld_or_acc_code 16 (base+4) → instrs 1-2
      unfold shr_ld_or_acc_code
      exact CodeReq.ofProg_mono_sub base (base + 4) evm_shr (shr_ld_or_acc_prog 16) 1
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide)
    · apply CodeReq_union_sub_both
      · -- shr_ld_or_acc_code 24 (base+12) → instrs 3-4
        unfold shr_ld_or_acc_code
        exact CodeReq.ofProg_mono_sub base (base + 12) evm_shr (shr_ld_or_acc_prog 24) 3
          (by bv_omega) (by native_decide) (by native_decide) (by native_decide)
      · apply CodeReq_union_sub_both
        · -- singleton (base+20) (.BNE .x5 .x0 320) → instr 5
          exact singleton_sub_shrCode base (base + 20) (.BNE .x5 .x0 320) 5
            (by native_decide) (by bv_omega) (by native_decide)
        · apply CodeReq_union_sub_both
          · -- singleton (base+24) (.LD .x5 .x12 0) → instr 6
            exact singleton_sub_shrCode base (base + 24) (.LD .x5 .x12 0) 6
              (by native_decide) (by bv_omega) (by native_decide)
          · apply CodeReq_union_sub_both
            · -- singleton (base+28) (.SLTIU .x10 .x5 256) → instr 7
              exact singleton_sub_shrCode base (base + 28) (.SLTIU .x10 .x5 256) 7
                (by native_decide) (by bv_omega) (by native_decide)
            · -- singleton (base+32) (.BEQ .x10 .x0 308) → instr 8
              exact singleton_sub_shrCode base (base + 32) (.BEQ .x10 .x0 308) 8
                (by native_decide) (by bv_omega) (by native_decide)

/-- Phase B code (ofProg, 7 instrs at +36) is subsumed by shrCode. -/
private theorem phase_b_sub_shrCode (base : Addr) :
    ∀ a i, shr_phase_b_code (base + 36) a = some i → shrCode base a = some i := by
  unfold shr_phase_b_code
  exact CodeReq.ofProg_mono_sub base (base + 36) evm_shr shr_phase_b 9
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

set_option maxHeartbeats 4000000 in
private theorem cascade_17_sub_shrCode (base : Addr) :
    ∀ a i, CodeReq.ofProg (base + 68) (shr_cascade_step_prog 1 92) a = some i → shrCode base a = some i :=
  CodeReq.ofProg_mono_sub base (base + 68) evm_shr (shr_cascade_step_prog 1 92) 17
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

set_option maxHeartbeats 4000000 in
private theorem cascade_19_sub_shrCode (base : Addr) :
    ∀ a i, CodeReq.ofProg (base + 76) (shr_cascade_step_prog 2 32) a = some i → shrCode base a = some i :=
  CodeReq.ofProg_mono_sub base (base + 76) evm_shr (shr_cascade_step_prog 2 32) 19
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- Phase C code (union chain, 5 instrs at +64) is subsumed by shrCode. -/
private theorem phase_c_sub_shrCode (base : Addr) :
    ∀ a i, shr_phase_c_code (base + 64) a = some i → shrCode base a = some i := by
  unfold shr_phase_c_code
  apply CodeReq_union_sub_both
  · -- singleton (base+64) (.BEQ .x5 .x0 176) → instr 16
    exact singleton_sub_shrCode base (base + 64) (.BEQ .x5 .x0 176) 16
      (by native_decide) (by bv_omega) (by native_decide)
  · apply CodeReq_union_sub_both
    · -- shr_cascade_step_code 1 92 (base+68) → instrs 17-18
      unfold shr_cascade_step_code
      have : (base + 64 : Addr) + 4 = base + 68 := by bv_omega
      rw [this]
      exact cascade_17_sub_shrCode base
    · -- shr_cascade_step_code 2 32 (base+76) → instrs 19-20
      unfold shr_cascade_step_code
      have : (base + 64 : Addr) + 12 = base + 76 := by bv_omega
      rw [this]
      exact cascade_19_sub_shrCode base

/-- Body 3 code (ofProg, 7 instrs at +84) is subsumed by shrCode. -/
private theorem body_3_sub_shrCode (base : Addr) :
    ∀ a i, shr_body_3_code 252 (base + 84) a = some i → shrCode base a = some i := by
  unfold shr_body_3_code
  exact CodeReq.ofProg_mono_sub base (base + 84) evm_shr (shr_body_3_prog 252) 21
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- Body 2 code (ofProg, 13 instrs at +112) is subsumed by shrCode. -/
private theorem body_2_sub_shrCode (base : Addr) :
    ∀ a i, shr_body_2_code 200 (base + 112) a = some i → shrCode base a = some i := by
  unfold shr_body_2_code
  exact CodeReq.ofProg_mono_sub base (base + 112) evm_shr (shr_body_2_prog 200) 28
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- Body 1 code (ofProg, 19 instrs at +164) is subsumed by shrCode. -/
private theorem body_1_sub_shrCode (base : Addr) :
    ∀ a i, shr_body_1_code 124 (base + 164) a = some i → shrCode base a = some i := by
  unfold shr_body_1_code
  exact CodeReq.ofProg_mono_sub base (base + 164) evm_shr (shr_body_1_prog 124) 41
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- Body 0 code (ofProg, 25 instrs at +240) is subsumed by shrCode. -/
private theorem body_0_sub_shrCode (base : Addr) :
    ∀ a i, shr_body_0_code 24 (base + 240) a = some i → shrCode base a = some i := by
  unfold shr_body_0_code
  exact CodeReq.ofProg_mono_sub base (base + 240) evm_shr (shr_body_0_prog 24) 60
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- Zero path code (ofProg, 5 instrs at +340) is subsumed by shrCode. -/
private theorem zero_path_sub_shrCode (base : Addr) :
    ∀ a i, shr_zero_path_code (base + 340) a = some i → shrCode base a = some i := by
  unfold shr_zero_path_code
  exact CodeReq.ofProg_mono_sub base (base + 340) evm_shr shr_zero_path 85
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

-- Individual instruction subsumption helpers (for phase A raw composition)

/-- LD x5 x12 8 singleton at base is subsumed by shrCode. -/
private theorem ld_s1_sub_shrCode (base : Addr) :
    ∀ a i, CodeReq.singleton base (.LD .x5 .x12 8) a = some i → shrCode base a = some i :=
  singleton_sub_shrCode base base (.LD .x5 .x12 8) 0
    (by native_decide) (by bv_omega) (by native_decide)

/-- LD/OR acc at base+4 (2 instrs) is subsumed by shrCode. -/
private theorem ld_or_16_sub_shrCode (base : Addr) :
    ∀ a i, shr_ld_or_acc_code 16 (base + 4) a = some i → shrCode base a = some i := by
  unfold shr_ld_or_acc_code
  exact CodeReq.ofProg_mono_sub base (base + 4) evm_shr (shr_ld_or_acc_prog 16) 1
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- LD/OR acc at base+12 (2 instrs) is subsumed by shrCode. -/
private theorem ld_or_24_sub_shrCode (base : Addr) :
    ∀ a i, shr_ld_or_acc_code 24 (base + 12) a = some i → shrCode base a = some i := by
  unfold shr_ld_or_acc_code
  exact CodeReq.ofProg_mono_sub base (base + 12) evm_shr (shr_ld_or_acc_prog 24) 3
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- BNE singleton at base+20 is subsumed by shrCode. -/
private theorem bne_sub_shrCode (base : Addr) :
    ∀ a i, CodeReq.singleton (base + 20) (.BNE .x5 .x0 320) a = some i → shrCode base a = some i :=
  singleton_sub_shrCode base (base + 20) (.BNE .x5 .x0 320) 5
    (by native_decide) (by bv_omega) (by native_decide)

/-- LD x5 x12 0 singleton at base+24 is subsumed by shrCode. -/
private theorem ld_s0_sub_shrCode (base : Addr) :
    ∀ a i, CodeReq.singleton (base + 24) (.LD .x5 .x12 0) a = some i → shrCode base a = some i :=
  singleton_sub_shrCode base (base + 24) (.LD .x5 .x12 0) 6
    (by native_decide) (by bv_omega) (by native_decide)

/-- SLTIU singleton at base+28 is subsumed by shrCode. -/
private theorem sltiu_sub_shrCode (base : Addr) :
    ∀ a i, CodeReq.singleton (base + 28) (.SLTIU .x10 .x5 256) a = some i → shrCode base a = some i :=
  singleton_sub_shrCode base (base + 28) (.SLTIU .x10 .x5 256) 7
    (by native_decide) (by bv_omega) (by native_decide)

/-- BEQ singleton at base+32 is subsumed by shrCode. -/
private theorem beq_sub_shrCode (base : Addr) :
    ∀ a i, CodeReq.singleton (base + 32) (.BEQ .x10 .x0 308) a = some i → shrCode base a = some i :=
  singleton_sub_shrCode base (base + 32) (.BEQ .x10 .x0 308) 8
    (by native_decide) (by bv_omega) (by native_decide)

-- ============================================================================
-- Section 3: Address normalization lemmas
-- ============================================================================

private theorem shr_off_4 (base : Addr) : (base + 4 : Addr) + 8 = base + 12 := by bv_omega
private theorem shr_off_12 (base : Addr) : (base + 12 : Addr) + 8 = base + 20 := by bv_omega
private theorem shr_off_20 (base : Addr) : (base + 20 : Addr) + 4 = base + 24 := by bv_omega
private theorem shr_off_24 (base : Addr) : (base + 24 : Addr) + 4 = base + 28 := by bv_omega
private theorem shr_off_28 (base : Addr) : (base + 28 : Addr) + 4 = base + 32 := by bv_omega
private theorem shr_off_32 (base : Addr) : (base + 32 : Addr) + 4 = base + 36 := by bv_omega
private theorem shr_off_36_28 (base : Addr) : (base + 36 : Addr) + 28 = base + 64 := by bv_omega
private theorem shr_off_340_20 (base : Addr) : (base + 340 : Addr) + 20 = base + 360 := by bv_omega
private theorem shr_bne_target (base : Addr) : (base + 20 : Addr) + signExtend13 320 = base + 340 := by
  rw [show signExtend13 (320 : BitVec 13) = (320 : Word) from by native_decide]; bv_omega
private theorem shr_beq_target (base : Addr) : (base + 32 : Addr) + signExtend13 308 = base + 340 := by
  rw [show signExtend13 (308 : BitVec 13) = (308 : Word) from by native_decide]; bv_omega
-- Phase C exit addresses
private theorem shr_c_e0 (base : Addr) : (base + 64 : Addr) + signExtend13 176 = base + 240 := by
  rw [show signExtend13 (176 : BitVec 13) = (176 : Word) from by native_decide]; bv_omega
private theorem shr_c_e1 (base : Addr) : ((base + 64 : Addr) + 8) + signExtend13 92 = base + 164 := by
  rw [show signExtend13 (92 : BitVec 13) = (92 : Word) from by native_decide]; bv_omega
private theorem shr_c_e2 (base : Addr) : ((base + 64 : Addr) + 16) + signExtend13 32 = base + 112 := by
  rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by native_decide]; bv_omega
private theorem shr_c_e3 (base : Addr) : (base + 64 : Addr) + 20 = base + 84 := by bv_omega
-- Body exit addresses (JAL targets)
private theorem shr_body3_exit (base : Addr) : ((base + 84 : Addr) + 24) + signExtend21 252 = base + 360 := by
  rw [show signExtend21 (252 : BitVec 21) = (252 : Word) from by native_decide]; bv_omega
private theorem shr_body2_exit (base : Addr) : ((base + 112 : Addr) + 48) + signExtend21 200 = base + 360 := by
  rw [show signExtend21 (200 : BitVec 21) = (200 : Word) from by native_decide]; bv_omega
private theorem shr_body1_exit (base : Addr) : ((base + 164 : Addr) + 72) + signExtend21 124 = base + 360 := by
  rw [show signExtend21 (124 : BitVec 21) = (124 : Word) from by native_decide]; bv_omega
private theorem shr_body0_exit (base : Addr) : ((base + 240 : Addr) + 96) + signExtend21 24 = base + 360 := by
  rw [show signExtend21 (24 : BitVec 21) = (24 : Word) from by native_decide]; bv_omega

-- ============================================================================
-- Section 4: Zero path composition
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- Zero path via BNE taken: high shift limbs are nonzero → shift ≥ 256 → result is zero.
    Execution: LD s1 → LD/OR s2 → LD/OR s3 → BNE(taken) → zero_path. -/
theorem evm_shr_zero_high_spec (sp base : Addr)
    (s0 s1 s2 s3 v0 v1 v2 v3 r5 r10 : Word)
    (hhigh : s1 ||| s2 ||| s3 ≠ 0)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 360) (shrCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  -- Memory validity
  have hv8 : isValidDwordAccess (sp + 8) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv16 : isValidDwordAccess (sp + 16) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv24 : isValidDwordAccess (sp + 24) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv32 : ValidMemRange (sp + 32) 4 := by
    intro i hi; have := hvalid.get (i := i + 4) (by omega)
    have : isValidDwordAccess (sp + BitVec.ofNat 64 (8 * (i + 4))) = true := this
    rw [show sp + BitVec.ofNat 64 (8 * (i + 4)) = sp + 32 + BitVec.ofNat 64 (8 * i) from by bv_omega] at this
    exact this
  -- Step 1: LD x5 x12 8 at base → extend to shrCode
  have h1 := cpsTriple_extend_code (ld_s1_sub_shrCode base)
    (ld_spec_gen .x5 .x12 sp r5 s1 8 base (by nofun)
      (by simp only [signExtend12_8]; exact hv8))
  simp only [signExtend12_8] at h1
  -- Step 2: LD/OR at base+4 → extend to shrCode
  have h2 := cpsTriple_extend_code (ld_or_16_sub_shrCode base)
    (shr_ld_or_acc_spec sp s1 r10 s2 16 (base + 4)
      (by simp only [signExtend12_16]; exact hv16))
  simp only [signExtend12_16] at h2
  rw [shr_off_4] at h2
  -- Step 3: LD/OR at base+12 → extend to shrCode
  have h3 := cpsTriple_extend_code (ld_or_24_sub_shrCode base)
    (shr_ld_or_acc_spec sp (s1 ||| s2) s2 s3 24 (base + 12)
      (by simp only [signExtend12_24]; exact hv24))
  simp only [signExtend12_24] at h3
  rw [shr_off_12] at h3
  -- Frame and compose LD → LD/OR → LD/OR
  have h1f := cpsTriple_frame_left base (base + 4) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
     (sp ↦ₘ s0) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h1
  have h2f := cpsTriple_frame_left (base + 4) (base + 12) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h2
  have h12 := cpsTriple_seq_with_perm_same_cr base (base + 4) (base + 12) _
    _ _ _ _
    (fun h hp => by xperm_hyp hp) h1f h2f
  have h3f := cpsTriple_frame_left (base + 12) (base + 20) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h3
  have h123 := cpsTriple_seq_with_perm_same_cr base (base + 12) (base + 20) _
    _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 h3f
  -- Step 4: BNE at base+20 → extend to shrCode, eliminate ntaken
  have hbne_raw := bne_spec_gen .x5 .x0 320 (s1 ||| s2 ||| s3) (0 : Word) (base + 20)
  rw [shr_bne_target, shr_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code (bne_sub_shrCode base) hbne_raw
  -- Eliminate ntaken path (s1|||s2|||s3 = 0 contradicts hhigh)
  have hbne_taken := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hhigh)
  -- Frame BNE with remaining state
  have hbne_framed := cpsTriple_frame_left (base + 20) (base + 340) _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ s3) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbne_taken
  -- Compose linear chain → BNE(taken)
  have hAB := cpsTriple_seq_with_perm_same_cr base (base + 20) (base + 340) _
    _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hbne_framed
  -- Step 5: Zero path (base+340 → base+360) → extend to shrCode
  have hzp := cpsTriple_extend_code (zero_path_sub_shrCode base)
    (shr_zero_path_spec sp v0 v1 v2 v3 (base + 340) hv32)
  rw [shr_off_340_20] at hzp
  -- Frame zero path with remaining state
  have hzp_framed := cpsTriple_frame_left (base + 340) (base + 360) _ _ _
    ((.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ s3) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) hzp
  -- Address normalization lemmas
  have ha40 : sp + 40 = (sp + 32 : Addr) + 8 := by bv_omega
  have ha48 : sp + 48 = (sp + 32 : Addr) + 16 := by bv_omega
  have ha56 : sp + 56 = (sp + 32 : Addr) + 24 := by bv_omega
  have ha40' : (sp + 32 : Addr) + 8 = sp + 40 := by bv_omega
  have ha48' : (sp + 32 : Addr) + 16 = sp + 48 := by bv_omega
  have ha56' : (sp + 32 : Addr) + 24 = sp + 56 := by bv_omega
  -- Compose AB → ZP: normalize addresses in perm callback
  have hABZ := cpsTriple_seq_with_perm_same_cr base (base + 340) (base + 360) _
    _ _ _ _
    (fun h hp => by
      simp only [ha40, ha48, ha56] at hp
      xperm_hyp hp) hAB hzp_framed
  -- Final: normalize addresses back + weaken regs to regOwn
  exact cpsTriple_consequence _ _ _ _ _ _ _
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

set_option maxHeartbeats 3200000 in
/-- Zero path via BEQ taken: s1=s2=s3=0 but s0 ≥ 256 → result is zero.
    Execution: LD s1 → LD/OR s2 → LD/OR s3 → BNE(ntaken) → LD s0 → SLTIU → BEQ(taken) → zero_path. -/
theorem evm_shr_zero_large_spec (sp base : Addr)
    (s0 s1 s2 s3 v0 v1 v2 v3 r5 r10 : Word)
    (hlow : s1 ||| s2 ||| s3 = 0)
    (hlarge : BitVec.ult s0 (signExtend12 (256 : BitVec 12)) = false)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 360) (shrCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  -- Memory validity
  have hv0 : isValidDwordAccess sp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv8 : isValidDwordAccess (sp + 8) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv16 : isValidDwordAccess (sp + 16) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv24 : isValidDwordAccess (sp + 24) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv32 : ValidMemRange (sp + 32) 4 := by
    intro i hi; have := hvalid.get (i := i + 4) (by omega)
    have : isValidDwordAccess (sp + BitVec.ofNat 64 (8 * (i + 4))) = true := this
    rw [show sp + BitVec.ofNat 64 (8 * (i + 4)) = sp + 32 + BitVec.ofNat 64 (8 * i) from by bv_omega] at this
    exact this
  -- Steps 1-3: Same linear chain as zero_high
  have h1 := cpsTriple_extend_code (ld_s1_sub_shrCode base)
    (ld_spec_gen .x5 .x12 sp r5 s1 8 base (by nofun) (by simp only [signExtend12_8]; exact hv8))
  simp only [signExtend12_8] at h1
  have h2 := cpsTriple_extend_code (ld_or_16_sub_shrCode base)
    (shr_ld_or_acc_spec sp s1 r10 s2 16 (base + 4) (by simp only [signExtend12_16]; exact hv16))
  simp only [signExtend12_16] at h2; rw [shr_off_4] at h2
  have h3 := cpsTriple_extend_code (ld_or_24_sub_shrCode base)
    (shr_ld_or_acc_spec sp (s1 ||| s2) s2 s3 24 (base + 12) (by simp only [signExtend12_24]; exact hv24))
  simp only [signExtend12_24] at h3; rw [shr_off_12] at h3
  -- Frame + compose linear chain
  have h1f := cpsTriple_frame_left base (base + 4) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
     (sp ↦ₘ s0) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h1
  have h2f := cpsTriple_frame_left (base + 4) (base + 12) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h2
  have h12 := cpsTriple_seq_with_perm_same_cr base (base + 4) (base + 12) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1f h2f
  have h3f := cpsTriple_frame_left (base + 12) (base + 20) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) h3
  have h123 := cpsTriple_seq_with_perm_same_cr base (base + 12) (base + 20) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 h3f
  -- Step 4: BNE at base+20 → eliminate TAKEN (s1|||s2|||s3 = 0 contradicts ≠ 0)
  have hbne_raw := bne_spec_gen .x5 .x0 320 (s1 ||| s2 ||| s3) (0 : Word) (base + 20)
  rw [shr_bne_target, shr_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code (bne_sub_shrCode base) hbne_raw
  have hbne_ntaken := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _ _ _).mp h_rest).2 hlow)
  -- Frame BNE(ntaken) with remaining state
  have hbne_framed := cpsTriple_frame_left (base + 20) (base + 24) _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ s3) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbne_ntaken
  -- Compose linear → BNE(ntaken)
  have h1234 := cpsTriple_seq_with_perm_same_cr base (base + 20) (base + 24) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hbne_framed
  -- Step 5: LD x5 x12 0 at base+24 → extend to shrCode
  have hld_raw := ld_spec_gen .x5 .x12 sp (s1 ||| s2 ||| s3) s0 0 (base + 24) (by nofun)
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_omega]; exact hv0)
  simp only [signExtend12_0] at hld_raw
  rw [show sp + (0 : Word) = sp from by bv_omega, shr_off_24] at hld_raw
  have hld := cpsTriple_extend_code (ld_s0_sub_shrCode base) hld_raw
  -- Step 6: SLTIU at base+28 → extend to shrCode
  have hsltiu_raw := sltiu_spec_gen .x10 .x5 s3 s0 256 (base + 28) (by nofun)
  rw [shr_off_28] at hsltiu_raw
  have hsltiu := cpsTriple_extend_code (sltiu_sub_shrCode base) hsltiu_raw
  -- Frame + compose LD → SLTIU
  have hld_f := cpsTriple_frame_left (base + 24) (base + 28) _ _ _
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ s3) **
     ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hld
  have hsltiu_f := cpsTriple_frame_left (base + 28) (base + 32) _ _ _
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hsltiu
  have h56 := cpsTriple_seq_with_perm_same_cr (base + 24) (base + 28) (base + 32) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hld_f hsltiu_f
  -- Compose h1234 → h56
  have h123456 := cpsTriple_seq_with_perm_same_cr base (base + 24) (base + 32) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234 h56
  -- Step 7: BEQ at base+32 → eliminate ntaken (sltiu_val = 0 since s0 ≥ 256)
  let sltiu_val := (if BitVec.ult s0 (signExtend12 (256 : BitVec 12)) then (1 : Word) else (0 : Word))
  have hbeq_raw := beq_spec_gen .x10 .x0 308 sltiu_val (0 : Word) (base + 32)
  rw [shr_beq_target, shr_off_32] at hbeq_raw
  have hbeq := cpsBranch_extend_code (beq_sub_shrCode base) hbeq_raw
  -- sltiu_val = 0 (since s0 ≥ 256 → ult is false)
  have hsltiu_eq : sltiu_val = (0 : Word) := by
    simp only [sltiu_val, hlarge]; decide
  -- Eliminate ntaken: ntaken postcondition has ⌜sltiu_val ≠ 0⌝, but sltiu_val = 0
  have hbeq_taken := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbeq
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact ((sepConj_pure_right _ _ _).mp h_rest).2 hsltiu_eq)
  -- Frame BEQ(taken) with remaining state
  have hbeq_framed := cpsTriple_frame_left (base + 32) (base + 340) _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbeq_taken
  -- Compose h123456 → BEQ(taken)
  have h1234567 := cpsTriple_seq_with_perm_same_cr base (base + 32) (base + 340) _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123456 hbeq_framed
  -- Step 8: Zero path (base+340 → base+360)
  have hzp := cpsTriple_extend_code (zero_path_sub_shrCode base)
    (shr_zero_path_spec sp v0 v1 v2 v3 (base + 340) hv32)
  rw [shr_off_340_20] at hzp
  have hzp_framed := cpsTriple_frame_left (base + 340) (base + 360) _ _ _
    ((.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ sltiu_val) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) hzp
  -- Address normalization lemmas
  have ha40 : sp + 40 = (sp + 32 : Addr) + 8 := by bv_omega
  have ha48 : sp + 48 = (sp + 32 : Addr) + 16 := by bv_omega
  have ha56 : sp + 56 = (sp + 32 : Addr) + 24 := by bv_omega
  have ha40' : (sp + 32 : Addr) + 8 = sp + 40 := by bv_omega
  have ha48' : (sp + 32 : Addr) + 16 = sp + 48 := by bv_omega
  have ha56' : (sp + 32 : Addr) + 24 = sp + 56 := by bv_omega
  -- Compose → ZP: normalize addresses in perm callback
  have hfull := cpsTriple_seq_with_perm_same_cr base (base + 340) (base + 360) _ _ _ _ _
    (fun h hp => by
      simp only [ha40, ha48, ha56] at hp
      xperm_hyp hp) h1234567 hzp_framed
  -- Final: normalize addresses back + weaken regs to regOwn
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      simp only [ha40', ha48', ha56'] at hq
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ s0) ** (.x10 ↦ᵣ sltiu_val) **
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
-- Section 5: Body path composition
-- ============================================================================

-- Helpers for extending code requirements to cpsNBranch

/-- Monotonicity for cpsNBranch: extend to a larger CodeReq. -/
private theorem cpsNBranch_extend_code {entry : Addr} {cr cr' : CodeReq}
    {P : Assertion} {exits : List (Addr × Assertion)}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsNBranch entry cr P exits) :
    cpsNBranch entry cr' P exits := by
  intro R hR s hcr' hPR hpc
  exact h R hR s (CodeReq.SatisfiedBy_mono s hmono hcr') hPR hpc

/-- Frame rule for cpsNBranch: frames each exit postcondition with F. -/
private theorem cpsNBranch_frame_left {entry : Addr} {cr : CodeReq}
    {P : Assertion} {exits : List (Addr × Assertion)} {F : Assertion}
    (hF : F.pcFree) (h : cpsNBranch entry cr P exits) :
    cpsNBranch entry cr (P ** F) (exits.map (fun ex => (ex.1, ex.2 ** F))) := by
  intro R hR s hcr hPFR hpc
  have hFR : (F ** R).pcFree := pcFree_sepConj hF hR
  have hPFR' : (P ** (F ** R)).holdsFor s :=
    holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQFR⟩ :=
    h (F ** R) hFR s hcr hPFR' hpc
  refine ⟨k, s', hstep, (ex.1, ex.2 ** F), ?_, hpc', holdsFor_sepConj_assoc.mpr hQFR⟩
  exact List.mem_map.mpr ⟨ex, hmem, rfl⟩

-- Address normalization lemmas for body path
private theorem shr_off_64_20 (base : Addr) : (base + 64 : Addr) + 20 = base + 84 := by bv_omega
private theorem shr_off_sp32 (sp : Word) : sp + signExtend12 (32 : BitVec 12) = sp + 32 := by
  simp only [signExtend12_32]

-- ============================================================================
-- Section 5a: Phase A ntaken → Phase B composition
-- ============================================================================

-- Phase A is already provided as a cpsBranch (shr_phase_a_spec) with:
--   taken: zero_path (base+340), x5/x10 existential
--   ntaken: base+36, x5 = s0, x10 existential
-- Phase B takes x5 = s0 at base+36 and produces parameters at base+64.

-- ============================================================================
-- Section 5b: Body path theorem (Phase A ntaken → B → C → body → exit)
-- ============================================================================

-- Helper to derive ValidMemRange for the value portion (sp+32..sp+56)
private theorem validMem_value_portion {sp : Addr} (hvalid : ValidMemRange sp 8) :
    ValidMemRange (sp + 32) 4 := by
  intro i hi; have := hvalid.get (i := i + 4) (by omega)
  have : isValidDwordAccess (sp + BitVec.ofNat 64 (8 * (i + 4))) = true := this
  rw [show sp + BitVec.ofNat 64 (8 * (i + 4)) = sp + 32 + BitVec.ofNat 64 (8 * i) from by bv_omega] at this
  exact this

-- Note: evm_shr_body_spec (with memOwn postcondition) was removed because it
-- hides the result. The useful spec is evm_shr_stack_spec in ShrSemantic.lean
-- which states the concrete result `value >>> shift.toNat`.
-- The body-path composition infrastructure (Phase A ntaken → B → C → bodies)
-- will be inlined into the semantic proof when the bitvector bridge lemma
-- (getLimb_ushiftRight) is available.

-- The body path composition + bitvector bridge is in ShrSemantic.lean
-- (evm_shr_body_evmWord_spec), which depends on getLimb_ushiftRight from Basic.lean.

end EvmAsm.Rv64
