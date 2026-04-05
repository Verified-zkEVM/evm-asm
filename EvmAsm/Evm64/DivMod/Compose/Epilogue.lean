/-
  EvmAsm.Evm64.DivMod.Compose.Epilogue

  Denorm, DIV Epilogue, and MOD compositions for DivMod.
  Sections 10l–14 of the original DivModCompose.
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Section 10l: Denorm composition (25 instructions at base+904)
-- LD shift, BEQ skip, ADDI+SUB anti, 3×merge + last
-- ============================================================================

/-- Denorm code (block 9) is subsumed by divCode. -/
private theorem divK_denorm_code_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 904) divK_denorm) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Helper: Denorm sub-block subsumption via ofProg_mono_sub. -/
private theorem denorm_sub (base : Word) (sub_prog : List Instr) (k : Nat)
    (hk : k + sub_prog.length ≤ divK_denorm.length)
    (hslice : (divK_denorm.drop k).take sub_prog.length = sub_prog)
    (hbound : 4 * divK_denorm.length < 2 ^ 64) :
    ∀ a i, (CodeReq.ofProg ((base + 904) + BitVec.ofNat 64 (4 * k)) sub_prog) a = some i →
      (divCode base) a = some i := by
  intro a i h
  exact divK_denorm_code_sub_divCode base a i
    (CodeReq.ofProg_mono_sub (base + 904) _ divK_denorm _ k rfl hslice hk hbound a i h)

-- signExtend12 for u[] offsets
private theorem se12_4032' : signExtend12 (4032 : BitVec 12) = signExtend12 4032 := rfl
private theorem se12_4040' : signExtend12 (4040 : BitVec 12) = signExtend12 4040 := rfl
private theorem se12_4048' : signExtend12 (4048 : BitVec 12) = signExtend12 4048 := rfl
private theorem se12_4056' : signExtend12 (4056 : BitVec 12) = signExtend12 4056 := rfl

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 4096 in
/-- Full Denorm (shift body only): denormalize u[0..3] by right-shifting.
    base+904+16 → base+904+100 (21 instructions: ADDI+SUB + 3×merge + last).
    Used when shift≠0. The BEQ and LD are handled separately. -/
theorem divK_denorm_body_spec (sp u0 u1 u2 u3 v2 v5 v7 shift : Word) (base : Word)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true) :
    let anti_shift := signExtend12 (0 : BitVec 12) - shift
    let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (anti_shift.toNat % 64))
    let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (anti_shift.toNat % 64))
    let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (anti_shift.toNat % 64))
    let u3' := u3 >>> (shift.toNat % 64)
    cpsTriple (base + 912) (base + 1004) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u3') ** (.x7 ↦ᵣ (u3 <<< (anti_shift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
       ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3')) := by
  intro anti_shift u0' u1' u2' u3'
  -- ADDI x2 x0 0 + SUB x2 x2 x6 (base+912 → base+920): compute anti_shift
  have haddi := addi_x0_spec_gen .x2 v2 0 (base + 912) (by nofun)
  rw [show (base + 912 : Word) + 4 = base + 916 from by bv_addr] at haddi
  have haddie := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 904) (base + 912) divK_denorm
        [.ADDI .x2 .x0 0] 2
        (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h)) haddi
  -- Frame ADDI with x12, x5, x7, x6, and all memory
  have haddief := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ shift) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) haddie
  have hsub := sub_spec_gen_rd_eq_rs1 .x2 .x6
    (signExtend12 (0 : BitVec 12)) shift (base + 916) (by nofun)
  rw [show (base + 916 : Word) + 4 = base + 920 from by bv_addr] at hsub
  have hsube := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_divCode base a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + 904) divK_denorm 3
          (by native_decide) (by native_decide)
        rw [show BitVec.ofNat 64 (4 * 3) = (12 : Word) from by native_decide,
            show (base + 904 : Word) + 12 = base + 916 from by bv_addr] at hlookup
        exact hlookup) a i h)) hsub
  -- Frame SUB with x12, x5, x7, x0, and all memory
  have hsubf := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hsube
  have h_anti := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) haddief hsubf
  -- Merge u[0] with u[1] (base+920 → base+944)
  have hm0 := divK_denorm_merge_spec 4056 4048 sp u0 u1 v5 v7 shift anti_shift (base + 920)
    hv_u0 hv_u1
  rw [show (base + 920 : Word) + 24 = base + 944 from by bv_addr] at hm0
  have hm0e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 904) (base + 920) divK_denorm
        (divK_denorm_merge_prog 4056 4048) 4
        (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h)) hm0
  have hm0ef := cpsTriple_frame_left _ _ _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hm0e
  have h_m0 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h_anti hm0ef
  -- Merge u[1] with u[2] (base+944 → base+968)
  have hm1 := divK_denorm_merge_spec 4048 4040 sp u1 u2
    u0' (u1 <<< (anti_shift.toNat % 64)) shift anti_shift (base + 944)
    hv_u1 hv_u2
  rw [show (base + 944 : Word) + 24 = base + 968 from by bv_addr] at hm1
  have hm1e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 904) (base + 944) divK_denorm
        (divK_denorm_merge_prog 4048 4040) 10
        (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h)) hm1
  have hm1ef := cpsTriple_frame_left _ _ _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hm1e
  have h_m1 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h_m0 hm1ef
  -- Merge u[2] with u[3] (base+968 → base+992)
  have hm2 := divK_denorm_merge_spec 4040 4032 sp u2 u3
    u1' (u2 <<< (anti_shift.toNat % 64)) shift anti_shift (base + 968)
    hv_u2 hv_u3
  rw [show (base + 968 : Word) + 24 = base + 992 from by bv_addr] at hm2
  have hm2e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 904) (base + 968) divK_denorm
        (divK_denorm_merge_prog 4040 4032) 16
        (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h)) hm2
  have hm2ef := cpsTriple_frame_left _ _ _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1'))
    (by pcFree) hm2e
  have h_m2 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h_m1 hm2ef
  -- Last u[3] (base+992 → base+1004)
  have hl := divK_denorm_last_spec 4032 sp u3 u2' shift (base + 992) hv_u3
  rw [show (base + 992 : Word) + 12 = base + 1004 from by bv_addr] at hl
  have hle := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 904) (base + 992) divK_denorm
        (divK_denorm_last_prog 4032) 22
        (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h)) hl
  have hlef := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ (u3 <<< (anti_shift.toNat % 64))) ** (.x2 ↦ᵣ anti_shift) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
     ((sp + signExtend12 4040) ↦ₘ u2'))
    (by pcFree) hle
  have h_all := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h_m2 hlef
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h_all

-- ============================================================================
-- Section 10m: DIV Epilogue composition (10 instructions at base+1004)
-- Load q[0..3], ADDI sp+32, store to output, JAL to NOP
-- ============================================================================

/-- DIV epilogue code (block 10) is subsumed by divCode. -/
private theorem divK_divEpilogue_code_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1004) (divK_div_epilogue 24)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 4096 in
/-- Full DIV epilogue: load q[0..3] from scratch, advance sp, store to output, JAL to NOP.
    base+1004 → base+1064 (10 instructions). -/
theorem divK_div_epilogue_spec (sp : Word) (base : Word)
    (q0 q1 q2 q3 v5 v6 v7 v10 m0 m8 m16 m24 : Word)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true) :
    cpsTriple (base + 1004) (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0) ** (.x6 ↦ᵣ q1) ** (.x7 ↦ᵣ q2) ** (.x10 ↦ᵣ q3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ q0) ** ((sp + 40) ↦ₘ q1) **
       ((sp + 48) ↦ₘ q2) ** ((sp + 56) ↦ₘ q3)) := by
  -- Load phase (base+1004 → base+1020)
  have hload := divK_epilogue_load_spec 4088 4080 4072 4064 sp q0 q1 q2 q3 v5 v6 v7 v10
    (base + 1004) hv_q0 hv_q1 hv_q2 hv_q3
  rw [show (base + 1004 : Word) + 16 = base + 1020 from by bv_addr] at hload
  have hloade := cpsTriple_extend_code (hmono := fun a i h =>
    divK_divEpilogue_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 1004) (base + 1004) (divK_div_epilogue 24)
        (divK_epilogue_load_prog 4088 4080 4072 4064) 0
        (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h)) hload
  -- Store phase (base+1020 → base+1064 via JAL)
  have hstore := divK_epilogue_store_spec sp (base + 1020) q0 q1 q2 q3 m0 m8 m16 m24 24 hvalid
  rw [show (base + 1020 : Word) + 20 + signExtend21 24 = base + 1064 from by
        rw [show signExtend21 (24 : BitVec 21) = (24 : Word) from by native_decide]; bv_addr]
    at hstore
  have hstoree := cpsTriple_extend_code (hmono := fun a i h =>
    divK_divEpilogue_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 1004) (base + 1020) (divK_div_epilogue 24)
        (divK_epilogue_store_prog 24) 4
        (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h)) hstore
  -- Frame load with output memory
  have hloadef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) ** ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hloade
  -- Frame store with scratch memory
  have hstoref := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3))
    (by pcFree) hstoree
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hloadef hstoref
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

-- ============================================================================
-- Section 11: MOD program code infrastructure
-- ============================================================================

-- modCode is defined in Base.lean

-- ============================================================================
-- Section 12: MOD CodeReq subsumption lemmas (via mono_unionAll)
-- ============================================================================

private theorem divK_phaseA_code_sub_modCode (base : Word) :
    ∀ a i, (divK_phaseA_code base) a = some i → (modCode base) a = some i := by
  unfold modCode divK_phaseA_code; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _

private theorem divK_zeroPath_code_sub_modCode (base : Word) :
    ∀ a i, (divK_zeroPath_code (base + 1044)) a = some i → (modCode base) a = some i := by
  unfold modCode divK_zeroPath_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

private theorem beq_singleton_sub_modCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 28) (.BEQ .x5 .x0 1016)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  exact CodeReq.union_mono_left _ _ a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup base (divK_phaseA 1016) 7
      (by native_decide) (by native_decide)) a i h)

-- signExtend13 normalization needed for BEQ offset in MOD specs
private theorem signExtend13_1016 : signExtend13 (1016 : BitVec 13) = (1016 : Word) := by
  native_decide

-- ============================================================================
-- Section 13: MOD zero path composition (b = 0)
-- Phase A body → BEQ(taken) → zeroPath → exit
-- ============================================================================

set_option maxRecDepth 2048 in
/-- When b = 0 (all limbs zero), evm_mod writes zeros and advances sp.
    Execution path: phaseA body (7 instrs), BEQ taken, zeroPath (5 instrs). -/
theorem evm_mod_bzero_spec (sp base : Word)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbz : b0 ||| b1 ||| b2 ||| b3 = 0)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 1064) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  -- Step 1: Phase A body (base → base+28, 7 straight-line instructions)
  have hbody := cpsTriple_extend_code (divK_phaseA_code_sub_modCode base)
    (divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10 hvalid)
  -- Step 2: BEQ at base+28, eliminate ntaken via hbz
  have hbeq_raw := beq_spec_gen .x5 .x0 1016 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + 28)
  rw [show (base + 28 : Word) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_addr,
      show (base + 28 : Word) + 4 = base + 32 from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hbz ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbeq := cpsTriple_extend_code (beq_singleton_sub_modCode base) hbeq_clean
  -- Step 3: Frame BEQ with regs + mem
  have hbeq_framed := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  -- Step 4: Compose body → BEQ(taken): base → base+1044
  have hAB := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- Step 5: ZeroPath (base+1044 → base+1064)
  have hzp := cpsTriple_extend_code (divK_zeroPath_code_sub_modCode base)
    (divK_zeroPath_spec sp (base + 1044) b0 b1 b2 b3 hvalid)
  rw [show (base + 1044 : Word) + 20 = base + 1064 from by bv_addr] at hzp
  -- Frame ZP with x5 + x10 + x0
  have hzp_framed := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hzp
  -- Step 6: Compose AB → ZP: base → base+1064
  have hABZ := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hAB hzp_framed
  -- Step 7: Final consequence — rewrite bor → 0
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by rw [hbz] at hq; xperm_hyp hq)
    hABZ

-- ============================================================================
-- Section 14: MOD Phase A not-taken composition (b ≠ 0)
-- ============================================================================

set_option maxRecDepth 2048 in
/-- When b ≠ 0, evm_mod falls through Phase A to Phase B at base+32.
    Execution path: phaseA body (7 instrs), BEQ not taken. -/
theorem evm_mod_phaseA_ntaken_spec (sp base : Word)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 32) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  -- Step 1: Phase A body (base → base+28, 7 straight-line instructions)
  have hbody := cpsTriple_extend_code (divK_phaseA_code_sub_modCode base)
    (divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10 hvalid)
  -- Step 2: BEQ at base+28, eliminate taken path (b=0 absurd since hbnz)
  have hbeq_raw := beq_spec_gen .x5 .x0 1016 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + 28)
  rw [show (base + 28 : Word) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_addr,
      show (base + 28 : Word) + 4 = base + 32 from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hbnz)
  have hbeq := cpsTriple_extend_code (beq_singleton_sub_modCode base) hbeq_clean
  -- Step 3: Frame BEQ with regs + mem
  have hbeq_framed := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  -- Step 4: Compose body → BEQ(ntaken): base → base+32
  have hAB := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- Step 5: Final consequence — permute assertions
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hAB

end EvmAsm.Rv64
