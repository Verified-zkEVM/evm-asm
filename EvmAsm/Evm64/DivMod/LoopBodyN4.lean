/-
  EvmAsm.Evm64.DivMod.LoopBodyN4

  Fixed loop body compositions for n=4 (4-limb divisor, m=0, single iteration).
  Eliminates the u_addr/window-cell and vtop/v3 overlaps in the generic spec.

  For n=4, three address overlaps exist:
  1. u_addr = u_base + signExtend12 4064  (both refer to u[j+4])
  2. u_addr + 8 = u_base + signExtend12 4072  (both refer to u[j+3])
  3. vtop_base + signExtend12 32 = sp + signExtend12 56  (both refer to v[3])

  This file eliminates these overlaps by:
  - Expanding the trial spec's let-bindings via dsimp
  - Rewriting u_addr and vtop_base to canonical u_base-relative form
  - Framing only with cells NOT already in the trial spec
  - Composing without cell duplication in any separating conjunction
-/

import EvmAsm.Evm64.DivMod.LoopBody
import EvmAsm.Evm64.DivMod.LoopDefs

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address rewriting lemmas for n=4 (no let-bindings, suitable for rw)
-- ============================================================================

/-- For n=4: u_addr = u_base + signExtend12 4064 -/
theorem u_addr_eq_n4 (sp j : Word) :
    sp + signExtend12 4056 - (j + (4 : Word)) <<< (3 : BitVec 6).toNat =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064 := by
  divmod_addr

/-- For n=4: (u_base + signExtend12 4064) + 8 = u_base + signExtend12 4072 -/
theorem u_addr8_eq_n4 (sp j : Word) :
    ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) + 8 =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  divmod_addr

/-- For n=4: vtop_base + signExtend12 32 = sp + signExtend12 56 -/
theorem vtop_eq_v3_n4 (sp : Word) :
    (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat) + signExtend12 32 =
    sp + signExtend12 56 := by
  divmod_addr

-- ============================================================================
-- Section 12n4: Full loop body cpsBranch for n=4, BLTU not-taken + BEQ skip
-- Non-vacuous: no overlapping cells in precondition.
-- ============================================================================

/-- Full loop body (BLTU ntaken + BEQ skip) for n=4.
    No overlapping cells: u_hi=u_top, u_lo=u3, v_top=v3.
    Entry: base+448, cpsBranch to base+448/904. -/
theorem divK_loop_body_n4_max_skip_spec
    (sp j j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095  -- MAX64
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow = 0
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsBranch (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (base + loopBodyOff) (loopBodyN4SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top)
      (base + denormOff) (loopBodyN4SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  -- Expand mulsub computation locally for intermediate steps
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  -- Extract individual components matching the old let-chain names
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0
  let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi
  let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1
  let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi
  let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2
  let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi
  let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let j' := j + signExtend12 4095
  -- Abbreviation for vtop_base (register value, not a memory address)
  let vtop_base := sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial max full (base+448 → base+516), instantiated with n=4, u_hi=u_top, u_lo=u3, v_top=v3
  have TF := divK_trial_max_full_spec sp j (4 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u_top u3 v3 base hbltu
  -- Expand let-bindings in TF to expose raw address expressions
  dsimp only [] at TF
  -- Rewrite u_addr → u_base + signExtend12 4064, and (u_addr+8) → u_base + signExtend12 4072
  rw [u_addr_eq_n4 sp j] at TF
  rw [u_addr8_eq_n4 sp j] at TF
  -- Rewrite vtop_base + signExtend12 32 → sp + signExtend12 56
  rw [vtop_eq_v3_n4 sp] at TF
  -- 2. Mulsub + correction skip (base+516 → base+880)
  have MCS := divK_mulsub_correction_skip_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
    j u3 vtop_base u_top v3 v2_old base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  -- 3. Store loop cpsBranch (base+880 → base+448/904)
  have SL := divK_store_loop_spec sp j q_hat u4_new (0 : Word) q_old base
  intro_lets at SL
  -- 4. Frame TF with mulsub cells that DON'T overlap
  --    (u_base+4064 ↦ₘ u_top, u_base+4072 ↦ₘ u3, sp+56 ↦ₘ v3 are already in TF)
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCS0
  seqFrame TFf MCS0
  -- 6. Frame store_loop with remaining atoms
  have SLf := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)))
    (by pcFree) SL
  -- 7. Compose pre_store (cpsTriple) with SLf (cpsBranch)
  have full := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  -- 8. Permute final cpsBranch to match target
  exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN4SkipPost loopBodySkipPost mulsubN4 loopExitPostN4 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (fun h hp => by delta loopBodyN4SkipPost loopBodySkipPost mulsubN4 loopExitPostN4 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- Section 13n4: Full loop body cpsBranch for n=4, BLTU not-taken + BEQ addback
-- ============================================================================

/-- Full loop body (BLTU ntaken + BEQ addback) for n=4.
    No overlapping cells: u_hi=u_top, u_lo=u3, v_top=v3.
    Entry: base+448, cpsBranch to base+448/904. -/
theorem divK_loop_body_n4_max_addback_spec
    (sp j j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095  -- MAX64
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - ms.2.2.2.2) v0 v1 v2 v3
    -- Hypothesis: second addback carry nonzero (only needed if first carry = 0)
    (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = 0 →
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) →
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsBranch (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (base + loopBodyOff) (loopBodyN4AddbackBeqPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top)
      (base + denormOff) (loopBodyN4AddbackBeqPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr ms ab hcarry2_nz hborrow
  -- Local lets matching beq_spec structure
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
  let q_out := if carry = 0 then q_hat + signExtend12 4095 + signExtend12 4095
               else q_hat + signExtend12 4095
  let un0_out := if carry = 0 then ab'.1 else ab.1
  let un1_out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2_out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3_out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  let carry_out := if carry = 0 then
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
    else carry
  -- Abbreviation for vtop_base (register value, not a memory address)
  let vtop_base := sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial max full (base+448 → base+516)
  have TF := divK_trial_max_full_spec sp j (4 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u_top u3 v3 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n4 sp j] at TF
  rw [u_addr8_eq_n4 sp j] at TF
  rw [vtop_eq_v3_n4 sp] at TF
  -- 2. Mulsub + correction addback + BEQ (base+516 → base+884)
  have MCA := divK_mulsub_correction_addback_beq_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
    j u3 vtop_base u_top v3 v2_old base

  intro_lets at MCA
  have MCA0 := MCA hcarry2_nz hborrow
  -- 3. Store loop cpsBranch (base+884 → base+448/908)
  have SL := divK_store_loop_spec sp j q_out u4_out carry_out q_old base
  intro_lets at SL
  -- 4. Frame TF with non-overlapping cells
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCA0
  seqFrame TFf MCA0
  -- 6. Frame store_loop
  have SLf := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3_out) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_out) **
     ((u_base + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)))
    (by pcFree) SL
  -- 7. Compose
  have full := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN4AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN4 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (fun h hp => by delta loopBodyN4AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN4 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- Section 14n4: Full loop body cpsBranch for n=4, BLTU taken + BEQ skip
-- ============================================================================

/-- Full loop body (BLTU taken + BEQ skip) for n=4.
    No overlapping cells: u_hi=u_top, u_lo=u3, v_top=v3.
    Entry: base+448, cpsBranch to base+448/904. -/
theorem divK_loop_body_n4_call_skip_spec
    (sp j j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- div128 intermediates
    let d_hi := v3 >>> (32 : BitVec 6).toNat
    let d_lo := (v3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u_top d_hi
    let rhat := u_top - q1 * d_hi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + d_hi
    let q_dlo := q1c * d_lo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * d_lo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * d_lo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow = 0
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsBranch (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (base + loopBodyOff)
      (loopBodyN4SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v3) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0))
      (base + denormOff)
      (loopBodyN4SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v3) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  intro u_base
        d_hi d_lo div_un1 div_un0 q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' q_hat
        q_addr hborrow
  -- Expand mulsub computation locally for intermediate steps
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0
  let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi
  let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1
  let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi
  let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2
  let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi
  let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let j' := j + signExtend12 4095
  let vtop_base := sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial call full (base+448 → base+516)
  have TF := divK_trial_call_full_spec sp j (4 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u_top u3 v3 ret_mem d_mem dlo_mem scratch_un0 base
    halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n4 sp j] at TF
  rw [u_addr8_eq_n4 sp j] at TF
  rw [vtop_eq_v3_n4 sp] at TF
  -- 2. Mulsub + correction skip (base+516 → base+880)
  have MCS := divK_mulsub_correction_skip_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  -- 3. Store loop cpsBranch (base+880 → base+448/904)
  have SL := divK_store_loop_spec sp j q_hat u4_new (0 : Word) q_old base
  intro_lets at SL
  -- 4. Frame TF (trial_call includes scratch memory, so don't add those to frame)
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCS0
  seqFrame TFf MCS0
  -- 6. Frame store_loop
  have SLf := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v3) **
     (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  -- 7. Compose
  have full := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN4SkipPost loopBodySkipPost mulsubN4 loopExitPostN4 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (fun h hp => by delta loopBodyN4SkipPost loopBodySkipPost mulsubN4 loopExitPostN4 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- Section 15n4: Full loop body cpsBranch for n=4, BLTU taken + BEQ addback
-- ============================================================================

/-- Full loop body (BLTU taken + BEQ addback) for n=4.
    No overlapping cells: u_hi=u_top, u_lo=u3, v_top=v3.
    Entry: base+448, cpsBranch to base+448/904. -/
theorem divK_loop_body_n4_call_addback_spec
    (sp j j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- div128 intermediates
    let d_hi := v3 >>> (32 : BitVec 6).toNat
    let d_lo := (v3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u_top d_hi
    let rhat := u_top - q1 * d_hi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + d_hi
    let q_dlo := q1c * d_lo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * d_lo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * d_lo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - ms.2.2.2.2) v0 v1 v2 v3
    -- Hypothesis: second addback carry nonzero (only needed if first carry = 0)
    (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = 0 →
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) →
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsBranch (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (base + loopBodyOff)
      (loopBodyN4AddbackBeqPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v3) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0))
      (base + denormOff)
      (loopBodyN4AddbackBeqPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v3) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  intro u_base
        d_hi d_lo div_un1 div_un0 q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' q_hat
        q_addr ms ab hcarry2_nz hborrow
  -- Local lets matching beq_spec structure
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
  let q_out := if carry = 0 then q_hat + signExtend12 4095 + signExtend12 4095
               else q_hat + signExtend12 4095
  let un0_out := if carry = 0 then ab'.1 else ab.1
  let un1_out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2_out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3_out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  let carry_out := if carry = 0 then
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
    else carry
  let vtop_base := sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial call full (base+448 → base+516)
  have TF := divK_trial_call_full_spec sp j (4 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u_top u3 v3 ret_mem d_mem dlo_mem scratch_un0 base
    halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n4 sp j] at TF
  rw [u_addr8_eq_n4 sp j] at TF
  rw [vtop_eq_v3_n4 sp] at TF
  -- 2. Mulsub + correction addback + BEQ (base+516 → base+884)
  have MCA := divK_mulsub_correction_addback_beq_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base

  intro_lets at MCA
  have MCA0 := MCA hcarry2_nz hborrow
  -- 3. Store loop cpsBranch (base+884 → base+448/908)
  have SL := divK_store_loop_spec sp j q_out u4_out carry_out q_old base
  intro_lets at SL
  -- 4. Frame TF
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCA0
  seqFrame TFf MCA0
  -- 6. Frame store_loop
  have SLf := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3_out) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_out) **
     ((u_base + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v3) **
     (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  -- 7. Compose
  have full := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN4AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN4 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (fun h hp => by delta loopBodyN4AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN4 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- Section 16n4: Combined loop body cpsBranch for n=4 (all 4 paths unified)
-- ============================================================================

/-- Postcondition for one loop iteration at n=4.
    Output values are concrete parameters (not existentially quantified),
    preserving the relationship between outputs and inputs for semantic
    correctness proofs. -/
def loopBodyPostN4
    (sp j v0 v1 v2 v3 : Word)
    (x2v x10v x11v : Word)
    (un0v un1v un2v un3v u4v qv : Word)
    (retv dv dlov sunv : Word) : Assertion :=
  let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let j' := j + signExtend12 4095
  let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
  (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
  (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) **
  (.x2 ↦ᵣ x2v) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0v) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1v) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2v) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3v) **
  ((u_base + signExtend12 4064) ↦ₘ u4v) **
  (q_addr ↦ₘ qv) **
  (sp + signExtend12 3968 ↦ₘ retv) **
  (sp + signExtend12 3960 ↦ₘ dv) **
  (sp + signExtend12 3952 ↦ₘ dlov) **
  (sp + signExtend12 3944 ↦ₘ sunv)


end EvmAsm.Evm64
