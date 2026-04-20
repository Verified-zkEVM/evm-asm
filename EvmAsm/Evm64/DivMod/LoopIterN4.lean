/-
  EvmAsm.Evm64.DivMod.LoopIterN4

  Loop body cpsTriple specs for n=4 at j=0.
  These are the j=0-specialized versions of the LoopBodyN4 cpsBranch specs,
  using divK_store_loop_j0_spec to eliminate the loop-back branch and
  produce clean cpsTriples from base+448 to base+904.
-/

import EvmAsm.Evm64.DivMod.LoopBodyN4

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- n=4, BLTU not-taken (max path) + BEQ skip, j=0 → cpsTriple to base+904
-- ============================================================================

set_option maxRecDepth 4096 in
/-- Loop body cpsTriple for n=4, max+skip, j=0.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+904. -/
theorem divK_loop_body_n4_max_skip_j0_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qHat : Word := signExtend12 4095  -- MAX64
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow = 0
    (if BitVec.ult u_top (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (qAddr ↦ₘ q_old))
      (loopBodyN4SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base qHat qAddr hborrow
  -- Expand mulsub computation locally

  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0
  let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi
  let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1
  let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi
  let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2
  let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi
  let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3

  let vtopBase := sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial max full (base+448 → base+516)
  have TF := divK_trial_max_full_spec sp (0 : Word) (4 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u_top u3 v3 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n4 sp (0 : Word)] at TF
  rw [u_addr8_eq_n4 sp (0 : Word)] at TF
  rw [vtop_eq_v3_n4 sp] at TF
  -- 2. Mulsub + correction skip (base+516 → base+880)
  have MCS := divK_mulsub_correction_skip_spec sp qHat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (0 : Word) u3 vtopBase u_top v3 v2_old base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  -- 3. Store + loop exit j=0 (cpsTriple base+880 → base+904)
  have SL := divK_store_loop_j0_spec sp qHat u4_new (0 : Word) q_old base
  intro_lets at SL
  -- 4. Frame TF with mulsub cells
  have TFf := cpsTriple_frameR
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     (qAddr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCS0
  seqFrame TFf MCS0
  -- 6. Frame store_loop_j0 with remaining atoms
  have SLf := cpsTriple_frameR
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)))
    (by pcFree) SL
  -- 7. Compose pre_store (cpsTriple) with SLf (cpsTriple)
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  -- 8. Permute final cpsTriple to match target
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN4SkipPost loopBodySkipPost mulsubN4 loopExitPostN4 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=4, BLTU taken (call path) + BEQ skip, j=0 → cpsTriple to base+904
-- ============================================================================

set_option maxRecDepth 4096 in
/-- Loop body cpsTriple for n=4, call+skip, j=0.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+904. -/
theorem divK_loop_body_n4_call_skip_j0_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
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
    let qHat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow = 0
    (if BitVec.ult u_top (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (qAddr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN4SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v3) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  intro u_base
        d_hi d_lo div_un1 div_un0 q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' qHat
        qAddr hborrow

  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3

  let vtopBase := sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial call full (base+448 → base+516)
  have TF := divK_trial_call_full_spec sp (0 : Word) (4 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u_top u3 v3 ret_mem d_mem dlo_mem scratch_un0 base
    halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n4 sp (0 : Word)] at TF
  rw [u_addr8_eq_n4 sp (0 : Word)] at TF
  rw [vtop_eq_v3_n4 sp] at TF
  -- 2. Mulsub + correction skip (base+516 → base+880)
  have MCS := divK_mulsub_correction_skip_spec sp qHat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  -- 3. Store + loop exit j=0 (cpsTriple base+880 → base+904)
  have SL := divK_store_loop_j0_spec sp qHat u4_new (0 : Word) q_old base
  intro_lets at SL
  -- 4. Frame TF
  have TFf := cpsTriple_frameR
    (((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     (qAddr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCS0
  seqFrame TFf MCS0
  -- 6. Frame store_loop_j0
  have SLf := cpsTriple_frameR
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
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
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN4SkipPost loopBodySkipPost mulsubN4 loopExitPostN4 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=4, BLTU not-taken (max path) + BEQ addback (beq variant), j=0
-- Uses divK_mulsub_correction_addback_beq_spec to eliminate sorry.
-- ============================================================================

set_option maxRecDepth 4096 in
/-- Loop body cpsTriple for n=4, max+addback (beq variant), j=0.
    Uses the beq_spec which handles both carry=0 and carry≠0 internally,
    eliminating the sorry for aco3 ≠ 0. -/
theorem divK_loop_body_n4_max_addback_j0_beq_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u_top v3)
    (hcarry2_nz : isAddbackCarry2NzN4Max v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qHat : Word := signExtend12 4095  -- MAX64
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult u_top (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (qAddr ↦ₘ q_old))
      (loopBodyN4AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base qHat qAddr hborrow
  -- Local lets matching beq_spec structure (NOT the old inline expansion)
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
  let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
               else qHat + signExtend12 4095
  let un0_out := if carry = 0 then ab'.1 else ab.1
  let un1_out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2_out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3_out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  let carry_out := if carry = 0 then
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
    else carry
  let vtopBase := sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial max full (base+448 → base+516)
  have TF := divK_trial_max_full_spec sp (0 : Word) (4 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u_top u3 v3 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n4 sp (0 : Word)] at TF
  rw [u_addr8_eq_n4 sp (0 : Word)] at TF
  rw [vtop_eq_v3_n4 sp] at TF
  -- 2. Use beq_spec instead of old spec (NO sorry!)
  have MCA := divK_mulsub_correction_addback_beq_spec sp qHat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (0 : Word) u3 vtopBase u_top v3 v2_old base

  intro_lets at MCA
  unfold isAddbackCarry2NzN4Max isAddbackCarry2Nz at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  -- 3. Store loop (use q_out, u4_out, carry_out)
  have SL := divK_store_loop_j0_spec sp q_out u4_out carry_out q_old base
  intro_lets at SL
  -- 4. Frame TF with mulsub cells
  have TFf := cpsTriple_frameR
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     (qAddr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCA0
  seqFrame TFf MCA0
  -- 6. Frame store_loop_j0 with remaining atoms
  have SLf := cpsTriple_frameR
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3_out) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_out) **
     ((u_base + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)))
    (by pcFree) SL
  -- 7. Compose pre_store (cpsTriple) with SLf (cpsTriple)
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  -- 8. Permute final cpsTriple to match target
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN4AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN4 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=4, BLTU taken (call path) + BEQ addback (beq variant), j=0
-- Uses divK_mulsub_correction_addback_beq_spec to eliminate sorry.
-- ============================================================================

set_option maxRecDepth 4096 in
/-- Loop body cpsTriple for n=4, call+addback (beq variant), j=0.
    Uses the beq_spec which handles both carry=0 and carry≠0 internally,
    eliminating the sorry for aco3 ≠ 0. -/
theorem divK_loop_body_n4_call_addback_j0_beq_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u_top v3)
    (hcarry2_nz : isAddbackCarry2NzN4Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
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
    let qHat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult u_top (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (qAddr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN4AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v3) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  intro u_base
        d_hi d_lo div_un1 div_un0 q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' qHat
        qAddr hborrow
  -- Local lets matching beq_spec structure
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
  let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
               else qHat + signExtend12 4095
  let un0_out := if carry = 0 then ab'.1 else ab.1
  let un1_out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2_out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3_out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  let carry_out := if carry = 0 then
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
    else carry
  let vtopBase := sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial call full (base+448 → base+516)
  have TF := divK_trial_call_full_spec sp (0 : Word) (4 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u_top u3 v3 ret_mem d_mem dlo_mem scratch_un0 base
    halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n4 sp (0 : Word)] at TF
  rw [u_addr8_eq_n4 sp (0 : Word)] at TF
  rw [vtop_eq_v3_n4 sp] at TF
  -- 2. Use beq_spec instead of old spec (NO sorry!)
  have MCA := divK_mulsub_correction_addback_beq_spec sp qHat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base

  intro_lets at MCA
  unfold isAddbackCarry2NzN4Call isAddbackCarry2Nz div128Quot at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  -- 3. Store loop (use q_out, u4_out, carry_out)
  have SL := divK_store_loop_j0_spec sp q_out u4_out carry_out q_old base
  intro_lets at SL
  -- 4. Frame TF
  have TFf := cpsTriple_frameR
    (((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     (qAddr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCA0
  seqFrame TFf MCA0
  -- 6. Frame store_loop_j0
  have SLf := cpsTriple_frameR
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3_out) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
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
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN4AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN4 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

end EvmAsm.Evm64
