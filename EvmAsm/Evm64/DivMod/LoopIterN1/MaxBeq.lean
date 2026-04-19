/-
  EvmAsm.Evm64.DivMod.LoopIterN1.MaxBeq

  Loop body cpsTriple specs for n=1, max path with BEQ double-addback handling.
  Split from LoopIterN1.lean for faster builds.
-/

import EvmAsm.Evm64.DivMod.LoopBodyN1

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (slt_jpos_1 slt_jpos_2 slt_jpos_3)

-- ============================================================================
-- BEQ variants: max path addback with double-addback handling (no sorry)
-- ============================================================================

-- n=1, max+addback BEQ, j=0

set_option maxRecDepth 4096 in
theorem divK_loop_body_n1_max_addback_j0_beq_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopBodyN1AddbackBeqPost sp (0 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
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
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (0 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (0 : Word)] at TF
  rw [u_addr8_eq_n1 sp (0 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCA := divK_mulsub_correction_addback_beq_spec sp q_hat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (0 : Word) u0 vtop_base u1 v0 v2_old base

  intro_lets at MCA
  unfold isAddbackCarry2NzN1Max isAddbackCarry2Nz at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  have SL := divK_store_loop_j0_spec sp q_out u4_out carry_out q_old base
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3_out) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_out) **
     ((u_base + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- n=1, max+addback BEQ, j=3

set_option maxRecDepth 4096 in
theorem divK_loop_body_n1_max_addback_j3_beq_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 -(3 : Word) <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095
    let q_addr := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (3 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopBodyN1AddbackBeqPost sp (3 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
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
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (3 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (3 : Word)] at TF
  rw [u_addr8_eq_n1 sp (3 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCA := divK_mulsub_correction_addback_beq_spec sp q_hat (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (3 : Word) u0 vtop_base u1 v0 v2_old base

  intro_lets at MCA
  unfold isAddbackCarry2NzN1Max isAddbackCarry2Nz at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  have hj_pos := slt_jpos_3
  have SL := divK_store_loop_jgt0_spec sp (3 : Word) q_out u4_out carry_out q_old base hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3_out) **
     (sp + signExtend12 3976 ↦ₘ (3 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_out) **
     ((u_base + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- n=1, max+addback BEQ, j=1

set_option maxRecDepth 4096 in
theorem divK_loop_body_n1_max_addback_j1_beq_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 -(1 : Word) <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095
    let q_addr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopBodyN1AddbackBeqPost sp (1 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
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
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (1 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (1 : Word)] at TF
  rw [u_addr8_eq_n1 sp (1 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCA := divK_mulsub_correction_addback_beq_spec sp q_hat (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (1 : Word) u0 vtop_base u1 v0 v2_old base

  intro_lets at MCA
  unfold isAddbackCarry2NzN1Max isAddbackCarry2Nz at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  have hj_pos := slt_jpos_1
  have SL := divK_store_loop_jgt0_spec sp (1 : Word) q_out u4_out carry_out q_old base hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3_out) **
     (sp + signExtend12 3976 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_out) **
     ((u_base + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- n=1, max+addback BEQ, j=2

set_option maxRecDepth 4096 in
theorem divK_loop_body_n1_max_addback_j2_beq_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 -(2 : Word) <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095
    let q_addr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopBodyN1AddbackBeqPost sp (2 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
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
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (2 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (2 : Word)] at TF
  rw [u_addr8_eq_n1 sp (2 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCA := divK_mulsub_correction_addback_beq_spec sp q_hat (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (2 : Word) u0 vtop_base u1 v0 v2_old base

  intro_lets at MCA
  unfold isAddbackCarry2NzN1Max isAddbackCarry2Nz at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  have hj_pos := slt_jpos_2
  have SL := divK_store_loop_jgt0_spec sp (2 : Word) q_out u4_out carry_out q_old base hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3_out) **
     (sp + signExtend12 3976 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_out) **
     ((u_base + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

end EvmAsm.Evm64
