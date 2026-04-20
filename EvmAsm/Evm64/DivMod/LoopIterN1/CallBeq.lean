/-
  EvmAsm.Evm64.DivMod.LoopIterN1.CallBeq

  Loop body cpsTriple specs for n=1, call path with BEQ double-addback handling.
  Split from LoopIterN1.lean for faster builds.
-/

import EvmAsm.Evm64.DivMod.LoopBodyN1

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (slt_jpos_1 slt_jpos_2 slt_jpos_3)

-- ============================================================================
-- BEQ variants: call path addback with double-addback handling (no sorry)
-- ============================================================================

-- n=1, call+addback BEQ, j=0

set_option maxRecDepth 4096 in
theorem divK_loop_body_n1_call_addback_j0_beq_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isAddbackBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top)
    (hcarry2_nz : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
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
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN1CallAddbackBeqPostJ sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  let dHi := v0 >>> (32 : BitVec 6).toNat
  let dLo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 dHi; let rhat := u1 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let q_dlo := q1c * dLo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi; let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0_dlo := q0c * dLo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isAddbackBorrowN1Call div128Quot at hborrow
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (0 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u1 u0 v0 ret_mem d_mem dlo_mem scratch_un0 base
    halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (0 : Word)] at TF
  rw [u_addr8_eq_n1 sp (0 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
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
  let carryOut := if carry = 0 then
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
    else carry
  have MCA := divK_mulsub_correction_addback_beq_spec sp q_hat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' dHi q0_dlo q1' (base + 516) base

  intro_lets at MCA
  unfold isAddbackCarry2NzN1Call isAddbackCarry2Nz div128Quot at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  have SL := divK_store_loop_j0_spec sp q_out u4_out carryOut q_old base
  intro_lets at SL
  have TFf := cpsTriple_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frameR
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3_out) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_out) **
     ((u_base + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallAddbackBeqPostJ div128Quot div128DLo div128Un0
            loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- n=1, call+addback BEQ, j=1

set_option maxRecDepth 4096 in
theorem divK_loop_body_n1_call_addback_j1_beq_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isAddbackBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top)
    (hcarry2_nz : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
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
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN1CallAddbackBeqPostJ sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  let dHi := v0 >>> (32 : BitVec 6).toNat
  let dLo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 dHi; let rhat := u1 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let q_dlo := q1c * dLo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi; let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0_dlo := q0c * dLo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isAddbackBorrowN1Call div128Quot at hborrow
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (1 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u1 u0 v0 ret_mem d_mem dlo_mem scratch_un0 base
    halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (1 : Word)] at TF
  rw [u_addr8_eq_n1 sp (1 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
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
  let carryOut := if carry = 0 then
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
    else carry
  have MCA := divK_mulsub_correction_addback_beq_spec sp q_hat (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' dHi q0_dlo q1' (base + 516) base

  intro_lets at MCA
  unfold isAddbackCarry2NzN1Call isAddbackCarry2Nz div128Quot at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  have hj_pos := slt_jpos_1
  have SL := divK_store_loop_jgt0_spec sp (1 : Word) q_out u4_out carryOut q_old base hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frameR
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3_out) **
     (sp + signExtend12 3976 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_out) **
     ((u_base + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallAddbackBeqPostJ div128Quot div128DLo div128Un0
            loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- n=1, call+addback BEQ, j=2

set_option maxRecDepth 4096 in
theorem divK_loop_body_n1_call_addback_j2_beq_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isAddbackBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top)
    (hcarry2_nz : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
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
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN1CallAddbackBeqPostJ sp base (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  let dHi := v0 >>> (32 : BitVec 6).toNat
  let dLo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 dHi; let rhat := u1 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let q_dlo := q1c * dLo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi; let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0_dlo := q0c * dLo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isAddbackBorrowN1Call div128Quot at hborrow
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (2 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u1 u0 v0 ret_mem d_mem dlo_mem scratch_un0 base
    halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (2 : Word)] at TF
  rw [u_addr8_eq_n1 sp (2 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
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
  let carryOut := if carry = 0 then
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
    else carry
  have MCA := divK_mulsub_correction_addback_beq_spec sp q_hat (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' dHi q0_dlo q1' (base + 516) base

  intro_lets at MCA
  unfold isAddbackCarry2NzN1Call isAddbackCarry2Nz div128Quot at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  have hj_pos := slt_jpos_2
  have SL := divK_store_loop_jgt0_spec sp (2 : Word) q_out u4_out carryOut q_old base hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frameR
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3_out) **
     (sp + signExtend12 3976 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_out) **
     ((u_base + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallAddbackBeqPostJ div128Quot div128DLo div128Un0
            loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- n=1, call+addback BEQ, j=3

set_option maxRecDepth 4096 in
theorem divK_loop_body_n1_call_addback_j3_beq_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isAddbackBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top)
    (hcarry2_nz : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
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
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN1CallAddbackBeqPostJ sp base (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  let dHi := v0 >>> (32 : BitVec 6).toNat
  let dLo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 dHi; let rhat := u1 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let q_dlo := q1c * dLo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi; let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0_dlo := q0c * dLo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isAddbackBorrowN1Call div128Quot at hborrow
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (3 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u1 u0 v0 ret_mem d_mem dlo_mem scratch_un0 base
    halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (3 : Word)] at TF
  rw [u_addr8_eq_n1 sp (3 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
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
  let carryOut := if carry = 0 then
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
    else carry
  have MCA := divK_mulsub_correction_addback_beq_spec sp q_hat (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' dHi q0_dlo q1' (base + 516) base

  intro_lets at MCA
  unfold isAddbackCarry2NzN1Call isAddbackCarry2Nz div128Quot at hcarry2_nz
  have MCA0 := MCA hcarry2_nz hborrow
  have hj_pos := slt_jpos_3
  have SL := divK_store_loop_jgt0_spec sp (3 : Word) q_out u4_out carryOut q_old base hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frameR
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3_out) **
     (sp + signExtend12 3976 ↦ₘ (3 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_out) **
     ((u_base + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallAddbackBeqPostJ div128Quot div128DLo div128Un0
            loopBodyN1AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full


end EvmAsm.Evm64
