/-
  EvmAsm.Evm64.DivMod.LoopBodyN4Concrete

  Concrete (non-existential) loop body postcondition for n=4 at j=0.
  Exposes the full register-level computation as let-bindings, enabling
  semantic correctness proofs via mulsub_register_4limb_val256.

  The key output values (q_hat, un0-un3, borrow) are concrete functions
  of the inputs, allowing callers to apply the Euclidean bridge theorems.
-/

import EvmAsm.Evm64.DivMod.LoopBodyN4
import EvmAsm.Evm64.EvmWordArith.DivMulSubCarry

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Concrete output computation for one n=4 loop iteration
-- ============================================================================

/-- Compute the trial quotient for one loop iteration.
    If u_top < v3 (BLTU taken), uses 128÷64 trial division (div128).
    Otherwise uses MAX64 = signExtend12 4095 = 2^64-1. -/
def trialQuotientN4 (v3 u3 u_top : Word) : Word :=
  if BitVec.ult u_top v3 then
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
    (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  else signExtend12 (4095 : BitVec 12)

/-- Mulsub: compute u - q*v for 4 limbs, returning (un0, un1, un2, un3, c3). -/
def mulsubN4 (q v0 v1 v2 v3 u0 u1 u2 u3 : Word) :
    Word × Word × Word × Word × Word :=
  let p0_lo := q * v0; let p0_hi := rv64_mulhu q v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q * v1; let p1_hi := rv64_mulhu q v1
  let fs1 := p1_lo + c0
  let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi
  let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q * v2; let p2_hi := rv64_mulhu q v2
  let fs2 := p2_lo + c1
  let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi
  let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q * v3; let p3_hi := rv64_mulhu q v3
  let fs3 := p3_lo + c2
  let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi
  let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  (un0, un1, un2, un3, c3)

/-- Addback: compute u + v for 4 limbs (used after mulsub underflow). -/
def addbackN4 (un0 un1 un2 un3 u4_new v0 v1 v2 v3 : Word) :
    Word × Word × Word × Word × Word :=
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0
  let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0
  let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1
  let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1
  let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2
  let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2
  let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3
  let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  let aco3 := ac1_3 ||| ac2_3
  let aun4 := u4_new + aco3
  (aun0, aun1, aun2, aun3, aun4)

/-- Complete loop body output computation for n=4 at j=0.
    Returns the 13 output values as a let-binding chain in the return type.
    Mirrors the exact register-level computation of the Knuth D loop body. -/
def loopBodyN4Output
    (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word)
    (ret_mem d_mem dlo_mem scratch_un0 base : Word) :
    Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word :=
  let q_hat := trialQuotientN4 v3 u3 u_top
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let un0 := ms.1; let un1 := ms.2.1; let un2 := ms.2.2.1
  let un3 := ms.2.2.2.1; let c3 := ms.2.2.2.2
  let u4_new := u_top - c3
  let borrow := if BitVec.ult u_top c3 then (1 : Word) else 0
  let ab := addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3
  let aun0 := ab.1; let aun1 := ab.2.1; let aun2 := ab.2.2.1
  let aun3 := ab.2.2.2.1; let aun4 := ab.2.2.2.2
  let d_lo := (v3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  -- Final output values (path-selected)
  let out_x2v := if borrow = 0 then un3 else aun3
  let out_x10v := c3
  let out_x11v := if borrow = 0 then q_hat else q_hat + signExtend12 4095
  let out_un0v := if borrow = 0 then un0 else aun0
  let out_un1v := if borrow = 0 then un1 else aun1
  let out_un2v := if borrow = 0 then un2 else aun2
  let out_un3v := if borrow = 0 then un3 else aun3
  let out_u4v := if borrow = 0 then u4_new else aun4
  let out_qv := if borrow = 0 then q_hat else q_hat + signExtend12 4095
  let out_retv := if BitVec.ult u_top v3 then (base + 516) else ret_mem
  let out_dv := if BitVec.ult u_top v3 then v3 else d_mem
  let out_dlov := if BitVec.ult u_top v3 then d_lo else dlo_mem
  let out_sunv := if BitVec.ult u_top v3 then div_un0 else scratch_un0
  (out_x2v, out_x10v, out_x11v, out_un0v, out_un1v, out_un2v, out_un3v,
   out_u4v, out_qv, out_retv, out_dv, out_dlov, out_sunv)

-- ============================================================================
-- Semantic bridge: mulsub equation from loopBodyN4Output
-- ============================================================================

/-- The trial quotient from the loop body output. -/
def loopBodyN4_qhat (v3 u3 u_top : Word) : Word :=
  trialQuotientN4 v3 u3 u_top

/-- The mulsub carry from the loop body output. -/
def loopBodyN4_carry (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Word :=
  let q_hat := trialQuotientN4 v3 u3 u_top
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  ms.2.2.2.2  -- c3

/-- The mulsub borrow flag (1 if underflow, 0 otherwise). -/
def loopBodyN4_borrow (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Word :=
  let c3 := loopBodyN4_carry v0 v1 v2 v3 u0 u1 u2 u3 u_top
  if BitVec.ult u_top c3 then (1 : Word) else 0

-- ============================================================================
-- Semantic bridge: mulsubN4 satisfies the val256 Euclidean equation
-- ============================================================================

open EvmWord in
/-- The mulsubN4 computation satisfies the 4-limb Euclidean equation.
    This is the key bridge to semantic correctness: the register-level
    multiply-subtract produces values satisfying
    `val256(u) + carry * 2^256 = val256(u_new) + q * val256(v)`.

    Proof: unfold mulsubN4 to expose the mulsub let-bindings, which
    match exactly the pattern of mulsub_register_4limb_val256. -/
theorem mulsubN4_val256_eq (q v0 v1 v2 v3 u0 u1 u2 u3 : Word) :
    let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
    let un0 := ms.1; let un1 := ms.2.1; let un2 := ms.2.2.1
    let un3 := ms.2.2.2.1; let c3 := ms.2.2.2.2
    val256 u0 u1 u2 u3 + c3.toNat * 2^256 =
      val256 un0 un1 un2 un3 + q.toNat * val256 v0 v1 v2 v3 := by
  -- Unfold mulsubN4 to expose the register-level let-bindings
  simp only [mulsubN4]
  -- The let-bindings now match mulsub_register_4limb_val256 exactly:
  -- fs0 = q * v0 + 0, ba0 = borrow_add, un0 = u0 - fs0, etc.
  -- Note: signExtend12 0 = (0 : Word), so fs0 = q * v0 + 0
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  simp only [hse0]
  exact mulsub_register_4limb_val256 q v0 v1 v2 v3 u0 u1 u2 u3

-- ============================================================================
-- Per-case concrete specs: loop body at j=0 with mulsubN4-based postcondition
-- ============================================================================

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12800000 in
/-- Concrete loop body for n=4, j=0, MAX+SKIP case (BLTU not taken, borrow=0).
    Postcondition uses mulsubN4 outputs directly — no existentials. -/
theorem divK_loop_body_n4_j0_max_skip_concrete
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - ((0 : Word) + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - ((0 : Word) + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_hat := signExtend12 (4095 : BitVec 12)
    let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
    let un0 := ms.1; let un1 := ms.2.1; let un2 := ms.2.2.1
    let un3 := ms.2.2.2.1; let c3 := ms.2.2.2.2
    let u4_new := u_top - c3
    (if BitVec.ult u_top c3 then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
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
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (fun h => loopBodyPostN4 sp (0 : Word) v0 v1 v2 v3
        un3 c3 q_hat un0 un1 un2 un3 u4_new q_hat
        ret_mem d_mem dlo_mem scratch_un0 h) := by
  intro u_base q_addr q_hat ms un0 un1 un2 un3 c3 u4_new hborrow
  let vtop_base := sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (0 : Word) (4 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u_top u3 v3 base hv_j hv_n1 hv_uhi hv_ulo hv_vtop hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n4 sp (0 : Word)] at TF
  rw [u_addr8_eq_n4 sp (0 : Word)] at TF
  rw [vtop_eq_v3_n4 sp] at TF
  have MCS := divK_mulsub_correction_skip_spec sp q_hat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (0 : Word) u3 vtop_base u_top v3 v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCS
  have MCS0 := MCS hborrow
  have SL := divK_store_loop_j0_spec sp q_hat u4_new (0 : Word) q_old base hv_q
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCS0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)))
    (by pcFree) SL
  have fullt := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  have fullf := cpsTriple_frame_left _ _ _ _ _
    ((sp + signExtend12 3968 ↦ₘ ret_mem) **
     (sp + signExtend12 3960 ↦ₘ d_mem) **
     (sp + signExtend12 3952 ↦ₘ dlo_mem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) fullt
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by unfold loopBodyPostN4; xperm_hyp hp)
    fullf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12800000 in
/-- Concrete loop body for n=4, j=0, MAX+ADDBACK case (BLTU not taken, borrow≠0).
    Postcondition uses addbackN4 outputs directly — no existentials. -/
theorem divK_loop_body_n4_j0_max_addback_concrete
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - ((0 : Word) + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - ((0 : Word) + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_hat := signExtend12 (4095 : BitVec 12)
    let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
    let un0 := ms.1; let un1 := ms.2.1; let un2 := ms.2.2.1
    let un3 := ms.2.2.2.1; let c3 := ms.2.2.2.2
    let u4_new := u_top - c3
    let ab := addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3
    let aun0 := ab.1; let aun1 := ab.2.1; let aun2 := ab.2.2.1
    let aun3 := ab.2.2.2.1; let aun4 := ab.2.2.2.2
    let q_hat' := q_hat + signExtend12 4095
    (if BitVec.ult u_top c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
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
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (fun h => loopBodyPostN4 sp (0 : Word) v0 v1 v2 v3
        aun3 c3 q_hat' aun0 aun1 aun2 aun3 aun4 q_hat'
        ret_mem d_mem dlo_mem scratch_un0 h) := by
  intro u_base q_addr q_hat ms un0 un1 un2 un3 c3 u4_new ab aun0 aun1 aun2 aun3 aun4 q_hat' hborrow
  -- Manual addback let-bindings (needed for aco3 in store_loop)
  let upc0' := un0 + (signExtend12 0 : Word)
  let ac1_0' := if BitVec.ult upc0' (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0' := upc0' + v0
  let ac2_0' := if BitVec.ult aun0' v0 then (1 : Word) else 0
  let aco0' := ac1_0' ||| ac2_0'
  let upc1' := un1 + aco0'
  let ac1_1' := if BitVec.ult upc1' aco0' then (1 : Word) else 0
  let aun1' := upc1' + v1
  let ac2_1' := if BitVec.ult aun1' v1 then (1 : Word) else 0
  let aco1' := ac1_1' ||| ac2_1'
  let upc2' := un2 + aco1'
  let ac1_2' := if BitVec.ult upc2' aco1' then (1 : Word) else 0
  let aun2' := upc2' + v2
  let ac2_2' := if BitVec.ult aun2' v2 then (1 : Word) else 0
  let aco2' := ac1_2' ||| ac2_2'
  let upc3' := un3 + aco2'
  let ac1_3' := if BitVec.ult upc3' aco2' then (1 : Word) else 0
  let aun3' := upc3' + v3
  let ac2_3' := if BitVec.ult aun3' v3 then (1 : Word) else 0
  let aco3' := ac1_3' ||| ac2_3'
  let vtop_base := sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (0 : Word) (4 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u_top u3 v3 base hv_j hv_n1 hv_uhi hv_ulo hv_vtop hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n4 sp (0 : Word)] at TF
  rw [u_addr8_eq_n4 sp (0 : Word)] at TF
  rw [vtop_eq_v3_n4 sp] at TF
  have MCA := divK_mulsub_correction_addback_spec sp q_hat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (0 : Word) u3 vtop_base u_top v3 v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCA
  have MCA0 := MCA hborrow
  have SL := divK_store_loop_j0_spec sp q_hat' aun4 aco3' q_old base hv_q
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)))
    (by pcFree) SL
  have fullt := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  have fullf := cpsTriple_frame_left _ _ _ _ _
    ((sp + signExtend12 3968 ↦ₘ ret_mem) **
     (sp + signExtend12 3960 ↦ₘ d_mem) **
     (sp + signExtend12 3952 ↦ₘ dlo_mem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) fullt
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by unfold loopBodyPostN4; xperm_hyp hp)
    fullf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12800000 in
/-- Concrete loop body for n=4, j=0, CALL+SKIP case (BLTU taken, borrow=0).
    Postcondition uses mulsubN4 outputs directly — no existentials.
    Scratch memory (ret, d, dlo, un0) updated to div128 values. -/
theorem divK_loop_body_n4_j0_call_skip_concrete
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - ((0 : Word) + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - ((0 : Word) + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- div128 intermediates for q_hat
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
    -- mulsub outputs
    let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
    let un0 := ms.1; let un1 := ms.2.1; let un2 := ms.2.2.1
    let un3 := ms.2.2.2.1; let c3 := ms.2.2.2.2
    let u4_new := u_top - c3
    (if BitVec.ult u_top c3 then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
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
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (fun h => loopBodyPostN4 sp (0 : Word) v0 v1 v2 v3
        un3 c3 q_hat un0 un1 un2 un3 u4_new q_hat
        (base + 516) v3 d_lo div_un0 h) := by
  intro u_base q_addr
        d_hi d_lo div_un1 div_un0
        q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' q_hat
        ms un0 un1 un2 un3 c3 u4_new hborrow
  let vtop_base := sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (0 : Word) (4 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u_top u3 v3 ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n4 sp (0 : Word)] at TF
  rw [u_addr8_eq_n4 sp (0 : Word)] at TF
  rw [vtop_eq_v3_n4 sp] at TF
  have MCS := divK_mulsub_correction_skip_spec sp q_hat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCS
  have MCS0 := MCS hborrow
  have SL := divK_store_loop_j0_spec sp q_hat u4_new (0 : Word) q_old base hv_q
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCS0
  have SLf := cpsTriple_frame_left _ _ _ _ _
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
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by unfold loopBodyPostN4; xperm_hyp hp)
    full

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12800000 in
/-- Concrete loop body for n=4, j=0, CALL+ADDBACK case (BLTU taken, borrow≠0).
    Postcondition uses addbackN4 outputs directly — no existentials.
    Scratch memory (ret, d, dlo, un0) updated to div128 values. -/
theorem divK_loop_body_n4_j0_call_addback_concrete
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - ((0 : Word) + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - ((0 : Word) + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- div128 intermediates for q_hat
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
    -- mulsub outputs
    let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
    let un0 := ms.1; let un1 := ms.2.1; let un2 := ms.2.2.1
    let un3 := ms.2.2.2.1; let c3 := ms.2.2.2.2
    let u4_new := u_top - c3
    -- addback outputs
    let ab := addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3
    let aun0 := ab.1; let aun1 := ab.2.1; let aun2 := ab.2.2.1
    let aun3 := ab.2.2.2.1; let aun4 := ab.2.2.2.2
    let q_hat' := q_hat + signExtend12 4095
    (if BitVec.ult u_top c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
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
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (fun h => loopBodyPostN4 sp (0 : Word) v0 v1 v2 v3
        aun3 c3 q_hat' aun0 aun1 aun2 aun3 aun4 q_hat'
        (base + 516) v3 d_lo div_un0 h) := by
  intro u_base q_addr
        d_hi d_lo div_un1 div_un0
        q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' q_hat
        ms un0 un1 un2 un3 c3 u4_new ab aun0 aun1 aun2 aun3 aun4 q_hat' hborrow
  -- Manual addback let-bindings (needed for aco3 in store_loop)
  let upc0' := un0 + (signExtend12 0 : Word)
  let ac1_0' := if BitVec.ult upc0' (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0' := upc0' + v0
  let ac2_0' := if BitVec.ult aun0' v0 then (1 : Word) else 0
  let aco0' := ac1_0' ||| ac2_0'
  let upc1' := un1 + aco0'
  let ac1_1' := if BitVec.ult upc1' aco0' then (1 : Word) else 0
  let aun1' := upc1' + v1
  let ac2_1' := if BitVec.ult aun1' v1 then (1 : Word) else 0
  let aco1' := ac1_1' ||| ac2_1'
  let upc2' := un2 + aco1'
  let ac1_2' := if BitVec.ult upc2' aco1' then (1 : Word) else 0
  let aun2' := upc2' + v2
  let ac2_2' := if BitVec.ult aun2' v2 then (1 : Word) else 0
  let aco2' := ac1_2' ||| ac2_2'
  let upc3' := un3 + aco2'
  let ac1_3' := if BitVec.ult upc3' aco2' then (1 : Word) else 0
  let aun3' := upc3' + v3
  let ac2_3' := if BitVec.ult aun3' v3 then (1 : Word) else 0
  let aco3' := ac1_3' ||| ac2_3'
  let vtop_base := sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (0 : Word) (4 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u_top u3 v3 ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n4 sp (0 : Word)] at TF
  rw [u_addr8_eq_n4 sp (0 : Word)] at TF
  rw [vtop_eq_v3_n4 sp] at TF
  have MCA := divK_mulsub_correction_addback_spec sp q_hat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCA
  have MCA0 := MCA hborrow
  have SL := divK_store_loop_j0_spec sp q_hat' aun4 aco3' q_old base hv_q
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v3) **
     (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by unfold loopBodyPostN4; xperm_hyp hp)
    full

end EvmAsm.Evm64
