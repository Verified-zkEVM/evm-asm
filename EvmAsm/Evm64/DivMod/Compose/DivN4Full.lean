/-
  EvmAsm.Evm64.DivMod.Compose.DivN4Full

  End-to-end composition for n=4 DIV (256-bit ÷ 256-bit, b[3]≠0, shift≠0).
  Composes: pre-loop (base→base+448) + loop body j=0 (base+448→base+904) +
            post-loop (base+904→base+1064).
-/

import EvmAsm.Evm64.DivMod.LoopBodyN4
import EvmAsm.Evm64.DivMod.Compose.FullPath

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Address simplification lemmas for j=0
-- ============================================================================

/-- u_base for j=0: sp + signExtend12 4056 - 0<<<3 = sp + signExtend12 4056 -/
private theorem j0_u_base_eq (sp : Word) :
    sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4056 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide]
  bv_omega

/-- q_addr for j=0: sp + signExtend12 4088 - 0<<<3 = sp + signExtend12 4088 -/
private theorem j0_q_addr_eq (sp : Word) :
    sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4088 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide]
  bv_omega

/-- u0 addr for j=0: u_base + signExtend12 0 = sp + signExtend12 4056 -/
private theorem j0_u0_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 = sp + signExtend12 4056 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide]
  bv_omega

/-- u1 addr for j=0: u_base + signExtend12 4088 = sp + signExtend12 4048 -/
private theorem j0_u1_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 = sp + signExtend12 4048 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) from by native_decide]
  bv_omega

/-- u2 addr for j=0: u_base + signExtend12 4080 = sp + signExtend12 4040 -/
private theorem j0_u2_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 = sp + signExtend12 4040 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by native_decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by native_decide]
  bv_omega

/-- u3 addr for j=0: u_base + signExtend12 4072 = sp + signExtend12 4032 -/
private theorem j0_u3_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 = sp + signExtend12 4032 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- u4 addr for j=0: u_base + signExtend12 4064 = sp + signExtend12 4024 -/
private theorem j0_u4_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 = sp + signExtend12 4024 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by native_decide,
    show signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) from by native_decide]
  bv_omega

/-- Validity: uhi addr for j=0: sp + signExtend12 4056 - ((0+4)<<<3) = sp + signExtend12 4024 -/
private theorem j0_uhi_addr_eq (sp : Word) :
    sp + signExtend12 4056 - ((0 : Word) + (4 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4024 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) from by native_decide]
  bv_omega

/-- Validity: ulo addr for j=0: (sp + signExtend12 4056 - ((0+4)<<<3)) + 8 = sp + signExtend12 4032 -/
private theorem j0_ulo_addr_eq (sp : Word) :
    (sp + signExtend12 4056 - ((0 : Word) + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4032 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- Validity: vtop addr for n=4: sp + ((4 + signExtend12 4095)<<<3) + signExtend12 32 = sp + signExtend12 56 -/
private theorem j0_vtop_addr_eq (sp : Word) :
    sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32 = sp + signExtend12 56 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4095 : BitVec 12) = (18446744073709551615 : Word) from by native_decide,
    show signExtend12 (32 : BitVec 12) = (32 : Word) from by native_decide,
    show signExtend12 (56 : BitVec 12) = (56 : Word) from by native_decide]
  bv_omega

/-- x1 in pre-loop: signExtend12 4 - 4 = 0 -/
private theorem se12_4_sub_4 :
    signExtend12 (4 : BitVec 12) - (4 : Word) = (0 : Word) := by native_decide

/-- x5 in loop body post for j=0: 0<<<3 = 0 -/
private theorem j0_shl3_eq :
    (0 : Word) <<< (3 : BitVec 6).toNat = (0 : Word) := by native_decide

/-- j' for j=0: 0 + signExtend12 4095 -/
private theorem j0_j'_eq :
    (0 : Word) + signExtend12 (4095 : BitVec 12) = signExtend12 (4095 : BitVec 12) := by
  bv_omega

-- ============================================================================
-- Composition: pre-loop + loop body (base → base+904) for n=4, shift≠0
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Pre-loop + single-iteration loop body for n=4 DIV (shift≠0).
    Composes base→base+448 (normalization) with base+448→base+904 (loop body j=0).
    Postcondition uses loopBodyPostN4 with existentials for computed values. -/
theorem evm_div_n4_preloop_loopbody_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 : Word)
    (n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_j  : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch : isValidDwordAccess (sp + signExtend12 3944) = true) :
    let shift := (clzResult b3).1
    let anti_shift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    let u4 := a3 >>> (anti_shift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    cpsTriple base (base + 904) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
       ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4032) ↦ₘ u3_old) **
       ((sp + signExtend12 4024) ↦ₘ u4_old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_old) **
       ((sp + signExtend12 3968) ↦ₘ ret_mem) ** ((sp + signExtend12 3960) ↦ₘ d_mem) **
       ((sp + signExtend12 3952) ↦ₘ dlo_mem) ** ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (loopBodyPostN4 sp (0 : Word) b0' b1' b2' b3' **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  intro shift anti_shift b3' b2' b1' b0' u4 u3 u2 u1 u0
  -- Step 1: Pre-loop (base → base+448)
  have hPL := evm_div_n4_to_loopSetup_spec sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem
    hbnz hb3nz hshift_nz hvalid hv_q0 hv_q1 hv_q2 hv_q3
    hv_u0 hv_u1 hv_u2 hv_u3 hv_u4 hv_u5 hv_u6 hv_u7 hv_n hv_shift
  intro_lets at hPL
  -- Frame pre-loop with x11, scratch memory
  have hPLf := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ v11) **
     ((sp + signExtend12 3976) ↦ₘ j_old) **
     ((sp + signExtend12 3968) ↦ₘ ret_mem) ** ((sp + signExtend12 3960) ↦ₘ d_mem) **
     ((sp + signExtend12 3952) ↦ₘ dlo_mem) ** ((sp + signExtend12 3944) ↦ₘ scratch_un0))
    (by pcFree) hPL
  -- Step 2: Loop body j=0 (base+448 → base+904)
  have hLB := divK_loop_body_n4_j0_spec sp j_old (4 : Word) shift u0
    (a0 >>> (anti_shift.toNat % 64)) v11 anti_shift
    b0' b1' b2' b3' u0 u1 u2 u3 u4 (0 : Word)
    ret_mem d_mem dlo_mem scratch_un0
    base
    hv_j hv_n
    (by rw [j0_uhi_addr_eq]; exact hv_u4)
    (by rw [j0_ulo_addr_eq]; exact hv_u3)
    (by rw [j0_vtop_addr_eq]
        exact ValidMemRange.fetch hvalid 7 _ (by omega) (by rfl))
    hv_ret hv_d hv_dlo hv_scratch
    halign
    (by rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by native_decide]
        exact ValidMemRange.fetch hvalid 4 _ (by omega) (by rfl))
    (by rw [j0_u0_addr_eq]; exact hv_u0)
    (by rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by native_decide]
        exact ValidMemRange.fetch hvalid 5 _ (by omega) (by rfl))
    (by rw [j0_u1_addr_eq]; exact hv_u1)
    (by rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by native_decide]
        exact ValidMemRange.fetch hvalid 6 _ (by omega) (by rfl))
    (by rw [j0_u2_addr_eq]; exact hv_u2)
    (by rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by native_decide]
        exact ValidMemRange.fetch hvalid 7 _ (by omega) (by rfl))
    (by rw [j0_u3_addr_eq]; exact hv_u3)
    (by rw [j0_u4_addr_eq]; exact hv_u4)
    (by rw [j0_q_addr_eq]; exact hv_q0)
  -- Rewrite x1 in pre-loop postcondition to match loop body's x1=0
  rw [se12_4_sub_4] at hPLf
  -- Expand let-bindings in loop body spec and canonicalize addresses
  dsimp only [] at hLB
  simp only [j0_u0_addr_eq, j0_q_addr_eq, j0_u1_addr_eq,
    j0_u2_addr_eq, j0_u3_addr_eq, j0_u4_addr_eq,
    signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56] at hLB
  -- Frame loop body with cells not used by it
  have hLBf := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hLB
  -- Compose pre-loop → loop body
  have hComp := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hPLf hLBf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    hComp

end EvmAsm.Rv64
