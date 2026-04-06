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

/-- Simplify x + 0 for Word (matches after signExtend12_0/j0_shl3_eq rewrites) -/
private theorem word_add_zero (x : Word) : x + (0 : Word) = x := by bv_omega

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

/-- u_base for j=0 after shl3: sp + SE12(4056) - 0 = sp + SE12(4056) -/
private theorem j0_sub_zero (sp : Word) :
    sp + signExtend12 4056 - (0 : Word) = sp + signExtend12 4056 := by bv_omega

/-- q_addr for j=0 after shl3: sp + SE12(4088) - 0 = sp + SE12(4088) -/
private theorem j0_q_sub_zero (sp : Word) :
    sp + signExtend12 4088 - (0 : Word) = sp + signExtend12 4088 := by bv_omega

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
  -- Lift loop body from sharedDivModCode to divCode
  have hLB := cpsTriple_extend_code (sharedDivModCode_sub_divCode base) hLB
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

-- ============================================================================
-- Helper: sequential composition with existential intermediate assertion
-- ============================================================================

/-- Sequential composition where the intermediate has existentials.
    For each value v, the second triple maps Q v to R. -/
private theorem cpsTriple_seq_ex_same_cr {V : Type} (s m e : Word) (cr : CodeReq)
    (P : Assertion) (Q : V → Assertion) (R : Assertion)
    (h1 : cpsTriple s m cr P (fun h => ∃ v, Q v h))
    (h2 : ∀ v, cpsTriple m e cr (Q v) R) :
    cpsTriple s e cr P R := by
  intro F hF st hcr hPF hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF st hcr hPF hpc
  obtain ⟨h_heap, hcompat, h_q, h_f, heq, hdisj, ⟨v, hQv⟩, hFv⟩ := hQF
  have hQvF : (Q v ** F).holdsFor s1 := ⟨h_heap, hcompat, h_q, h_f, heq, hdisj, hQv, hFv⟩
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ :=
    h2 v F hF s1 (CodeReq.SatisfiedBy_preserved cr k1 _ _ hstep1 hcr) hQvF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 st s1 s2 hstep1 hstep2, hpc2, hRF⟩

-- ============================================================================
-- Full end-to-end: base → base+1064 for n=4 DIV (shift≠0)
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Full n=4 DIV spec (shift≠0): base → base+1064.
    Composes pre-loop + loop body (base→base+904) with
    preamble + denorm + epilogue (base+904→base+1064). -/
theorem evm_div_n4_full_spec (sp base : Word)
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
    cpsTriple base (base + 1064) (divCode base)
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
      (fun h => ∃ (qv0 x2out x1out x11out : Word)
        (u0out u1out u2out u3out u4out : Word)
        (retout dout dlout scout : Word),
        ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ qv0) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
         (.x2 ↦ᵣ x2out) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
         (.x1 ↦ᵣ x1out) ** (.x11 ↦ᵣ x11out) **
         ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
         ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
         ((sp + 32) ↦ₘ qv0) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 3992) ↦ₘ shift) **
         ((sp + signExtend12 4056) ↦ₘ u0out) ** ((sp + signExtend12 4048) ↦ₘ u1out) **
         ((sp + signExtend12 4040) ↦ₘ u2out) ** ((sp + signExtend12 4032) ↦ₘ u3out) **
         ((sp + signExtend12 4088) ↦ₘ qv0) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 4024) ↦ₘ u4out) **
         ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 3968) ↦ₘ retout) ** ((sp + signExtend12 3960) ↦ₘ dout) **
         ((sp + signExtend12 3952) ↦ₘ dlout) ** ((sp + signExtend12 3944) ↦ₘ scout)) h) := by
  intro shift anti_shift b3' b2' b1' b0'
  -- Step 1: Pre-loop + loop body (base → base+904)
  have hPLLB := evm_div_n4_preloop_loopbody_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7
    n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0
    hbnz hb3nz hshift_nz hvalid halign
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch
  intro_lets at hPLLB
  -- Step 2: Compose via cpsTriple definition to handle existential intermediate
  show cpsTriple base (base + 1064) (divCode base) _ _
  intro F hF st hcr hPF hpc
  -- Execute first half: base → base+904
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := hPLLB F hF st hcr hPF hpc
  -- Destructure holdsFor and sep conj
  obtain ⟨h_full, hcompat1, h_qframe, h_f, heq_outer, hdisj_outer, hQFrame, hF_heap⟩ := hQF
  obtain ⟨h_lp, h_frame, heq_inner, hdisj_inner, hLP, hFrame⟩ := hQFrame
  -- Expand loopBodyPostN4
  change loopBodyPostN4 sp (0 : Word) b0' b1' b2' b3' h_lp at hLP
  -- Unfold loopBodyPostN4 WITHOUT unfolding signExtend12 (which would destroy atom identity)
  unfold loopBodyPostN4 at hLP
  -- Simplify let-bindings and address expressions
  -- First: canonicalize compound addresses (u0-u4, q) that use the full u_base/q_addr patterns
  -- These must fire BEFORE j0_u_base_eq which partially simplifies
  simp only [j0_u0_addr_eq, j0_u1_addr_eq, j0_u2_addr_eq, j0_u3_addr_eq, j0_u4_addr_eq,
    j0_q_addr_eq] at hLP
  -- Second: simplify remaining expressions (u_base in registers, j', signExtend12, etc.)
  simp only [j0_u_base_eq, j0_shl3_eq, j0_j'_eq, j0_sub_zero, j0_q_sub_zero,
    signExtend12_0, signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
    word_add_zero] at hLP
  obtain ⟨x2v, x10v, x11v, un0v, un1v, un2v, un3v, u4v, qv,
    retv, dv, dlov, sunv, hLP_atoms⟩ := hLP
  -- Get post-loop chain with concrete values
  -- v2=x2v, v5=0, v6=sp+SE12(4056), v7=sp+SE12(4088), v10=x10v
  -- q0=qv, q1=0, q2=0, q3=0, m0=b0', m8=b1', m16=b2', m24=b3'
  have hDE := evm_div_preamble_denorm_epilogue_spec sp base
    un0v un1v un2v un3v shift
    x2v (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088) x10v
    qv (0 : Word) (0 : Word) (0 : Word) b0' b1' b2' b3'
    hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
  intro_lets at hDE
  -- Weaken postcondition to existential q output
  -- Don't weaken postcondition — use hDE directly with full output
  -- The postcondition weakening happens at the holdsFor level at the end
  -- Apply hDE (unframed) with combined frame = LEFTOVER ** F
  -- LEFTOVER: atoms not used by post-loop but carried through
  -- Recombine heaps
  have hCombined : sepConj _ _ h_qframe :=
    ⟨h_lp, h_frame, heq_inner, hdisj_inner, hLP_atoms, hFrame⟩
  have hAll : sepConj _ _ h_full :=
    ⟨h_qframe, h_f, heq_outer, hdisj_outer, hCombined, hF_heap⟩
  rw [sepConj_assoc'] at hAll
  -- Rearrange atoms to match POST_LOOP_PRE ** (LEFTOVER ** F)
  -- POST_LOOP_PRE = hDE's precondition (20 atoms)
  let POST_LOOP_PRE :=
    (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ sp + signExtend12 4056) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ sp + signExtend12 4088) ** (.x2 ↦ᵣ x2v) ** (.x10 ↦ᵣ x10v) **
    ((sp + signExtend12 3992) ↦ₘ shift) **
    ((sp + signExtend12 4056) ↦ₘ un0v) ** ((sp + signExtend12 4048) ↦ₘ un1v) **
    ((sp + signExtend12 4040) ↦ₘ un2v) ** ((sp + signExtend12 4032) ↦ₘ un3v) **
    ((sp + signExtend12 4088) ↦ₘ qv) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
    ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
    ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3')
  have hRearranged : (POST_LOOP_PRE ** (((.x1 ↦ᵣ signExtend12 (4095 : BitVec 12)) ** (.x11 ↦ᵣ x11v) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4v) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retv) ** (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) ** (sp + signExtend12 3944 ↦ₘ sunv)) ** F)) h_full := by
    xperm_hyp hAll
  have hQ2F : (POST_LOOP_PRE ** (((.x1 ↦ᵣ signExtend12 (4095 : BitVec 12)) ** (.x11 ↦ᵣ x11v) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4v) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retv) ** (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) ** (sp + signExtend12 3944 ↦ₘ sunv)) ** F)).holdsFor s1 :=
    ⟨h_full, hcompat1, hRearranged⟩
  -- Apply the post-loop chain with LEFTOVER ** F as the frame
  have hLOF_pcFree : (((.x1 ↦ᵣ signExtend12 (4095 : BitVec 12)) ** (.x11 ↦ᵣ x11v) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4v) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retv) ** (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) ** (sp + signExtend12 3944 ↦ₘ sunv)) ** F).pcFree := by
    pcFree; exact hF
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ :=
    hDE (((.x1 ↦ᵣ signExtend12 (4095 : BitVec 12)) ** (.x11 ↦ᵣ x11v) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4v) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retv) ** (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) ** (sp + signExtend12 3944 ↦ₘ sunv)) ** F) hLOF_pcFree s1
      (CodeReq.SatisfiedBy_preserved (divCode base) k1 _ _ hstep1 hcr) hQ2F hpc1
  -- Chain the steps
  refine ⟨k1 + k2, s2, stepN_add_eq k1 k2 st s1 s2 hstep1 hstep2, hpc2, ?_⟩
  -- Convert: (POST_LOOP_POST ** LEFTOVER ** F).holdsFor → (declared_post ** F).holdsFor
  obtain ⟨h_res, hcompat2, hRF_heap⟩ := hRF
  refine ⟨h_res, hcompat2, ?_⟩
  -- Provide existential witnesses and permute atoms
  -- hRF_heap : (POST_LOOP_POST ** LEFTOVER ** F) h_res
  -- Need: (∃ qv0 x2out ... scout, (all 35 atoms)) ** F) h_res
  -- The anti_shift/u' values from intro_lets become existential witnesses
  -- hRF_heap : (POST_LOOP_POST ** (LEFTOVER ** F)) h_res
  -- Goal: ((fun h => ∃ witnesses, atoms h) ** F) h_res
  -- Re-associate: POST ** (LO ** F) → (POST ** LO) ** F
  rw [← sepConj_assoc'] at hRF_heap
  -- Now hRF_heap : ((POST_LOOP_POST ** LEFTOVER) ** F) h_res
  -- Split into (POST ** LO) and F
  obtain ⟨h_pl, h_f3, heq_r, hdisj_r, hPL, hF3⟩ := hRF_heap
  -- Provide the sep conj with existential witnesses
  refine ⟨h_pl, h_f3, heq_r, hdisj_r, ?_, hF3⟩
  -- hPL : (POST_LOOP_POST ** LEFTOVER) h_pl
  -- Need: ∃ qv0 x2out ... scout, (35 atoms) h_pl
  -- Expand let-bindings in POST_LOOP_POST
  intro_lets at hPL
  exact ⟨qv, _, signExtend12 (4095 : BitVec 12), x11v,
    _, _, _, _, u4v, retv, dv, dlov, sunv,
    by xperm_hyp hPL⟩

end EvmAsm.Rv64
