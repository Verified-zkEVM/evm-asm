/-
  EvmAsm.Evm64.DivMod.Compose.DivN3FullShift0

  End-to-end composition for n=3 DIV (b[3]=0, b[2]≠0, shift=0).
  Composes: pre-loop (base→base+448) + loop body j=1 (cpsBranch at base+448) +
            loop body j=0 (base+448→base+904) + post-loop shift=0 (base+904→base+1064).
  For n=3, the loop runs 2 iterations: j=1 (loops back) then j=0 (exits).
  Since shift=0, b[] values are already normalized and u[] = copies of a[].
-/

import EvmAsm.Evm64.DivMod.LoopBodyN3
import EvmAsm.Evm64.DivMod.Compose.FullPathN3
import EvmAsm.Evm64.DivMod.Compose.FullPath

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Address simplification lemmas for j=0 (n=3)
-- ============================================================================

/-- u_base for j=0: sp + signExtend12 4056 - 0<<<3 = sp + signExtend12 4056 -/
private theorem j0_u_base_eq_s0 (sp : Word) :
    sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4056 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide]
  bv_omega

/-- Simplify x + 0 for Word -/
private theorem word_add_zero_s0 (x : Word) : x + (0 : Word) = x := by bv_omega

/-- q_addr for j=0: sp + signExtend12 4088 - 0<<<3 = sp + signExtend12 4088 -/
private theorem j0_q_addr_eq_s0 (sp : Word) :
    sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4088 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide]
  bv_omega

/-- u0 addr for j=0: u_base + signExtend12 0 = sp + signExtend12 4056 -/
private theorem j0_u0_addr_eq_s0 (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 = sp + signExtend12 4056 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide]
  bv_omega

/-- u1 addr for j=0: u_base + signExtend12 4088 = sp + signExtend12 4048 -/
private theorem j0_u1_addr_eq_s0 (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 = sp + signExtend12 4048 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) from by native_decide]
  bv_omega

/-- u2 addr for j=0: u_base + signExtend12 4080 = sp + signExtend12 4040 -/
private theorem j0_u2_addr_eq_s0 (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 = sp + signExtend12 4040 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by native_decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by native_decide]
  bv_omega

/-- u3 addr for j=0: u_base + signExtend12 4072 = sp + signExtend12 4032 -/
private theorem j0_u3_addr_eq_s0 (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 = sp + signExtend12 4032 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- u4 addr for j=0: u_base + signExtend12 4064 = sp + signExtend12 4024 -/
private theorem j0_u4_addr_eq_s0 (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 = sp + signExtend12 4024 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by native_decide,
    show signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) from by native_decide]
  bv_omega

/-- Validity: uhi addr for j=0, n=3: sp + SE12(4056) - ((0+3)<<<3) = sp + SE12(4032) -/
private theorem j0_uhi_addr_eq_n3_s0 (sp : Word) :
    sp + signExtend12 4056 - ((0 : Word) + (3 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4032 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- Validity: ulo addr for j=0, n=3: (sp + SE12(4056) - ((0+3)<<<3)) + 8 = sp + SE12(4040) -/
private theorem j0_ulo_addr_eq_n3_s0 (sp : Word) :
    (sp + signExtend12 4056 - ((0 : Word) + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4040 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by native_decide]
  bv_omega

/-- Validity: vtop addr for n=3: sp + ((3 + SE12(4095))<<<3) + SE12(32) = sp + 48 -/
private theorem j0_vtop_addr_eq_n3_s0 (sp : Word) :
    sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32 = sp + 48 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4095 : BitVec 12) = (18446744073709551615 : Word) from by native_decide,
    show signExtend12 (32 : BitVec 12) = (32 : Word) from by native_decide]
  bv_omega

/-- x5 in loop body post for j=0: 0<<<3 = 0 -/
private theorem j0_shl3_eq_s0 :
    (0 : Word) <<< (3 : BitVec 6).toNat = (0 : Word) := by native_decide

/-- u_base for j=0 after shl3: sp + SE12(4056) - 0 = sp + SE12(4056) -/
private theorem j0_sub_zero_s0 (sp : Word) :
    sp + signExtend12 4056 - (0 : Word) = sp + signExtend12 4056 := by bv_omega

/-- q_addr for j=0 after shl3: sp + SE12(4088) - 0 = sp + SE12(4088) -/
private theorem j0_q_sub_zero_s0 (sp : Word) :
    sp + signExtend12 4088 - (0 : Word) = sp + signExtend12 4088 := by bv_omega

/-- j' for j=0: 0 + signExtend12 4095 -/
private theorem j0_j'_eq_s0 :
    (0 : Word) + signExtend12 (4095 : BitVec 12) = signExtend12 (4095 : BitVec 12) := by
  bv_omega

-- ============================================================================
-- Address simplification lemmas for j=1 (n=3)
-- ============================================================================

/-- u_base for j=1: sp + SE12(4056) - 1<<<3 = sp + SE12(4048) -/
private theorem j1_u_base_eq_s0 (sp : Word) :
    sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4048 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) from by native_decide]
  bv_omega

/-- q_addr for j=1: sp + SE12(4088) - 1<<<3 = sp + SE12(4080) -/
private theorem j1_q_addr_eq_s0 (sp : Word) :
    sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4080 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by native_decide]
  bv_omega

/-- u0 addr for j=1: u_base(j=1) + SE12(0) = sp + SE12(4048) -/
private theorem j1_u0_addr_eq_s0 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 = sp + signExtend12 4048 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) from by native_decide]
  bv_omega

/-- u1 addr for j=1: u_base(j=1) + SE12(4088) = sp + SE12(4040) -/
private theorem j1_u1_addr_eq_s0 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 = sp + signExtend12 4040 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) from by native_decide]
  bv_omega

/-- u2 addr for j=1: u_base(j=1) + SE12(4080) = sp + SE12(4032) -/
private theorem j1_u2_addr_eq_s0 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 = sp + signExtend12 4032 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- u3 addr for j=1: u_base(j=1) + SE12(4072) = sp + SE12(4024) -/
private theorem j1_u3_addr_eq_s0 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 = sp + signExtend12 4024 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by native_decide,
    show signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) from by native_decide]
  bv_omega

/-- u4 addr for j=1: u_base(j=1) + SE12(4064) = sp + SE12(4016) -/
private theorem j1_u4_addr_eq_s0 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 = sp + signExtend12 4016 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by native_decide,
    show signExtend12 (4016 : BitVec 12) = (18446744073709551536 : Word) from by native_decide]
  bv_omega

/-- Validity: uhi addr for j=1, n=3: sp + SE12(4056) - ((1+3)<<<3) = sp + SE12(4024) -/
private theorem j1_uhi_addr_eq_s0 (sp : Word) :
    sp + signExtend12 4056 - ((1 : Word) + (3 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4024 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) from by native_decide]
  bv_omega

/-- Validity: ulo addr for j=1, n=3: (sp + SE12(4056) - ((1+3)<<<3)) + 8 = sp + SE12(4032) -/
private theorem j1_ulo_addr_eq_s0 (sp : Word) :
    (sp + signExtend12 4056 - ((1 : Word) + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4032 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) from by native_decide]
  bv_omega

/-- x5 in loop body post for j=1: 1<<<3 = 8 -/
private theorem j1_shl3_eq_s0 :
    (1 : Word) <<< (3 : BitVec 6).toNat = (8 : Word) := by native_decide

/-- j' for j=1: 1 + signExtend12 4095 = 0 -/
private theorem j1_j'_eq_s0 :
    (1 : Word) + signExtend12 (4095 : BitVec 12) = (0 : Word) := by
  simp only [show signExtend12 (4095 : BitVec 12) = (18446744073709551615 : Word) from by native_decide]
  bv_omega

/-- u_base for j=1 after shl3: sp + SE12(4056) - 8 = sp + SE12(4048) -/
private theorem j1_sub_8_s0 (sp : Word) :
    sp + signExtend12 4056 - (8 : Word) = sp + signExtend12 4048 := by
  simp only [show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) from by native_decide]
  bv_omega

/-- q_addr for j=1 after shl3: sp + SE12(4088) - 8 = sp + SE12(4080) -/
private theorem j1_q_sub_8_s0 (sp : Word) :
    sp + signExtend12 4088 - (8 : Word) = sp + signExtend12 4080 := by
  simp only [show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by native_decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by native_decide]
  bv_omega

/-- x1 in pre-loop for n=3: signExtend12 4 - 3 = 1 -/
private theorem se12_4_sub_3_s0 :
    signExtend12 (4 : BitVec 12) - (3 : Word) = (1 : Word) := by native_decide

-- ============================================================================
-- Helper: compose cpsBranch (loop-back iteration) with cpsTriple (final iteration)
-- ============================================================================

/-- Compose a cpsBranch that may loop back to `entry` or exit to `exit_`
    with a cpsTriple that handles the loop-back case.
    The cpsBranch's taken path goes to `entry` (loop back) with postcondition Q_loop.
    The cpsBranch's not-taken path goes to `exit_` with postcondition Q_exit.
    h_next handles the loop-back: cpsTriple from Q_loop to Q.
    h_exit converts the exit postcondition Q_exit → Q. -/
private theorem cpsBranch_loop_back_then_cpsTriple_s0
    (entry exit_ : Word) (cr : CodeReq)
    (P Q_loop Q_exit Q : Assertion)
    (hbr : cpsBranch entry cr P entry Q_loop exit_ Q_exit)
    (h_next : cpsTriple entry exit_ cr Q_loop Q)
    (h_exit : ∀ h, Q_exit h → Q h) :
    cpsTriple entry exit_ cr P Q := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, s1, hstep1, hbranch⟩ := hbr F hF s hcr hPF hpc
  rcases hbranch with ⟨hpc_loop, hQloopF⟩ | ⟨hpc_exit, hQexitF⟩
  · -- Taken: looped back to entry. Apply h_next.
    have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
    obtain ⟨k2, s2, hstep2, hpc2, hQF⟩ := h_next F hF s1 hcr' hQloopF hpc_loop
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hQF⟩
  · -- Not taken: exited to exit_. Weaken Q_exit → Q.
    refine ⟨k1, s1, hstep1, hpc_exit, ?_⟩
    obtain ⟨h_full, hcompat, h_q, h_f, heq, hdisj, hQex, hFv⟩ := hQexitF
    exact ⟨h_full, hcompat, h_q, h_f, heq, hdisj, h_exit _ hQex, hFv⟩

-- ============================================================================
-- Helper: sequential composition with existential intermediate
-- ============================================================================

/-- Sequential composition where the intermediate has existentials. -/
private theorem cpsTriple_seq_ex_same_cr_s0 {V : Type} (s m e : Word) (cr : CodeReq)
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
-- Composition: pre-loop + two loop iterations (base → base+904) for n=3, shift=0
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Pre-loop + two-iteration loop body for n=3 DIV (shift=0).
    Composes base→base+448 (copy path, no normalization) with two iterations of loop body
    at base+448: j=1 (cpsBranch, loops back) then j=0 (cpsTriple, exits to base+904).
    Since shift=0, b[] values are unchanged and u[] = copies of a[].
    Postcondition uses loopBodyPostN3 with existentials for computed values. -/
theorem evm_div_n3_shift0_preloop_loopbody_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 : Word)
    (n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_z : (clzResult b2).1 = 0)
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
    cpsTriple base (base + 904) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) ** (.x11 ↦ᵣ v11) **
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
      (fun h => ∃ (x1out x5out x6out x7out x2out x10out x11out : Word)
        (u0out u1out u2out u3out u4out q0out : Word)
        (u5out q1out : Word)
        (j_mem_out : Word)
        (retout dout dlout scout : Word),
       ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ x1out) **
        (.x5 ↦ᵣ x5out) ** (.x6 ↦ᵣ x6out) **
        (.x7 ↦ᵣ x7out) ** (.x10 ↦ᵣ x10out) ** (.x11 ↦ᵣ x11out) **
        (.x2 ↦ᵣ x2out) ** (.x0 ↦ᵣ (0 : Word)) **
        (sp + signExtend12 3976 ↦ₘ j_mem_out) **
        (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
        ((sp + 32) ↦ₘ b0) ** ((sp + signExtend12 4056) ↦ₘ u0out) **
        ((sp + 40) ↦ₘ b1) ** ((sp + signExtend12 4048) ↦ₘ u1out) **
        ((sp + 48) ↦ₘ b2) ** ((sp + signExtend12 4040) ↦ₘ u2out) **
        ((sp + 56) ↦ₘ b3) ** ((sp + signExtend12 4032) ↦ₘ u3out) **
        ((sp + signExtend12 4024) ↦ₘ u4out) **
        ((sp + signExtend12 4088) ↦ₘ q0out) **
        ((sp + signExtend12 4016) ↦ₘ u5out) **
        ((sp + signExtend12 4080) ↦ₘ q1out) **
        (sp + signExtend12 3968 ↦ₘ retout) **
        (sp + signExtend12 3960 ↦ₘ dout) **
        (sp + signExtend12 3952 ↦ₘ dlout) **
        (sp + signExtend12 3944 ↦ₘ scout) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1)) h) := by
  -- Step 1: Pre-loop shift=0 (base → base+448)
  -- Since shift=0: b values unchanged, u values = copies of a
  have hPL := evm_div_n3_shift0_to_loopSetup_spec sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem
    hbnz hb3z hb2nz hshift_z hvalid hv_q0 hv_q1 hv_q2 hv_q3
    hv_u0 hv_u1 hv_u2 hv_u3 hv_u4 hv_u5 hv_u6 hv_u7 hv_n hv_shift
  -- Frame pre-loop with x11, j_old, scratch memory
  have hPLf := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ v11) **
     ((sp + signExtend12 3976) ↦ₘ j_old) **
     ((sp + signExtend12 3968) ↦ₘ ret_mem) ** ((sp + signExtend12 3960) ↦ₘ d_mem) **
     ((sp + signExtend12 3952) ↦ₘ dlo_mem) ** ((sp + signExtend12 3944) ↦ₘ scratch_un0))
    (by pcFree) hPL
  -- Rewrite x1 in pre-loop postcondition to match j=1 loop body's x1=1
  rw [se12_4_sub_3_s0] at hPLf
  -- Step 2: j=1 cpsBranch (base+448 → base+448/904)
  -- For shift=0: b values unchanged (b0..b3), u values = copies of a (a0..a3)
  -- The j=1 window positions:
  -- u[0] at sp+SE12(4048) = a1, u[1] at sp+SE12(4040) = a2,
  -- u[2] at sp+SE12(4032) = a3, u[3] at sp+SE12(4024) = 0,
  -- u_top at sp+SE12(4016) = 0, q_old at sp+SE12(4080) = 0
  have hJ1 := divK_loop_body_n3_combined_spec
    sp (1 : Word) j_old (3 : Word) (clzResult b2).1 ((clzResult b2).2 >>> (63 : Nat)) b3 v11
    (signExtend12 (0 : BitVec 12) - (clzResult b2).1)
    b0 b1 b2 b3 a1 a2 a3 (0 : Word) (0 : Word) (0 : Word)
    ret_mem d_mem dlo_mem scratch_un0
    base
    hv_j hv_n
    (by rw [j1_uhi_addr_eq_s0]; exact hv_u4)
    (by rw [j1_ulo_addr_eq_s0]; exact hv_u3)
    (by rw [j0_vtop_addr_eq_n3_s0]; exact ValidMemRange.fetch hvalid 6 _ (by omega) (by rfl))
    hv_ret hv_d hv_dlo hv_scratch
    halign
    (by rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by native_decide]
        exact ValidMemRange.fetch hvalid 4 _ (by omega) (by rfl))
    (by rw [j1_u0_addr_eq_s0]; exact hv_u1)
    (by rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by native_decide]
        exact ValidMemRange.fetch hvalid 5 _ (by omega) (by rfl))
    (by rw [j1_u1_addr_eq_s0]; exact hv_u2)
    (by rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by native_decide]
        exact ValidMemRange.fetch hvalid 6 _ (by omega) (by rfl))
    (by rw [j1_u2_addr_eq_s0]; exact hv_u3)
    (by rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by native_decide]
        exact ValidMemRange.fetch hvalid 7 _ (by omega) (by rfl))
    (by rw [j1_u3_addr_eq_s0]; exact hv_u4)
    (by rw [j1_u4_addr_eq_s0]; exact hv_u5)
    (by rw [j1_q_addr_eq_s0]; exact hv_q1)
  -- Expand let-bindings and canonicalize j=1 addresses
  dsimp only [] at hJ1
  simp only [j1_u0_addr_eq_s0, j1_q_addr_eq_s0, j1_u1_addr_eq_s0,
    j1_u2_addr_eq_s0, j1_u3_addr_eq_s0, j1_u4_addr_eq_s0,
    signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56] at hJ1
  -- Lift j=1 from sharedDivModCode to divCode
  have hJ1d := cpsBranch_extend_code (sharedDivModCode_sub_divCode base) hJ1
  -- Frame j=1 with cells for j=0 window that j=1 doesn't touch
  have hJ1f := cpsBranch_frame_left _ _ _ _ _ _ _
    (((sp + signExtend12 4056) ↦ₘ a0) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))
    (by pcFree) hJ1d
  -- Step 3: Compose pre-loop + two loop iterations at holdsFor level
  show cpsTriple base (base + 904) (divCode base) _ _
  intro F hF st hcr hPF hpc
  -- Execute pre-loop: base → base+448
  obtain ⟨h_pre, hcompat_pre, hSep_pre⟩ := hPF
  obtain ⟨k1, s1, hstep1, hpc1, hQ1F⟩ := hPLf F hF st hcr
    ⟨h_pre, hcompat_pre, by xperm_hyp hSep_pre⟩ hpc
  have hcr1 := CodeReq.SatisfiedBy_preserved (divCode base) k1 st s1 hstep1 hcr
  -- Rearrange pre-loop postcondition to match j=1 cpsBranch precondition
  obtain ⟨h_f1, hc1, hSep1⟩ := hQ1F
  -- Execute j=1 cpsBranch: base+448 → base+448 (loop back) or base+904 (exit)
  obtain ⟨k2, s2, hstep2, hcase⟩ := hJ1f F hF s1 hcr1
    ⟨h_f1, hc1, by xperm_hyp hSep1⟩ hpc1
  have hcr2 := CodeReq.SatisfiedBy_preserved (divCode base) k2 s1 s2 hstep2 hcr1
  -- Case split: loop-back (base+448) vs exit (base+904)
  rcases hcase with ⟨hpc2, hQ2F⟩ | ⟨hpc2, hQ2F⟩
  · -- Loop-back case: j=1 looped back to base+448, now execute j=0
    obtain ⟨h_full2, hcompat2, h_qf2, h_f2, hdisj2, heq2, hQF2, hF2⟩ := hQ2F
    obtain ⟨h_lp2, h_frame2, hdisj_i2, heq_i2, hLP2, hFrame2⟩ := hQF2
    -- Unfold and canonicalize loopBodyPostN3 at j=1
    change loopBodyPostN3 sp (1 : Word) b0 b1 b2 b3 h_lp2 at hLP2
    unfold loopBodyPostN3 at hLP2
    simp only [j1_u0_addr_eq_s0, j1_u1_addr_eq_s0, j1_u2_addr_eq_s0, j1_u3_addr_eq_s0,
      j1_u4_addr_eq_s0, j1_q_addr_eq_s0] at hLP2
    simp only [j1_shl3_eq_s0, j1_j'_eq_s0, j1_sub_8_s0,
      signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56] at hLP2
    obtain ⟨x2v_j1, x10v_j1, x11v_j1, un0v_j1, un1v_j1, un2v_j1, un3v_j1, u4v_j1, qv_j1,
      retv_j1, dv_j1, dlov_j1, sunv_j1, hLP2_atoms⟩ := hLP2
    -- Build j=0 spec with j=1 output values (window shift)
    have hLB0 := divK_loop_body_n3_j0_spec sp
      (1 : Word) (8 : Word) (sp + signExtend12 4048) (sp + signExtend12 4080)
      x10v_j1 x11v_j1 x2v_j1
      b0 b1 b2 b3 a0 un0v_j1 un1v_j1 un2v_j1 un3v_j1 (0 : Word)
      retv_j1 dv_j1 dlov_j1 sunv_j1
      base
      hv_j hv_n
      (by rw [j0_uhi_addr_eq_n3_s0]; exact hv_u3)
      (by rw [j0_ulo_addr_eq_n3_s0]; exact hv_u2)
      (by rw [j0_vtop_addr_eq_n3_s0]; exact ValidMemRange.fetch hvalid 6 _ (by omega) (by rfl))
      hv_ret hv_d hv_dlo hv_scratch
      halign
      (by rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by native_decide]
          exact ValidMemRange.fetch hvalid 4 _ (by omega) (by rfl))
      (by rw [j0_u0_addr_eq_s0]; exact hv_u0)
      (by rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by native_decide]
          exact ValidMemRange.fetch hvalid 5 _ (by omega) (by rfl))
      (by rw [j0_u1_addr_eq_s0]; exact hv_u1)
      (by rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by native_decide]
          exact ValidMemRange.fetch hvalid 6 _ (by omega) (by rfl))
      (by rw [j0_u2_addr_eq_s0]; exact hv_u2)
      (by rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by native_decide]
          exact ValidMemRange.fetch hvalid 7 _ (by omega) (by rfl))
      (by rw [j0_u3_addr_eq_s0]; exact hv_u3)
      (by rw [j0_u4_addr_eq_s0]; exact hv_u4)
      (by rw [j0_q_addr_eq_s0]; exact hv_q0)
    dsimp only [] at hLB0
    simp only [j0_u0_addr_eq_s0, j0_q_addr_eq_s0, j0_u1_addr_eq_s0,
      j0_u2_addr_eq_s0, j0_u3_addr_eq_s0, j0_u4_addr_eq_s0,
      signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56] at hLB0
    have hLB0d := cpsTriple_extend_code (sharedDivModCode_sub_divCode base) hLB0
    have hLB0f := cpsTriple_frame_left _ _ _ _ _
      (((sp + signExtend12 4016) ↦ₘ u4v_j1) **
       ((sp + signExtend12 4080) ↦ₘ qv_j1) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))
      (by pcFree) hLB0d
    -- Recombine j=1 atoms for rearrangement to j=0 precondition
    have hCombined2 : sepConj _ _ h_qf2 :=
      ⟨h_lp2, h_frame2, hdisj_i2, heq_i2, hLP2_atoms, hFrame2⟩
    have hAll2 : sepConj _ _ h_full2 :=
      ⟨h_qf2, h_f2, hdisj2, heq2, hCombined2, hF2⟩
    rw [sepConj_assoc'] at hAll2
    -- Apply j=0 spec (xperm_hyp rearranges atoms to match its precondition)
    obtain ⟨k3, s3, hstep3, hpc3, hQ3F⟩ := hLB0f F hF s2 hcr2
      ⟨h_full2, hcompat2, by xperm_hyp hAll2⟩ hpc2
    -- Chain three execution steps
    refine ⟨k1 + k2 + k3, s3,
      stepN_add_eq _ _ _ _ _ (stepN_add_eq _ _ _ _ _ hstep1 hstep2) hstep3, hpc3, ?_⟩
    -- Destructure j=0 postcondition and provide final existential witnesses
    obtain ⟨h_res3, hcompat3, h_qf3, h_f3, hdisj3, heq3, hQF3, hF3⟩ := hQ3F
    refine ⟨h_res3, hcompat3, h_qf3, h_f3, hdisj3, heq3, ?_, hF3⟩
    obtain ⟨h_j0, h_fr0, hdisj_j0, heq_j0, hJ0post, hFR0⟩ := hQF3
    change loopBodyPostN3 sp (0 : Word) b0 b1 b2 b3 h_j0 at hJ0post
    unfold loopBodyPostN3 at hJ0post
    simp only [j0_u0_addr_eq_s0, j0_u1_addr_eq_s0, j0_u2_addr_eq_s0, j0_u3_addr_eq_s0,
      j0_u4_addr_eq_s0, j0_q_addr_eq_s0] at hJ0post
    simp only [j0_shl3_eq_s0, j0_j'_eq_s0, j0_sub_zero_s0,
      signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56] at hJ0post
    obtain ⟨x2v_j0, x10v_j0, x11v_j0, un0v_j0, un1v_j0, un2v_j0, un3v_j0, u4v_j0, qv_j0,
      retv_j0, dv_j0, dlov_j0, sunv_j0, hJ0_atoms⟩ := hJ0post
    have hCombined3 : sepConj _ _ h_qf3 :=
      ⟨h_j0, h_fr0, hdisj_j0, heq_j0, hJ0_atoms, hFR0⟩
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, u4v_j1, qv_j1, _, _, _, _, _,
      by xperm_hyp hCombined3⟩
  · -- Exit case: j=1 exited to base+904 directly (theoretically unreachable at j=1)
    obtain ⟨h_full2, hcompat2, h_qf2, h_f2, hdisj2, heq2, hQF2, hF2⟩ := hQ2F
    refine ⟨k1 + k2, s2, stepN_add_eq _ _ _ _ _ hstep1 hstep2, hpc2, ?_⟩
    refine ⟨h_full2, hcompat2, h_qf2, h_f2, hdisj2, heq2, ?_, hF2⟩
    obtain ⟨h_lp2, h_frame2, hdisj_i2, heq_i2, hLP2, hFrame2⟩ := hQF2
    change loopBodyPostN3 sp (1 : Word) b0 b1 b2 b3 h_lp2 at hLP2
    unfold loopBodyPostN3 at hLP2
    simp only [j1_u0_addr_eq_s0, j1_u1_addr_eq_s0, j1_u2_addr_eq_s0, j1_u3_addr_eq_s0,
      j1_u4_addr_eq_s0, j1_q_addr_eq_s0] at hLP2
    simp only [j1_shl3_eq_s0, j1_j'_eq_s0, j1_sub_8_s0,
      signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56] at hLP2
    obtain ⟨x2v_j1, x10v_j1, x11v_j1, un0v_j1, un1v_j1, un2v_j1, un3v_j1, u4v_j1, qv_j1,
      retv_j1, dv_j1, dlov_j1, sunv_j1, hLP2_atoms⟩ := hLP2
    have hCombined2 : sepConj _ _ h_qf2 :=
      ⟨h_lp2, h_frame2, hdisj_i2, heq_i2, hLP2_atoms, hFrame2⟩
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, u4v_j1, qv_j1, _, _, _, _, _,
      by xperm_hyp hCombined2⟩

-- ============================================================================
-- Full n=3 DIV spec (shift=0): base → base+1064
-- Composes preloop+loopbody (base→base+904) with shift=0 epilogue (base+904→base+1064)
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Full n=3 DIV spec (b[3]=0, b[2]≠0, shift=0): base → base+1064.
    Composes pre-loop + two-iteration loop body (base→base+904) with
    shift=0 epilogue (base+904→base+1064).
    Since shift=0, b[] values are already normalized and no denormalization step is needed. -/
theorem evm_div_n3_shift0_full_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 : Word)
    (n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_z : (clzResult b2).1 = 0)
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
    cpsTriple base (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) ** (.x11 ↦ᵣ v11) **
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
      (fun h => ∃ (q0v q1v x2out x1out x11out : Word)
        (u0out u1out u2out u3out u4out u5out : Word)
        (j_mem_out : Word)
        (retout dout dlout scout : Word),
        ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0v) ** (.x6 ↦ᵣ q1v) ** (.x7 ↦ᵣ (0 : Word)) **
         (.x2 ↦ᵣ x2out) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
         (.x1 ↦ᵣ x1out) ** (.x11 ↦ᵣ x11out) **
         ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
         ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
         ((sp + 32) ↦ₘ q0v) ** ((sp + 40) ↦ₘ q1v) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1) **
         ((sp + signExtend12 4056) ↦ₘ u0out) ** ((sp + signExtend12 4048) ↦ₘ u1out) **
         ((sp + signExtend12 4040) ↦ₘ u2out) ** ((sp + signExtend12 4032) ↦ₘ u3out) **
         ((sp + signExtend12 4088) ↦ₘ q0v) ** ((sp + signExtend12 4080) ↦ₘ q1v) **
         ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 4024) ↦ₘ u4out) **
         ((sp + signExtend12 4016) ↦ₘ u5out) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 3984) ↦ₘ (3 : Word)) ** ((sp + signExtend12 3976) ↦ₘ j_mem_out) **
         ((sp + signExtend12 3968) ↦ₘ retout) ** ((sp + signExtend12 3960) ↦ₘ dout) **
         ((sp + signExtend12 3952) ↦ₘ dlout) ** ((sp + signExtend12 3944) ↦ₘ scout)) h) := by
  -- Step 1: Pre-loop + loop body (base → base+904)
  have hPLLB := evm_div_n3_shift0_preloop_loopbody_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7
    n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0
    hbnz hb3z hb2nz hshift_z hvalid halign
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch
  -- Step 2: Compose via cpsTriple definition to handle existential intermediate
  show cpsTriple base (base + 1064) (divCode base) _ _
  intro F hF st hcr hPF hpc
  -- Execute first half: base → base+904
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := hPLLB F hF st hcr hPF hpc
  -- Destructure holdsFor and sep conj with existential intermediate
  obtain ⟨h_full, hcompat1, h_q, h_f, hdisj_qf, heq_qf,
    ⟨x1v, x5v, x6v, x7v, x2v, x10v, x11v,
     u0v, u1v, u2v, u3v, u4v, q0v,
     u5v, q1v, j_v,
     retv, dv, dlov, sunv, hQ_atoms⟩, hF_heap⟩ := hQF
  -- Get shift=0 epilogue spec (base+904 → base+1064)
  -- Since shift=0, no denormalization, b values pass through unchanged
  -- epilogue takes: _u0 _u1 _u2 _u3 (unused u params), shift=0, v2=x2v,
  -- v5=x5v, v6=x6v, v7=x7v, v10=x10v,
  -- q0=q0v (q[0]), q1=q1v (q[1]), q2=0, q3=0
  -- m0=b0, m8=b1, m16=b2, m24=b3 (the b memory values, normalized = same as input)
  have hDE := evm_div_shift0_epilogue_spec sp base
    u0v u1v u2v u3v ((clzResult b2).1)
    x2v x5v x6v x7v x10v
    q0v q1v (0 : Word) (0 : Word) b0 b1 b2 b3
    hshift_z hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3
  -- Recombine heaps: Q_atoms ** F
  have hAll : sepConj _ _ h_full :=
    ⟨h_q, h_f, hdisj_qf, heq_qf, hQ_atoms, hF_heap⟩
  -- Rearrange atoms to match POST_LOOP_PRE ** (LEFTOVER ** F)
  -- POST_LOOP_PRE = shift=0 epilogue precondition (16 atoms)
  let POST_LOOP_PRE :=
    (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ x6v) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x5 ↦ᵣ x5v) ** (.x7 ↦ᵣ x7v) ** (.x2 ↦ᵣ x2v) ** (.x10 ↦ᵣ x10v) **
    ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1) **
    ((sp + signExtend12 4088) ↦ₘ q0v) ** ((sp + signExtend12 4080) ↦ₘ q1v) **
    ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
    ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
    ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)
  -- LEFTOVER: u[] + a[] + other scratch (20 atoms)
  have hRearranged : (POST_LOOP_PRE ** (((.x1 ↦ᵣ x1v) ** (.x11 ↦ᵣ x11v) **
     (sp + signExtend12 3976 ↦ₘ j_v) **
     (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ u4v) **
     ((sp + signExtend12 4016) ↦ₘ u5v) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0v) ** ((sp + signExtend12 4048) ↦ₘ u1v) **
     ((sp + signExtend12 4040) ↦ₘ u2v) ** ((sp + signExtend12 4032) ↦ₘ u3v) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retv) ** (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) ** (sp + signExtend12 3944 ↦ₘ sunv)) ** F)) h_full := by
    xperm_hyp hAll
  have hQ2F : (POST_LOOP_PRE ** (((.x1 ↦ᵣ x1v) ** (.x11 ↦ᵣ x11v) **
     (sp + signExtend12 3976 ↦ₘ j_v) **
     (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ u4v) **
     ((sp + signExtend12 4016) ↦ₘ u5v) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0v) ** ((sp + signExtend12 4048) ↦ₘ u1v) **
     ((sp + signExtend12 4040) ↦ₘ u2v) ** ((sp + signExtend12 4032) ↦ₘ u3v) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retv) ** (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) ** (sp + signExtend12 3944 ↦ₘ sunv)) ** F)).holdsFor s1 :=
    ⟨h_full, hcompat1, hRearranged⟩
  -- Prove pcFree for LEFTOVER ** F
  have hLOF_pcFree : (((.x1 ↦ᵣ x1v) ** (.x11 ↦ᵣ x11v) **
     (sp + signExtend12 3976 ↦ₘ j_v) **
     (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ u4v) **
     ((sp + signExtend12 4016) ↦ₘ u5v) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0v) ** ((sp + signExtend12 4048) ↦ₘ u1v) **
     ((sp + signExtend12 4040) ↦ₘ u2v) ** ((sp + signExtend12 4032) ↦ₘ u3v) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retv) ** (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) ** (sp + signExtend12 3944 ↦ₘ sunv)) ** F).pcFree := by
    pcFree; exact hF
  -- Apply epilogue with LEFTOVER ** F as the frame
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ :=
    hDE (((.x1 ↦ᵣ x1v) ** (.x11 ↦ᵣ x11v) **
     (sp + signExtend12 3976 ↦ₘ j_v) **
     (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ u4v) **
     ((sp + signExtend12 4016) ↦ₘ u5v) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0v) ** ((sp + signExtend12 4048) ↦ₘ u1v) **
     ((sp + signExtend12 4040) ↦ₘ u2v) ** ((sp + signExtend12 4032) ↦ₘ u3v) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retv) ** (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) ** (sp + signExtend12 3944 ↦ₘ sunv)) ** F) hLOF_pcFree s1
      (CodeReq.SatisfiedBy_preserved (divCode base) k1 _ _ hstep1 hcr) hQ2F hpc1
  -- Chain the steps
  refine ⟨k1 + k2, s2, stepN_add_eq k1 k2 st s1 s2 hstep1 hstep2, hpc2, ?_⟩
  -- Convert: (POST_LOOP_POST ** LEFTOVER ** F).holdsFor → (declared_post ** F).holdsFor
  obtain ⟨h_res, hcompat2, hRF_heap⟩ := hRF
  refine ⟨h_res, hcompat2, ?_⟩
  -- Re-associate: POST ** (LO ** F) → (POST ** LO) ** F
  rw [← sepConj_assoc'] at hRF_heap
  obtain ⟨h_pl, h_f3, heq_r, hdisj_r, hPL, hF3⟩ := hRF_heap
  refine ⟨h_pl, h_f3, heq_r, hdisj_r, ?_, hF3⟩
  -- Provide existential witnesses
  -- epilogue output: x5=q0v, x6=q1v, x7=0, x10=0
  -- shift=0 so (clzResult b2).1=0, stored at 3992
  -- u values at 4056..4032 are u0v..u3v (passed through by epilogue, but epilogue ignores them)
  -- u5v at 4016, 0 at 4008, 0 at 4000
  exact ⟨q0v, q1v, _, x1v, x11v,
    u0v, u1v, u2v, u3v, u4v, u5v, j_v,
    retv, dv, dlov, sunv,
    by xperm_hyp hPL⟩

end EvmAsm.Rv64
