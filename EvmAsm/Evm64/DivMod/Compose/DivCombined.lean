/-
  EvmAsm.Evm64.DivMod.Compose.DivCombined

  Combined DIV full spec for the b≠0 case, unifying all n-cases (n=4,3,2,1)
  and both shift variants (shift=0 and shift≠0) into a single theorem.

  Each per-n spec has a different postcondition shape:
  - n=4: 1 q value (qv0), rest zero
  - n=3: 2 q values (q0v, q1v), rest zero
  - n=2: 3 q values (q0v, q1v, q2v), rest zero
  - n=1: 4 q values (q0v, q1v, q2v, q3v)

  The combined postcondition existentially quantifies all 4 q values and all
  other outputs, abstracting away n-specific details.
-/

import EvmAsm.Evm64.DivMod.Compose.DivN4Full
import EvmAsm.Evm64.DivMod.Compose.DivN4FullShift0
import EvmAsm.Evm64.DivMod.Compose.DivN3Full
import EvmAsm.Evm64.DivMod.Compose.DivN3FullShift0
import EvmAsm.Evm64.DivMod.Compose.DivN2Full
import EvmAsm.Evm64.DivMod.Compose.DivN2FullShift0
import EvmAsm.Evm64.DivMod.Compose.DivN1Full
import EvmAsm.Evm64.DivMod.Compose.DivN1FullShift0

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Helper lemma: signExtend12 (4 : BitVec 12) - (4 : Word) = (0 : Word)
-- ============================================================================

private theorem signExtend12_4_sub_4 :
    signExtend12 (4 : BitVec 12) - (4 : Word) = (0 : Word) := by
  simp only [show signExtend12 (4 : BitVec 12) = (4 : Word) from by native_decide]
  bv_omega

-- ============================================================================
-- Helper: b3 ≠ 0 implies b0 ||| b1 ||| b2 ||| b3 ≠ 0 is redundant (already given)
-- ============================================================================

-- ============================================================================
-- Combined b≠0 DIV full spec: base → base+1064
-- ============================================================================

/-- Combined DIV full spec for b≠0: handles all n-cases (n=4,3,2,1) × shift variants.
    The `v2` parameter encodes the x2 register initial value, which depends on which
    limb determines n (the highest non-zero b limb). -/
theorem evm_div_bnz_full_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 : Word)
    (n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hv2 : v2 = (if b3 ≠ 0 then (clzResult b3).2
                 else if b2 ≠ 0 then (clzResult b2).2
                 else if b1 ≠ 0 then (clzResult b1).2
                 else (clzResult b0).2) >>> (63 : Nat))
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
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
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
      (fun h => ∃ (q0v q1v q2v q3v : Word)
        (x2out x1out x11out : Word)
        (u0out u1out u2out u3out u4out : Word)
        (shift_out n_out j_out : Word)
        (u5out u6out u7out : Word)
        (retout dout dlout scout : Word),
        ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0v) ** (.x6 ↦ᵣ q1v) ** (.x7 ↦ᵣ q2v) **
         (.x2 ↦ᵣ x2out) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ q3v) **
         (.x1 ↦ᵣ x1out) ** (.x11 ↦ᵣ x11out) **
         ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
         ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
         ((sp + 32) ↦ₘ q0v) ** ((sp + 40) ↦ₘ q1v) **
         ((sp + 48) ↦ₘ q2v) ** ((sp + 56) ↦ₘ q3v) **
         ((sp + signExtend12 3992) ↦ₘ shift_out) **
         ((sp + signExtend12 4056) ↦ₘ u0out) ** ((sp + signExtend12 4048) ↦ₘ u1out) **
         ((sp + signExtend12 4040) ↦ₘ u2out) ** ((sp + signExtend12 4032) ↦ₘ u3out) **
         ((sp + signExtend12 4088) ↦ₘ q0v) ** ((sp + signExtend12 4080) ↦ₘ q1v) **
         ((sp + signExtend12 4072) ↦ₘ q2v) ** ((sp + signExtend12 4064) ↦ₘ q3v) **
         ((sp + signExtend12 4024) ↦ₘ u4out) **
         ((sp + signExtend12 4016) ↦ₘ u5out) ** ((sp + signExtend12 4008) ↦ₘ u6out) **
         ((sp + signExtend12 4000) ↦ₘ u7out) **
         ((sp + signExtend12 3984) ↦ₘ n_out) ** ((sp + signExtend12 3976) ↦ₘ j_out) **
         ((sp + signExtend12 3968) ↦ₘ retout) ** ((sp + signExtend12 3960) ↦ₘ dout) **
         ((sp + signExtend12 3952) ↦ₘ dlout) ** ((sp + signExtend12 3944) ↦ₘ scout)) h) := by
  -- Case split on which limb of b is the highest non-zero
  by_cases hb3 : b3 = 0
  · -- b3 = 0
    by_cases hb2 : b2 = 0
    · -- b3 = b2 = 0
      by_cases hb1 : b1 = 0
      · -- n=1 case: b3=b2=b1=0
        have hv2_eq : v2 = (clzResult b0).2 >>> (63 : Nat) := by
          rw [hv2, if_neg (not_not.mpr hb3), if_neg (not_not.mpr hb2), if_neg (not_not.mpr hb1)]
        rw [hv2_eq]
        by_cases hshift : (clzResult b0).1 = 0
        · -- n=1 shift=0
          have h := evm_div_n1_shift0_full_spec sp base
            a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11
            q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7
            n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0
            hbnz hb3 hb2 hb1 hshift hvalid halign
            hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
            hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch
          exact cpsTriple_consequence _ _ _ _ _ _ _
            (fun h hp => hp)
            (fun h hq => by
              obtain ⟨q0v, q1v, q2v, q3v, x2out, x1out, x11out,
                u0out, u1out, u2out, u3out, u4out, u5out, u6out, u7out,
                j_mem_out, retout, dout, dlout, scout, hA⟩ := hq
              exact ⟨q0v, q1v, q2v, q3v, x2out, x1out, x11out,
                u0out, u1out, u2out, u3out, u4out,
                _, (1 : Word), j_mem_out, u5out, u6out, u7out,
                retout, dout, dlout, scout, by xperm_hyp hA⟩)
            h
        · -- n=1 shift≠0
          have h := evm_div_n1_full_spec sp base
            a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11
            q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7
            n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0
            hbnz hb3 hb2 hb1 hshift hvalid halign
            hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
            hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch
          intro_lets at h
          exact cpsTriple_consequence _ _ _ _ _ _ _
            (fun h hp => hp)
            (fun h hq => by
              obtain ⟨q0v, q1v, q2v, q3v, x2out, x1out, x11out,
                u0out, u1out, u2out, u3out, u4out, u5out, u6out, u7out,
                j_mem_out, retout, dout, dlout, scout, hA⟩ := hq
              exact ⟨q0v, q1v, q2v, q3v, x2out, x1out, x11out,
                u0out, u1out, u2out, u3out, u4out,
                _, (1 : Word), j_mem_out, u5out, u6out, u7out,
                retout, dout, dlout, scout, by xperm_hyp hA⟩)
            h
      · -- n=2 case: b3=b2=0, b1≠0
        have hv2_eq : v2 = (clzResult b1).2 >>> (63 : Nat) := by
          rw [hv2, if_neg (not_not.mpr hb3), if_neg (not_not.mpr hb2), if_pos hb1]
        rw [hv2_eq]
        by_cases hshift : (clzResult b1).1 = 0
        · -- n=2 shift=0
          have h := evm_div_n2_shift0_full_spec sp base
            a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11
            q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7
            n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0
            hbnz hb3 hb2 hb1 hshift hvalid halign
            hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
            hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch
          exact cpsTriple_consequence _ _ _ _ _ _ _
            (fun h hp => hp)
            (fun h hq => by
              obtain ⟨q0v, q1v, x2out, x1out, x11out,
                u0out, u1out, u2out, u3out, u4out, u5out, u6out,
                q2v, j_mem_out, retout, dout, dlout, scout, hA⟩ := hq
              exact ⟨q0v, q1v, q2v, (0 : Word), x2out, x1out, x11out,
                u0out, u1out, u2out, u3out, u4out,
                _, (2 : Word), j_mem_out, u5out, u6out, (0 : Word),
                retout, dout, dlout, scout, by xperm_hyp hA⟩)
            h
        · -- n=2 shift≠0
          have h := evm_div_n2_full_spec sp base
            a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11
            q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7
            n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0
            hbnz hb3 hb2 hb1 hshift hvalid halign
            hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
            hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch
          intro_lets at h
          exact cpsTriple_consequence _ _ _ _ _ _ _
            (fun h hp => hp)
            (fun h hq => by
              obtain ⟨q0v, q1v, x2out, x1out, x11out,
                u0out, u1out, u2out, u3out, u4out, u5out, u6out,
                q2v, j_mem_out, retout, dout, dlout, scout, hA⟩ := hq
              exact ⟨q0v, q1v, q2v, (0 : Word), x2out, x1out, x11out,
                u0out, u1out, u2out, u3out, u4out,
                _, (2 : Word), j_mem_out, u5out, u6out, (0 : Word),
                retout, dout, dlout, scout, by xperm_hyp hA⟩)
            h
    · -- n=3 case: b3=0, b2≠0
      have hv2_eq : v2 = (clzResult b2).2 >>> (63 : Nat) := by
        rw [hv2, if_neg (not_not.mpr hb3), if_pos hb2]
      rw [hv2_eq]
      by_cases hshift : (clzResult b2).1 = 0
      · -- n=3 shift=0
        have h := evm_div_n3_shift0_full_spec sp base
          a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7
          n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0
          hbnz hb3 hb2 hshift hvalid halign
          hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
          hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch
        exact cpsTriple_consequence _ _ _ _ _ _ _
          (fun h hp => hp)
          (fun h hq => by
            obtain ⟨q0v, q1v, x2out, x1out, x11out,
              u0out, u1out, u2out, u3out, u4out, u5out,
              j_mem_out, retout, dout, dlout, scout, hA⟩ := hq
            exact ⟨q0v, q1v, (0 : Word), (0 : Word), x2out, x1out, x11out,
              u0out, u1out, u2out, u3out, u4out,
              _, (3 : Word), j_mem_out, u5out, (0 : Word), (0 : Word),
              retout, dout, dlout, scout, by xperm_hyp hA⟩)
          h
      · -- n=3 shift≠0
        have h := evm_div_n3_full_spec sp base
          a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7
          n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0
          hbnz hb3 hb2 hshift hvalid halign
          hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
          hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch
        intro_lets at h
        exact cpsTriple_consequence _ _ _ _ _ _ _
          (fun h hp => hp)
          (fun h hq => by
            obtain ⟨q0v, q1v, x2out, x1out, x11out,
              u0out, u1out, u2out, u3out, u4out, u5out,
              j_mem_out, retout, dout, dlout, scout, hA⟩ := hq
            exact ⟨q0v, q1v, (0 : Word), (0 : Word), x2out, x1out, x11out,
              u0out, u1out, u2out, u3out, u4out,
              _, (3 : Word), j_mem_out, u5out, (0 : Word), (0 : Word),
              retout, dout, dlout, scout, by xperm_hyp hA⟩)
          h
  · -- n=4 case: b3≠0
    have hv2_eq : v2 = (clzResult b3).2 >>> (63 : Nat) := by
      rw [hv2, if_pos hb3]
    rw [hv2_eq, signExtend12_4_sub_4]
    by_cases hshift : (clzResult b3).1 = 0
    · -- n=4 shift=0
      have h := evm_div_n4_shift0_full_spec sp base
        a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7
        n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0
        hbnz hb3 hshift hvalid halign
        hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
        hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch
      exact cpsTriple_consequence _ _ _ _ _ _ _
        (fun h hp => hp)
        (fun h hq => by
          obtain ⟨qv0, x2out, x1out, x11out,
            u0out, u1out, u2out, u3out, u4out,
            retout, dout, dlout, scout, hA⟩ := hq
          exact ⟨qv0, (0 : Word), (0 : Word), (0 : Word), x2out, x1out, x11out,
            u0out, u1out, u2out, u3out, u4out,
            _, (4 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word),
            retout, dout, dlout, scout, by xperm_hyp hA⟩)
        h
    · -- n=4 shift≠0
      have h := evm_div_n4_full_spec sp base
        a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7
        n_mem shift_mem j_old ret_mem d_mem dlo_mem scratch_un0
        hbnz hb3 hshift hvalid halign
        hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
        hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch
      intro_lets at h
      exact cpsTriple_consequence _ _ _ _ _ _ _
        (fun h hp => hp)
        (fun h hq => by
          obtain ⟨qv0, x2out, x1out, x11out,
            u0out, u1out, u2out, u3out, u4out,
            retout, dout, dlout, scout, hA⟩ := hq
          exact ⟨qv0, (0 : Word), (0 : Word), (0 : Word), x2out, x1out, x11out,
            u0out, u1out, u2out, u3out, u4out,
            _, (4 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word),
            retout, dout, dlout, scout, by xperm_hyp hA⟩)
        h

end EvmAsm.Rv64
