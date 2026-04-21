/-
  EvmAsm.Evm64.DivMod.Compose.ModFullPathN4Shift0

  Full n=4 MOD path composition for the shift=0 case:
  pre-loop → loop body (j=0) → shift=0 MOD epilogue.
  Composes base → base+1068 for the b[3]≠0, shift=0 case.

  Mirror of `FullPathN4Shift0.lean` for DIV, against `modCode`.

  When shift=0, normalization is identity (b'=b, u=a, uTop=0).
  Since uTop=0 < b3 (b3≠0), the BLTU condition is always taken → call path only.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4Shift0
import EvmAsm.Evm64.DivMod.Compose.ModFullPath

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

-- ============================================================================
-- Pre-loop + loop body (shift=0, call+skip): base → base+denormOff (MOD)
-- ============================================================================

/-- n=4 MOD pre-loop + call+skip loop body: base → base+denormOff (shift = 0).
    Mirror of `evm_div_n4_preloop_shift0_call_skip_spec` with `divCode →
    modCode`, reusing `preloopShift0CallSkipPostN4` (which is code-agnostic
    — the post shape doesn't depend on whether the outer code is DIV or
    MOD). -/
theorem evm_mod_n4_preloop_shift0_call_skip_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hborrow : isSkipBorrowN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + denormOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (preloopShift0CallSkipPostN4 sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  unfold isSkipBorrowN4Shift0 at hborrow
  -- Pre-loop: base → base+loopBodyOff (shift=0, MOD)
  have hPre := evm_mod_n4_shift0_to_loopSetup_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz hb3nz hshift_z
  -- Frame preloop with x11, jMem, retMem, dMem, dloMem, scratch_un0
  have hPreF := cpsTriple_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hPre
  -- Loop body: base+loopBodyOff → base+denormOff, call+skip with v=b, u=a, uTop=0
  have hbltu : BitVec.ult (0 : Word) b3 := ult_zero_of_ne hb3nz
  have hLoop := divK_loop_body_n4_call_skip_j0_norm_modCode sp base
    jMem (4 : Word) ((clzResult b3).1) ((clzResult b3).2 >>> (63 : Nat)) b3
    v11Old (signExtend12 (0 : BitVec 12) - (clzResult b3).1)
    b0 b1 b2 b3 a0 a1 a2 a3 (0 : Word) (0 : Word)
    retMem dMem dloMem scratch_un0 halign
    hbltu
  intro_lets at hLoop
  have hLoop' := hLoop hborrow
  -- Frame loop body with a[], q[1-3]=0, padding, shift=0
  have hLoopF := cpsTriple_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1))
    (by pcFree) hLoop'
  -- Compose preloop → loop body
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      simp only [x1_val_n4] at hp
      xperm_hyp hp) hPreF hLoopF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopShift0CallSkipPostN4; simp only [hshift_z] at hq; xperm_hyp hq)
    hFull

-- ============================================================================
-- Full path postcondition for n=4 MOD (shift=0, call+skip)
-- ============================================================================

/-- Full path postcondition for n=4 MOD (shift=0, call+skip). Mirror of
    `fullDivN4Shift0CallSkipPost` with the output slots at sp+32..sp+56
    holding the un-normalized mulsub remainder limbs (MOD result) instead
    of the quotient. Since shift=0, no denormalization step is needed. -/
@[irreducible]
def fullModN4Shift0CallSkipPost (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let qHat := div128Quot (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ ms.1) **
  (.x6 ↦ᵣ ms.2.1) ** (.x7 ↦ᵣ ms.2.2.1) **
  (.x2 ↦ᵣ ms.2.2.2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ms.2.2.2.1) **
  ((sp + signExtend12 3992) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4088) ↦ₘ qHat) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + 32) ↦ₘ ms.1) ** ((sp + 40) ↦ₘ ms.2.1) **
  ((sp + 48) ↦ₘ ms.2.2.1) ** ((sp + 56) ↦ₘ ms.2.2.2.1) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4056) ↦ₘ ms.1) **
  ((sp + signExtend12 4048) ↦ₘ ms.2.1) **
  ((sp + signExtend12 4040) ↦ₘ ms.2.2.1) **
  ((sp + signExtend12 4032) ↦ₘ ms.2.2.2.1) **
  ((sp + signExtend12 4024) ↦ₘ (0 : Word) - ms.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qHat) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ b3) **
  (sp + signExtend12 3952 ↦ₘ (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) **
  (sp + signExtend12 3944 ↦ₘ (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)

/-- `fullModN4Shift0CallSkipPost` is pc-free. -/
theorem pcFree_fullModN4Shift0CallSkipPost
    {sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    (fullModN4Shift0CallSkipPost sp base a0 a1 a2 a3 b0 b1 b2 b3).pcFree := by
  delta fullModN4Shift0CallSkipPost
  pcFree

instance pcFreeInst_fullModN4Shift0CallSkipPost
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Assertion.PCFree (fullModN4Shift0CallSkipPost sp base a0 a1 a2 a3 b0 b1 b2 b3) :=
  ⟨pcFree_fullModN4Shift0CallSkipPost⟩

-- ============================================================================
-- Full n=4 MOD path (shift=0, call+skip): base → base+nopOff
-- ============================================================================

/-- Full n=4 MOD path: base → base+nopOff (shift=0, call+skip).
    Composes pre-loop + loop body + shift=0 MOD epilogue. Mirror of
    `evm_div_n4_full_shift0_call_skip_spec` with `divCode → modCode`
    and the MOD-specific shift=0 epilogue. -/
theorem evm_mod_n4_full_shift0_call_skip_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hborrow : isSkipBorrowN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) ** (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (fullModN4Shift0CallSkipPost sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  let qHat := div128Quot (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  -- 1. Pre-loop + loop body: base → base+denormOff
  have hA := evm_mod_n4_preloop_shift0_call_skip_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hborrow
  -- 2. Post-loop: base+denormOff → base+nopOff (MOD shift=0 epilogue)
  have hB := evm_mod_shift0_epilogue_spec sp base
    ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (0 : Word)
    ms.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    ms.2.2.2.2
    b0 b1 b2 b3
    rfl
  -- Frame post-loop with remaining atoms
  have hBF := cpsTriple_frameR
    (((sp + signExtend12 4088) ↦ₘ qHat) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ (0 : Word) - ms.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qHat) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ b3) **
     (sp + signExtend12 3952 ↦ₘ (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) **
     (sp + signExtend12 3944 ↦ₘ (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat))
    (by pcFree) hB
  -- 3. Compose A + B
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      simp only [preloopShift0CallSkipPostN4_unfold] at hp
      xperm_hyp hp) hA hBF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullModN4Shift0CallSkipPost; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

-- ============================================================================
-- MOD Pre-loop + loop body (shift=0, call+addback BEQ): base → base+denormOff
-- ============================================================================

/-- n=4 MOD pre-loop + call+addback BEQ loop body: base → base+denormOff
    (shift = 0). Mirror of `evm_div_n4_preloop_shift0_call_addback_beq_spec`
    with `divCode → modCode`, reusing `preloopShift0CallAddbackBeqPostN4`
    (code-agnostic) and the shift=0 addback condition indicators. -/
theorem evm_mod_n4_preloop_shift0_call_addback_beq_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hborrow : isAddbackBorrowN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + denormOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (preloopShift0CallAddbackBeqPostN4 sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  unfold isAddbackBorrowN4Shift0 at hborrow
  unfold isAddbackCarry2NzN4Shift0 at hcarry2_nz
  -- Pre-loop: base → base+loopBodyOff (shift=0, MOD)
  have hPre := evm_mod_n4_shift0_to_loopSetup_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz hb3nz hshift_z
  -- Frame preloop with x11, jMem, retMem, dMem, dloMem, scratch_un0
  have hPreF := cpsTriple_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hPre
  -- Loop body: base+loopBodyOff → base+denormOff, call+addback BEQ (modCode)
  have hbltu : BitVec.ult (0 : Word) b3 := ult_zero_of_ne hb3nz
  have hLoop := divK_loop_body_n4_call_addback_j0_beq_norm_modCode sp base
    jMem (4 : Word) ((clzResult b3).1) ((clzResult b3).2 >>> (63 : Nat)) b3
    v11Old (signExtend12 (0 : BitVec 12) - (clzResult b3).1)
    b0 b1 b2 b3 a0 a1 a2 a3 (0 : Word) (0 : Word)
    retMem dMem dloMem scratch_un0 halign
    hbltu hcarry2_nz
  intro_lets at hLoop
  have hLoop' := hLoop hborrow
  -- Frame loop body with a[], q[1-3]=0, padding, shift=0
  have hLoopF := cpsTriple_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1))
    (by pcFree) hLoop'
  -- Compose preloop → loop body
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      simp only [x1_val_n4] at hp
      xperm_hyp hp) hPreF hLoopF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      delta preloopShift0CallAddbackBeqPostN4
      simp only [hshift_z] at hq
      xperm_hyp hq)
    hFull

-- ============================================================================
-- Full path postcondition for n=4 MOD (shift=0, call+addback BEQ)
-- ============================================================================

/-- Full path postcondition for n=4 MOD (shift=0, call+addback BEQ). Mirror
    of `fullDivN4Shift0CallAddbackBeqPost` with the sp+32..sp+56 slots
    holding post-addback remainder limbs (MOD result) instead of the
    quotient. Shift=0 skips the denorm step. -/
@[irreducible]
def fullModN4Shift0CallAddbackBeqPost
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let qHat := div128Quot (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  let c3 := ms.2.2.2.2
  let u4_new := (0 : Word) - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0 b1 b2 b3
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0 b1 b2 b3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0 b1 b2 b3
  let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
               else qHat + signExtend12 4095
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out  := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ un0Out) **
  (.x6 ↦ᵣ un1Out) ** (.x7 ↦ᵣ un2Out) **
  (.x2 ↦ᵣ un3Out) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ un3Out) **
  ((sp + signExtend12 3992) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4088) ↦ₘ q_out) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + 32) ↦ₘ un0Out) ** ((sp + 40) ↦ₘ un1Out) **
  ((sp + 48) ↦ₘ un2Out) ** ((sp + 56) ↦ₘ un3Out) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4056) ↦ₘ un0Out) **
  ((sp + signExtend12 4048) ↦ₘ un1Out) **
  ((sp + signExtend12 4040) ↦ₘ un2Out) **
  ((sp + signExtend12 4032) ↦ₘ un3Out) **
  ((sp + signExtend12 4024) ↦ₘ u4_out) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ q_out) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ b3) **
  (sp + signExtend12 3952 ↦ₘ (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) **
  (sp + signExtend12 3944 ↦ₘ (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)

/-- `fullModN4Shift0CallAddbackBeqPost` is pc-free. -/
theorem pcFree_fullModN4Shift0CallAddbackBeqPost
    {sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    (fullModN4Shift0CallAddbackBeqPost sp base a0 a1 a2 a3 b0 b1 b2 b3).pcFree := by
  delta fullModN4Shift0CallAddbackBeqPost
  pcFree

instance pcFreeInst_fullModN4Shift0CallAddbackBeqPost
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Assertion.PCFree (fullModN4Shift0CallAddbackBeqPost sp base a0 a1 a2 a3 b0 b1 b2 b3) :=
  ⟨pcFree_fullModN4Shift0CallAddbackBeqPost⟩

-- ============================================================================
-- Full n=4 MOD path (shift=0, call+addback BEQ): base → base+nopOff
-- ============================================================================

/-- Full n=4 MOD path: base → base+nopOff (shift=0, call+addback BEQ).
    Composes preloop + shift=0 MOD epilogue. Mirror of
    `evm_div_n4_full_shift0_call_addback_beq_spec` with `divCode → modCode`
    and `evm_div_shift0_epilogue_spec → evm_mod_shift0_epilogue_spec`. -/
theorem evm_mod_n4_full_shift0_call_addback_beq_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hborrow : isAddbackBorrowN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) ** (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (fullModN4Shift0CallAddbackBeqPost sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  let qHat := div128Quot (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  let c3 := ms.2.2.2.2
  let u4_new := (0 : Word) - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0 b1 b2 b3
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0 b1 b2 b3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0 b1 b2 b3
  let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
               else qHat + signExtend12 4095
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out  := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  have hA := evm_mod_n4_preloop_shift0_call_addback_beq_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hcarry2_nz hborrow
  have hB := evm_mod_shift0_epilogue_spec sp base
    un0Out un1Out un2Out un3Out (0 : Word)
    un3Out (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3
    b0 b1 b2 b3
    rfl
  -- Frame post-loop: q-slots stay in frame (MOD epilogue doesn't touch them),
  -- u-slots belong to epilogue's pre (MOD epilogue writes the remainder there).
  have hBF := cpsTriple_frameR
    (((sp + signExtend12 4088) ↦ₘ q_out) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4_out) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ q_out) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ b3) **
     (sp + signExtend12 3952 ↦ₘ (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) **
     (sp + signExtend12 3944 ↦ₘ (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat))
    (by pcFree) hB
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      simp only [preloopShift0CallAddbackBeqPostN4_unfold] at hp
      xperm_hyp hp) hA hBF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullModN4Shift0CallAddbackBeqPost; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
