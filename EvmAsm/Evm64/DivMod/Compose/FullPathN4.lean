-- file-size-exception: tracked by issue #312 (Compose subtree split). Pre-loop / loop-body / post-loop composition lives together; grandfathered pending split.
/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4

  Full n=4 DIV path composition: pre-loop → loop body (j=0) → post-loop.
  Composes base → base+1068 for the b[3]≠0 case.

  For n=4, the loop runs exactly 1 iteration (j=0 only).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4Loop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

-- ============================================================================
-- Address form helpers: signExtend12 K = K for small offsets
-- ============================================================================

-- se12_32, se12_40, se12_48, se12_56 live in Rv64/AddrNorm.lean (#494).

-- `x1_val_n4` now lives in `Compose/Base.lean` (shared with FullPathN4Shift0).

-- ============================================================================
-- Postcondition and condition functions for n=4 composition
-- ============================================================================

/-- Postcondition for pre-loop + max+skip loop body at n=4.
    Computes normalized b[], u[] from shift = clz(b3), then wraps loopBodyN4SkipPost
    with frame atoms (a[], q[1-3]=0, padding, shiftMem). -/
@[irreducible]
def preloopMaxSkipPostN4 (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  loopBodyN4SkipPost sp (0 : Word) (signExtend12 4095) b0' b1' b2' b3' u0 u1 u2 u3 u4 **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ shift)

/-- Max trial quotient condition at n=4: u4 ≥ normalized b3 (BLTU not taken). -/
def isMaxTrialN4 (a3 b2 b3 : Word) : Prop :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u4 := a3 >>> (antiShift.toNat % 64)
  ¬BitVec.ult u4 b3'

/-- Skip addback condition at n=4 with max trial quotient: borrow = 0. -/
def isSkipBorrowN4Max (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat : Word := signExtend12 4095
  (if BitVec.ult u4 (mulsubN4_c3 qHat b0' b1' b2' b3' u0 u1 u2 u3)
   then (1 : Word) else 0) = (0 : Word)

-- ============================================================================
-- Loop body n=4, max+skip/addback, j=0: normalized sp-relative precondition
-- ============================================================================

/-- Loop body n=4, max+skip, j=0 with sp-relative addresses in precondition. -/
theorem divK_loop_body_n4_max_skip_j0_norm (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult uTop v3) :
    let qHat : Word := signExtend12 4095
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + denormOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld))
      (loopBodyN4SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro qHat hborrow
  have raw := divK_loop_body_n4_max_skip_j0_divCode sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base

    hbltu hborrow
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact raw

-- ============================================================================
-- Pre-loop + loop body (max+skip): base → base+904
-- ============================================================================

/-- n=4 pre-loop + max+skip loop body: base → base+904 (shift ≠ 0). -/
theorem evm_div_n4_preloop_max_skip_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hbltu : isMaxTrialN4 a3 b2 b3)
    (hborrow : isSkipBorrowN4Max a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + denormOff) (divCode base)
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
       ((sp + signExtend12 3976) ↦ₘ jMem))
      (preloopMaxSkipPostN4 sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  unfold isMaxTrialN4 at hbltu
  unfold isSkipBorrowN4Max at hborrow
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  have hPre := evm_div_n4_to_loopSetup_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz hb3nz hshift_nz


  have hPreF := cpsTriple_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem))
    (by pcFree) hPre
  have hLoop := divK_loop_body_n4_max_skip_j0_norm sp base
    jMem (4 : Word) shift u0 (a0 >>> (antiShift.toNat % 64)) v11Old antiShift
    b0' b1' b2' b3' u0 u1 u2 u3 u4 (0 : Word)

    hbltu
  intro_lets at hLoop
  have hLoop' := hLoop hborrow
  have hLoopF := cpsTriple_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hLoop'
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      delta loopSetupPost at hp
      simp only [x1_val_n4] at hp
      xperm_hyp hp) hPreF hLoopF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopMaxSkipPostN4; xperm_hyp hq)
    hFull

-- ============================================================================
-- Full n=4 DIV path (max+skip, shift≠0): base → base+1068
-- ============================================================================

/-- Unfold preloopMaxSkipPostN4 to expanded form with sp-relative addresses. -/
theorem preloopMaxSkipPostN4_unfold (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    preloopMaxSkipPostN4 sp a0 a1 a2 a3 b0 b1 b2 b3 =
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    let qHat : Word := signExtend12 4095
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ signExtend12 4095) **
     (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ sp + signExtend12 4056) **
     (.x7 ↦ᵣ sp + signExtend12 4088) ** (.x10 ↦ᵣ ms.2.2.2.2) ** (.x11 ↦ᵣ qHat) **
     (.x2 ↦ᵣ ms.2.2.2.1) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     ((sp + 32) ↦ₘ b0') ** ((sp + signExtend12 4056) ↦ₘ ms.1) **
     ((sp + 40) ↦ₘ b1') ** ((sp + signExtend12 4048) ↦ₘ ms.2.1) **
     ((sp + 48) ↦ₘ b2') ** ((sp + signExtend12 4040) ↦ₘ ms.2.2.1) **
     ((sp + 56) ↦ₘ b3') ** ((sp + signExtend12 4032) ↦ₘ ms.2.2.2.1) **
     ((sp + signExtend12 4024) ↦ₘ u4 - ms.2.2.2.2) **
     ((sp + signExtend12 4088) ↦ₘ qHat)) **
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
    ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 3992) ↦ₘ shift) := by
  delta preloopMaxSkipPostN4
  simp only [loopBodyN4SkipPost, loopBodySkipPost, loopExitPostN4_j0_eq, se12_32, se12_40, se12_48, se12_56]

-- ============================================================================
-- Full n=4 DIV path (max+skip, shift≠0): base → base+1068
-- ============================================================================

/-- Full path postcondition for n=4 DIV (shift ≠ 0, max+skip).
    Computes normalized b[], u[], runs mulsub, then denormalizes remainder
    and outputs quotient. Includes frame atoms carried through the composition. -/
@[irreducible]
def fullDivN4MaxSkipPost (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat : Word := signExtend12 4095
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  denormDivPost sp shift ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 qHat 0 0 0 **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ (a3 >>> (antiShift.toNat % 64)) - ms.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qHat)

/-- Named unfold for `fullDivN4MaxSkipPost`. Restores access to the
    underlying sepConj structure once the `@[irreducible]` attribute
    above makes `delta` the only way in. Parallel to the `_unfold`
    theorems for the other post bundles (`denormDivPost_unfold` etc.). -/
theorem fullDivN4MaxSkipPost_unfold (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN4MaxSkipPost sp a0 a1 a2 a3 b0 b1 b2 b3 =
    (let shift := (clzResult b3).1
     let antiShift := signExtend12 (0 : BitVec 12) - shift
     let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
     let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
     let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
     let b0' := b0 <<< (shift.toNat % 64)
     let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
     let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
     let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
     let u0 := a0 <<< (shift.toNat % 64)
     let qHat : Word := signExtend12 4095
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     denormDivPost sp shift ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 qHat 0 0 0 **
     ((sp + signExtend12 3992) ↦ₘ shift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ (a3 >>> (antiShift.toNat % 64)) - ms.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qHat)) := by
  delta fullDivN4MaxSkipPost; rfl

/-- `fullDivN4MaxSkipPost` is pc-free: all its atoms (inside the
    `denormDivPost` sub-bundle plus the top-level wrapper atoms) are
    `regIs` / `memIs`. Proof goes through `delta` since the bundle is
    `@[irreducible]`; the inner `denormDivPost` is handled by its
    own `Assertion.PCFree` instance. -/
theorem pcFree_fullDivN4MaxSkipPost {sp a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    (fullDivN4MaxSkipPost sp a0 a1 a2 a3 b0 b1 b2 b3).pcFree := by
  delta fullDivN4MaxSkipPost
  pcFree

instance pcFreeInst_fullDivN4MaxSkipPost
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Assertion.PCFree (fullDivN4MaxSkipPost sp a0 a1 a2 a3 b0 b1 b2 b3) :=
  ⟨pcFree_fullDivN4MaxSkipPost⟩

-- ============================================================================
-- Full n=4 MOD path postcondition (max+skip, shift≠0)
-- ============================================================================

/-- Full path postcondition for n=4 MOD (shift ≠ 0, max+skip). Parallels
    `fullDivN4MaxSkipPost` but wraps `denormModPost` instead of
    `denormDivPost`: the `sp+32..sp+56` output slot holds the
    *denormalized* remainder limbs (MOD result), while the scratch
    cells at `sp+4088..sp+4064` still carry the raw `qHat / 0 / 0 / 0`
    trial-quotient values from the loop-body phase.

    Scaffolding for the forthcoming `evm_mod_n4_full_max_skip_spec`.
    Mirrors `fullDivN4MaxSkipPost` atom-for-atom except for the inner
    `denormDivPost` / `denormModPost` swap and the resulting output-slot
    values. -/
@[irreducible]
def fullModN4MaxSkipPost (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat : Word := signExtend12 4095
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  denormModPost sp shift ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 **
  ((sp + signExtend12 4088) ↦ₘ qHat) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ (a3 >>> (antiShift.toNat % 64)) - ms.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qHat)

/-- Named unfold for `fullModN4MaxSkipPost`. Mirror of
    `fullDivN4MaxSkipPost_unfold`. -/
theorem fullModN4MaxSkipPost_unfold (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullModN4MaxSkipPost sp a0 a1 a2 a3 b0 b1 b2 b3 =
    (let shift := (clzResult b3).1
     let antiShift := signExtend12 (0 : BitVec 12) - shift
     let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
     let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
     let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
     let b0' := b0 <<< (shift.toNat % 64)
     let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
     let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
     let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
     let u0 := a0 <<< (shift.toNat % 64)
     let qHat : Word := signExtend12 4095
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     denormModPost sp shift ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 **
     ((sp + signExtend12 4088) ↦ₘ qHat) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ (a3 >>> (antiShift.toNat % 64)) - ms.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qHat)) := by
  delta fullModN4MaxSkipPost; rfl

/-- `fullModN4MaxSkipPost` is pc-free. Mirror of
    `pcFree_fullDivN4MaxSkipPost`. -/
theorem pcFree_fullModN4MaxSkipPost {sp a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    (fullModN4MaxSkipPost sp a0 a1 a2 a3 b0 b1 b2 b3).pcFree := by
  delta fullModN4MaxSkipPost
  pcFree

instance pcFreeInst_fullModN4MaxSkipPost
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Assertion.PCFree (fullModN4MaxSkipPost sp a0 a1 a2 a3 b0 b1 b2 b3) :=
  ⟨pcFree_fullModN4MaxSkipPost⟩

/-- Full n=4 DIV path: base → base+1068 (shift ≠ 0, max+skip).
    Composes pre-loop + loop body + denorm + epilogue. -/
theorem evm_div_n4_full_max_skip_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hbltu : isMaxTrialN4 a3 b2 b3)
    (hborrow : isSkipBorrowN4Max a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + nopOff) (divCode base)
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
       ((sp + signExtend12 3976) ↦ₘ jMem))
      (fullDivN4MaxSkipPost sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat : Word := signExtend12 4095
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  -- 1. Pre-loop + loop body: base → base+904
  have hA := evm_div_n4_preloop_max_skip_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    hbnz hb3nz hshift_nz


    hbltu hborrow
  -- 2. Post-loop: base+904 → base+1068
  have hB := evm_div_preamble_denorm_epilogue_spec sp base
    ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 shift
    ms.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    ms.2.2.2.2 qHat 0 0 0
    b0' b1' b2' b3'
    hshift_nz
  -- Frame post-loop with remainder atoms
  have hBF := cpsTriple_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ (a3 >>> (antiShift.toNat % 64)) - ms.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qHat))
    (by pcFree) hB
  -- 3. Compose A + B
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      simp only [preloopMaxSkipPostN4_unfold] at hp
      xperm_hyp hp) hA hBF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullDivN4MaxSkipPost; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

-- div128Quot is now defined in LoopDefs.lean (shared across all n-cases)


-- ============================================================================
-- Call path normalized specs: sp-relative precondition using div128Quot
-- ============================================================================

/-- Call path condition: u4 < b3' (BLTU taken, use div128). -/
def isCallTrialN4 (a3 b2 b3 : Word) : Prop :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u4 := a3 >>> (antiShift.toNat % 64)
  BitVec.ult u4 b3'

/-- Skip addback condition at n=4 with call trial quotient. -/
def isSkipBorrowN4Call (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat := div128Quot u4 u3 b3'
  (if BitVec.ult u4 (mulsubN4_c3 qHat b0' b1' b2' b3' u0 u1 u2 u3)
   then (1 : Word) else 0) = (0 : Word)

/-- Addback condition at n=4 with call trial quotient. -/
def isAddbackBorrowN4Call (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat := div128Quot u4 u3 b3'
  (if BitVec.ult u4 (mulsubN4_c3 qHat b0' b1' b2' b3' u0 u1 u2 u3)
   then (1 : Word) else 0) ≠ (0 : Word)

/-- Loop body n=4, call+skip, j=0 with sp-relative addresses. -/
theorem divK_loop_body_n4_call_skip_j0_norm (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult uTop v3) :
    let qHat := div128Quot uTop u3 v3
    let dLo := (v3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + denormOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN4SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v3) **
       (sp + signExtend12 3952 ↦ₘ dLo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  intro qHat dLo div_un0 hborrow
  have raw := divK_loop_body_n4_call_skip_j0_divCode sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base halign hbltu
  have raw' := raw hborrow
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  exact raw'

-- ============================================================================
-- Call+skip full path: preloop + loop + postloop (base → base+1068)
-- ============================================================================

/-- Postcondition for pre-loop + call+skip loop body at n=4. -/
@[irreducible]
def preloopCallSkipPostN4 (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat := div128Quot u4 u3 b3'
  let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  loopBodyN4SkipPost sp (0 : Word) qHat b0' b1' b2' b3' u0 u1 u2 u3 u4 **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ b3') **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ shift)

/-- Unfold preloopCallSkipPostN4 to expanded sp-relative form. -/
theorem preloopCallSkipPostN4_unfold (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    preloopCallSkipPostN4 sp base a0 a1 a2 a3 b0 b1 b2 b3 =
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    let qHat := div128Quot u4 u3 b3'
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ signExtend12 4095) **
     (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ sp + signExtend12 4056) **
     (.x7 ↦ᵣ sp + signExtend12 4088) ** (.x10 ↦ᵣ ms.2.2.2.2) ** (.x11 ↦ᵣ qHat) **
     (.x2 ↦ᵣ ms.2.2.2.1) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     ((sp + 32) ↦ₘ b0') ** ((sp + signExtend12 4056) ↦ₘ ms.1) **
     ((sp + 40) ↦ₘ b1') ** ((sp + signExtend12 4048) ↦ₘ ms.2.1) **
     ((sp + 48) ↦ₘ b2') ** ((sp + signExtend12 4040) ↦ₘ ms.2.2.1) **
     ((sp + 56) ↦ₘ b3') ** ((sp + signExtend12 4032) ↦ₘ ms.2.2.2.1) **
     ((sp + signExtend12 4024) ↦ₘ u4 - ms.2.2.2.2) **
     ((sp + signExtend12 4088) ↦ₘ qHat)) **
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ b3') **
    (sp + signExtend12 3952 ↦ₘ dLo) **
    (sp + signExtend12 3944 ↦ₘ div_un0) **
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
    ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 3992) ↦ₘ shift) := by
  delta preloopCallSkipPostN4
  simp only [loopBodyN4SkipPost, loopBodySkipPost, loopExitPostN4_j0_eq, se12_32, se12_40, se12_48, se12_56]

/-- n=4 pre-loop + call+skip loop body: base → base+904 (shift ≠ 0). -/
theorem evm_div_n4_preloop_call_skip_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4 a3 b2 b3)
    (hborrow : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + denormOff) (divCode base)
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
      (preloopCallSkipPostN4 sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  unfold isCallTrialN4 at hbltu
  unfold isSkipBorrowN4Call at hborrow
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  have hPre := evm_div_n4_to_loopSetup_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz hb3nz hshift_nz


  have hPreF := cpsTriple_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hPre
  have hLoop := divK_loop_body_n4_call_skip_j0_norm sp base
    jMem (4 : Word) shift u0 (a0 >>> (antiShift.toNat % 64)) v11Old antiShift
    b0' b1' b2' b3' u0 u1 u2 u3 u4 (0 : Word)
    retMem dMem dloMem scratch_un0 halign

    hbltu
  intro_lets at hLoop
  have hLoop' := hLoop hborrow
  have hLoopF := cpsTriple_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hLoop'
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      delta loopSetupPost at hp
      simp only [x1_val_n4] at hp
      xperm_hyp hp) hPreF hLoopF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopCallSkipPostN4; xperm_hyp hq)
    hFull

/-- Full path postcondition for n=4 DIV (shift ≠ 0, call+skip).
    Includes denormDivPost plus all frame atoms from the composition. -/
@[irreducible]
def fullDivN4CallSkipPost (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat := div128Quot u4 u3 b3'
  let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  denormDivPost sp shift ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 qHat 0 0 0 **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ u4 - ms.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qHat) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ b3') **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0)

/-- Full n=4 DIV path: base → base+1068 (shift ≠ 0, call+skip). -/
theorem evm_div_n4_full_call_skip_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4 a3 b2 b3)
    (hborrow : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + nopOff) (divCode base)
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
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (fullDivN4CallSkipPost sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat := div128Quot u4 u3 b3'
  let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  -- 1. Pre-loop + loop body: base → base+904
  have hA := evm_div_n4_preloop_call_skip_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign
    hbltu hborrow
  -- 2. Post-loop: base+904 → base+1068
  have hB := evm_div_preamble_denorm_epilogue_spec sp base
    ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 shift
    ms.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    ms.2.2.2.2 qHat 0 0 0
    b0' b1' b2' b3'
    hshift_nz
  have hBF := cpsTriple_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4 - ms.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qHat) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ b3') **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) hB
  -- 3. Compose
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      simp only [preloopCallSkipPostN4_unfold] at hp
      xperm_hyp hp) hA hBF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullDivN4CallSkipPost; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull


end EvmAsm.Evm64
