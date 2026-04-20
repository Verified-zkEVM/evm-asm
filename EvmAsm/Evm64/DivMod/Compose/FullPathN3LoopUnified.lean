/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified

  Bool-parameterized unified preloop+loop composition for n=3.
  Issue #262: Single theorem covers all 4 path combinations at the
  preloop+loop level (base → base+904).

  Dispatches to the existing 4 per-path theorems in FullPathN3Loop.lean.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3Loop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

-- ============================================================================
-- Double-addback () condition predicates for n=3 preloop+loop composition
-- ============================================================================

/-- j=1 trial condition for n=3 (double-addback): same as `isTrialN3_j1`
    since the first iteration doesn't use `iterN3`. -/
def isTrialN3_j1 (bltu : Bool) (a3 b1 b2 : Word) : Prop :=
  let shift := (clzResult b2).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  bltu = BitVec.ult
    (a3 >>> (antiShift.toNat % 64))
    ((b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)))

/-- j=0 trial condition for n=3 (double-addback), dependent on j=1 path (bltu_1).
    Checks the BLTU condition after the j=1 iteration result using `iterN3`. -/
def isTrialN3_j0 (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b2).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u1S := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2S := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  bltu_0 = BitVec.ult
    (iterN3 bltu_1 v0' v1' v2' v3' u1S u2S u3S u4_s (0 : Word)).2.2.2.1
    v2'

-- ============================================================================
-- Double-addback unified preloop+loop postcondition
-- ============================================================================

/-- Unified postcondition for preloop+loop at n=3 (double-addback).
    Wraps loopN3UnifiedPost (with normalized values computed from a[],b[])
    plus frame atoms: a[0..3], spare q[2..3]=0, spare u[6..7]=0, shift. -/
@[irreducible]
def preloopN3UnifiedPost (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  let shift := (clzResult b2).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u0S := a0 <<< (shift.toNat % 64)
  let u1S := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2S := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  loopN3UnifiedPost bltu_1 bltu_0 sp base
    v0' v1' v2' v3' u1S u2S u3S (a3 >>> (antiShift.toNat % 64)) (0 : Word) u0S
    retMem dMem dloMem scratch_un0 **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1)

-- ============================================================================
-- Double-addback loop instantiation helper (heartbeat isolation)
-- ============================================================================

/-- Helper: instantiate unified n=3 loop (double-addback) with explicit normalized values.
    Separates the loop application from the composition for heartbeat budgeting. -/
private theorem evm_div_n3_loop_unified_inst
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift b0' b1' b2' b3' u0 u1 u2 u3 u4 : Word)
    (v10Old v11Old jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_1 : bltu_1 = BitVec.ult u4 b2')
    (hbltu_0 : bltu_0 = BitVec.ult
      (iterN3 bltu_1 b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2')
    (hcarry2 : Carry2NzAll b0' b1' b2' b3') :
    cpsTriple (base + loopBodyOff) (base + denormOff) (divCode base)
      (loopN3PreWithScratch sp jMem (3 : Word) shift u0 v10Old v11Old antiShift
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word)
        retMem dMem dloMem scratch_un0)
      (loopN3UnifiedPost bltu_1 bltu_0 sp base
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0
        retMem dMem dloMem scratch_un0) :=
  divK_loop_n3_unified_divCode bltu_1 bltu_0
    sp jMem (3 : Word) shift u0 v10Old v11Old antiShift
    b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word)
    retMem dMem dloMem scratch_un0 base halign
    hbltu_1 hbltu_0 hcarry2

-- ============================================================================
-- Double-addback unified preloop+loop composition (base → base+908)
-- ============================================================================

/-- Unified preloop+loop for n=3 (double-addback), parameterized by `(bltu_1 bltu_0 : Bool)`.
    Covers all 4 path combinations (max×max, call×call, max×call, call×max).
    Precondition always includes scratch cells.
    Composes preloop (base→base+448) with unified loop (base+448→base+908). -/
theorem evm_div_n3_preloop_loop_unified_spec (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_1 : isTrialN3_j1 bltu_1 a3 b1 b2)
    (hbltu_0 : isTrialN3_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b2).1).toNat % 64))
      ((b1 <<< (((clzResult b2).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b2 <<< (((clzResult b2).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b3 <<< (((clzResult b2).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))) :
    cpsTriple base (base + denormOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
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
       ((sp + signExtend12 3968) ↦ₘ retMem) **
       ((sp + signExtend12 3960) ↦ₘ dMem) **
       ((sp + signExtend12 3952) ↦ₘ dloMem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (preloopN3UnifiedPost bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0) := by
  -- 1. Pre-loop: base → base+448
  have hPre := evm_div_n3_to_loopSetup_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz hb3z hb2nz hshift_nz
  -- Frame preloop with .x11, jMem, scratch cells
  have hPreF := cpsTriple_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hPre
  -- 2. Loop: base+448 → base+908 (unified da, with explicit normalized values)
  have hLoop := evm_div_n3_loop_unified_inst bltu_1 bltu_0 sp base
    (clzResult b2).1 (signExtend12 (0 : BitVec 12) - (clzResult b2).1)
    (b0 <<< ((clzResult b2).1.toNat % 64))
    ((b1 <<< ((clzResult b2).1.toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
    ((b2 <<< ((clzResult b2).1.toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
    ((b3 <<< ((clzResult b2).1.toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
    (a0 <<< ((clzResult b2).1.toNat % 64))
    ((a1 <<< ((clzResult b2).1.toNat % 64)) ||| (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
    ((a2 <<< ((clzResult b2).1.toNat % 64)) ||| (a1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
    ((a3 <<< ((clzResult b2).1.toNat % 64)) ||| (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
    (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64))
    (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64))
    v11Old jMem
    retMem dMem dloMem scratch_un0
    halign
    hbltu_1 hbltu_0 hcarry2
  -- Frame loop with a[], spare q[2..3], spare u[6..7], shiftMem
  have hLoopF := cpsTriple_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))
    (by pcFree) hLoop
  -- 3. Compose preloop + loop
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      delta loopSetupPost at hp
      simp only [x1_val_n3] at hp
      delta loopN3PreWithScratch loopN3Pre
      simp only []
      simp only [n3_ub1_off0 sp, n3_ub1_off4088 sp, n3_ub1_off4080 sp,
                  n3_ub1_off4072 sp, n3_ub1_off4064 sp, n3_ub0_off0 sp,
                  n3_qa1 sp, n3_qa0 sp, se12_32, se12_40, se12_48, se12_56]
      xperm_hyp hp) hPreF hLoopF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopN3UnifiedPost; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
