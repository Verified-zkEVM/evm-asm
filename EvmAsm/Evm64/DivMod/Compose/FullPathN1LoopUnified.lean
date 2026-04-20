/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified

  Bool-parameterized unified preloop+loop composition for n=1.
  Issue #262: Single theorem covers all 16 path combinations at the
  preloop+loop level (base → base+904).

  Directly composes:
  - Preloop: evm_div_n1_to_loopSetup_spec (base → base+448)
  - Loop: divK_loop_n1_unified_divCode (base+448 → base+904)

  Unlike n=3 (which dispatches to 4 existing per-path theorems),
  n=1 composes the preloop and unified loop directly.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1Loop
import EvmAsm.Evm64.DivMod.Compose.FullPathN3Loop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

-- ============================================================================
-- Double-addback () condition predicates for n=1 preloop+loop composition
-- ============================================================================

/-- j=3 trial condition for n=1 (double-addback): `bltu_3 = BitVec.ult u_hi_norm v_top_norm`
    where `shift = clz(b0)`, `u_hi_norm = a3 >>> antiShift`,
    `v_top_norm = b0 <<< shift`. -/
def isTrialN1_j3 (bltu_3 : Bool) (a3 b0 : Word) : Prop :=
  let shift := (clzResult b0).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  bltu_3 = BitVec.ult
    (a3 >>> (antiShift.toNat % 64))
    (b0 <<< (shift.toNat % 64))

/-- j=2 trial condition for n=1 (double-addback), dependent on j=3 path (bltu_3).
    Checks the BLTU condition after the j=3 iteration result. -/
def isTrialN1_j2 (bltu_3 bltu_2 : Bool) (a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b0).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  bltu_2 = BitVec.ult
    (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.1
    v0'

/-- j=1 trial condition for n=1 (double-addback), dependent on j=3 and j=2 paths. -/
def isTrialN1_j1 (bltu_3 bltu_2 bltu_1 : Bool) (a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b0).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  let r3 := iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)
  bltu_1 = BitVec.ult
    (iterN1 bltu_2 v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1).2.1
    v0'

/-- j=0 trial condition for n=1 (double-addback), dependent on j=3, j=2, and j=1 paths. -/
def isTrialN1_j0 (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b0).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  let r3 := iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)
  let r2 := iterN1 bltu_2 v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
  bltu_0 = BitVec.ult
    (iterN1 bltu_1 v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1).2.1
    v0'

-- ============================================================================
-- Double-addback unified preloop+loop postcondition
-- ============================================================================

/-- Unified postcondition for preloop+loop at n=1 (double-addback).
    Wraps loopN1UnifiedPost (with normalized values computed from a[],b[])
    plus frame atoms: a[0..3], spare q3 slot, spare u7 slot, shift. -/
@[irreducible]
def preloopN1UnifiedPost (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  let shift := (clzResult b0).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  loopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base
    v0' v1' v2' v3' u3_s (a3 >>> (antiShift.toNat % 64)) (0 : Word) (0 : Word) (0 : Word)
    u2_s u1_s u0_s
    retMem dMem dloMem scratch_un0 **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1)

-- ============================================================================
-- Double-addback loop instantiation helper (heartbeat isolation)
-- ============================================================================

/-- Helper: instantiate unified n=1 loop (double-addback) with explicit normalized values.
    Separates the loop application from the composition for heartbeat budgeting. -/
private theorem evm_div_n1_loop_unified_inst
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift v0' v1' v2' v3' u0_s u1_s u2_s u3_s u4_s : Word)
    (v10_val v11_old jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_3 : bltu_3 = BitVec.ult u4_s v0')
    (hbltu_2 : bltu_2 = BitVec.ult
      (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.1 v0')
    (hbltu_1 : bltu_1 = BitVec.ult
      (iterN1 bltu_2 v0' v1' v2' v3' u2_s
        (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.1
        (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.1
        (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.1
        (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.2.1).2.1
      v0')
    (hbltu_0 : bltu_0 = BitVec.ult
      (iterN1 bltu_1 v0' v1' v2' v3' u1_s
        (iterN1 bltu_2 v0' v1' v2' v3' u2_s
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.2.1).2.1
        (iterN1 bltu_2 v0' v1' v2' v3' u2_s
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
        (iterN1 bltu_2 v0' v1' v2' v3' u2_s
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.2.1).2.2.2.1
        (iterN1 bltu_2 v0' v1' v2' v3' u2_s
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.2.1).2.2.2.2.1).2.1
      v0')
    (hcarry2 : Carry2NzAll v0' v1' v2' v3') :
    cpsTriple (base + loopBodyOff) (base + denormOff) (divCode base)
      (loopN1PreWithScratch sp jMem (1 : Word) shift u0_s v10_val v11_old antiShift
        v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)
        u2_s u1_s u0_s (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        retMem dMem dloMem scratch_un0)
      (loopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base
        v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)
        u2_s u1_s u0_s retMem dMem dloMem scratch_un0) :=
  divK_loop_n1_unified_divCode bltu_3 bltu_2 bltu_1 bltu_0
    sp jMem (1 : Word) shift u0_s v10_val v11_old antiShift
    v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)
    u2_s u1_s u0_s (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    retMem dMem dloMem scratch_un0 base halign





    hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2

-- ============================================================================
-- Double-addback unified preloop+loop composition (base → base+904)
-- ============================================================================

/-- Unified preloop+loop for n=1 (double-addback), parameterized by `(bltu_3 bltu_2 bltu_1 bltu_0 : Bool)`.
    Covers all 16 path combinations.
    Precondition always includes scratch cells.
    Composes preloop (base→base+448) with unified loop (base+448→base+904). -/
theorem evm_div_n1_preloop_loop_unified_spec
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))) :
    cpsTriple base (base + denormOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11_old) **
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
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       ((sp + signExtend12 3968) ↦ₘ retMem) **
       ((sp + signExtend12 3960) ↦ₘ dMem) **
       ((sp + signExtend12 3952) ↦ₘ dloMem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (preloopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0) := by
  -- 1. Pre-loop: base → base+448
  have hPre := evm_div_n1_to_loopSetup_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 nMem shiftMem
    hbnz hb3z hb2z hb1z hshift_nz


  -- Frame preloop with .x11, jMem, scratch cells
  have hPreF := cpsTriple_frameR
    ((.x11 ↦ᵣ v11_old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hPre
  -- 2. Loop: base+448 → base+904 (unified da, with explicit normalized values)
  have hLoop := evm_div_n1_loop_unified_inst bltu_3 bltu_2 bltu_1 bltu_0 sp base
    (clzResult b0).1 (signExtend12 (0 : BitVec 12) - (clzResult b0).1)
    (b0 <<< (((clzResult b0).1).toNat % 64))
    ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
    ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
    ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
    (a0 <<< (((clzResult b0).1).toNat % 64))
    ((a1 <<< (((clzResult b0).1).toNat % 64)) ||| (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
    ((a2 <<< (((clzResult b0).1).toNat % 64)) ||| (a1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
    ((a3 <<< (((clzResult b0).1).toNat % 64)) ||| (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
    (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))
    (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))
    v11_old jMem
    retMem dMem dloMem scratch_un0 halign
    hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2
  -- Frame loop with a[], shiftMem (no spare q/u for n=1)
  have hLoopF := cpsTriple_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1))
    (by pcFree) hLoop
  -- 3. Compose preloop + loop
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      delta loopSetupPost at hp
      simp only [x1_val_n1] at hp
      delta loopN1PreWithScratch loopN1Pre
      simp only []
      simp only [n1_ub3_off0 sp, n1_ub3_off4088 sp, n1_ub3_off4080 sp,
                  n1_ub3_off4072 sp, n1_ub3_off4064 sp,
                  n2_ub2_off0 sp,
                  n3_ub1_off0 sp,
                  n3_ub0_off0 sp,
                  n1_qa3 sp, n2_qa2 sp, n3_qa1 sp, n3_qa0 sp,
                  se12_32, se12_40, se12_48, se12_56]
      xperm_hyp hp) hPreF hLoopF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopN1UnifiedPost; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
