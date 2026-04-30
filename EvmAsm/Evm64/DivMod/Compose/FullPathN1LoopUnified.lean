/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified

  Bool-parameterized unified preloop+loop composition for n=1.
  Issue #262: Single theorem covers all 16 path combinations at the
  preloop+loop level (base → base+904).

  Directly composes:
  - Preloop: evm_div_n1_to_loopSetup_spec_within (base → base+448)
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
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  bltu_2 = BitVec.ult
    (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.1
    v0'

/-- j=1 trial condition for n=1 (double-addback), dependent on j=3 and j=2 paths. -/
def isTrialN1_j1 (bltu_3 bltu_2 bltu_1 : Bool) (a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b0).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u2S := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  let r3 := iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)
  bltu_1 = BitVec.ult
    (iterN1 bltu_2 v0' v1' v2' v3' u2S r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1).2.1
    v0'

/-- j=0 trial condition for n=1 (double-addback), dependent on j=3, j=2, and j=1 paths. -/
def isTrialN1_j0 (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b0).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u1S := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2S := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  let r3 := iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)
  let r2 := iterN1 bltu_2 v0' v1' v2' v3' u2S r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
  bltu_0 = BitVec.ult
    (iterN1 bltu_1 v0' v1' v2' v3' u1S r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1).2.1
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
  let u0S := a0 <<< (shift.toNat % 64)
  let u1S := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2S := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  loopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base
    v0' v1' v2' v3' u3S (a3 >>> (antiShift.toNat % 64)) (0 : Word) (0 : Word) (0 : Word)
    u2S u1S u0S
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
    (shift antiShift v0' v1' v2' v3' u0S u1S u2S u3S u4_s : Word)
    (v10_val v11Old jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : bltu_3 = BitVec.ult u4_s v0')
    (hbltu_2 : bltu_2 = BitVec.ult
      (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.1 v0')
    (hbltu_1 : bltu_1 = BitVec.ult
      (iterN1 bltu_2 v0' v1' v2' v3' u2S
        (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.1
        (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.1
        (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.1
        (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.2.1).2.1
      v0')
    (hbltu_0 : bltu_0 = BitVec.ult
      (iterN1 bltu_1 v0' v1' v2' v3' u1S
        (iterN1 bltu_2 v0' v1' v2' v3' u2S
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.2.1).2.1
        (iterN1 bltu_2 v0' v1' v2' v3' u2S
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
        (iterN1 bltu_2 v0' v1' v2' v3' u2S
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.2.1).2.2.2.1
        (iterN1 bltu_2 v0' v1' v2' v3' u2S
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.1
          (iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)).2.2.2.2.1).2.2.2.2.1).2.1
      v0')
    (hcarry2 : Carry2NzAll v0' v1' v2' v3') :
    cpsTripleWithin 808 (base + loopBodyOff) (base + denormOff) (divCode base)
      (loopN1PreWithScratch sp jMem (1 : Word) shift u0S v10_val v11Old antiShift
        v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)
        u2S u1S u0S (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        retMem dMem dloMem scratch_un0)
      (loopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base
        v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)
        u2S u1S u0S retMem dMem dloMem scratch_un0) :=
  divK_loop_n1_unified_divCode bltu_3 bltu_2 bltu_1 bltu_0
    sp jMem (1 : Word) shift u0S v10_val v11Old antiShift
    v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)
    u2S u1S u0S (0 : Word) (0 : Word) (0 : Word) (0 : Word)
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
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 808) base (base + denormOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
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
      (preloopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0) := by
  -- 1. Pre-loop: base → base+448
  have hPre := evm_div_n1_to_loopSetup_spec_within sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz hb3z hb2z hb1z hshift_nz


  -- Frame preloop with .x11, jMem, scratch cells
  have hPreF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
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
    v11Old jMem
    retMem dMem dloMem scratch_un0 halign
    hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2
  -- Frame loop with a[], shiftMem (no spare q/u for n=1)
  have hLoopF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1))
    (by pcFree) hLoop
  -- 3. Compose preloop + loop
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopSetupPost at hp
      simp only [x1_val_n1] at hp
      delta loopN1PreWithScratch loopN1Pre
      simp only []
      simp only [n1_ub3_off0, n1_ub3_off4088, n1_ub3_off4080,
                  n1_ub3_off4072, n1_ub3_off4064,
                  n2_ub2_off0,
                  n3_ub1_off0,
                  n3_ub0_off0,
                  n1_qa3, n2_qa2, n3_qa1, n3_qa0,
                  se12_32, se12_40, se12_48, se12_56]
      xperm_hyp hp) hPreF hLoopF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopN1UnifiedPost; xperm_hyp hq)
    hFull

-- ============================================================================
-- Irreducible full-path intermediates for n=1
-- ============================================================================

@[irreducible]
def fullDivN1Shift (b0 : Word) : Word :=
  (clzResult b0).1

@[irreducible]
def fullDivN1AntiShift (b0 : Word) : Word :=
  signExtend12 (0 : BitVec 12) - fullDivN1Shift b0

@[irreducible]
def fullDivN1NormV (b0 b1 b2 b3 : Word) : Word × Word × Word × Word :=
  let shift := fullDivN1Shift b0
  let antiShift := fullDivN1AntiShift b0
  (b0 <<< (shift.toNat % 64),
   (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)),
   (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)),
   (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64)))

@[irreducible]
def fullDivN1NormU (a0 a1 a2 a3 b0 : Word) :
    Word × Word × Word × Word × Word :=
  let shift := fullDivN1Shift b0
  let antiShift := fullDivN1AntiShift b0
  (a0 <<< (shift.toNat % 64),
   (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)),
   (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)),
   (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)),
   a3 >>> (antiShift.toNat % 64))

@[irreducible]
def fullDivN1R3 (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  iterN1 bltu_3 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)

@[irreducible]
def fullDivN1R2 (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  iterN1 bltu_2 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.1 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1

@[irreducible]
def fullDivN1R1 (bltu_3 bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  iterN1 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

@[irreducible]
def fullDivN1R0 (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  iterN1 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

@[irreducible]
def fullDivN1C3 (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  if bltu_0 then
    (mulsubN4 (div128Quot r1.2.1 u.1 v.1)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  else
    (mulsubN4 (signExtend12 4095 : Word)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2

@[irreducible]
def fullDivN1Scratch (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    Assertion :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let scratch_ret3 := if bltu_3 then (base + div128CallRetOff) else retMem
  let scratch_d3 := if bltu_3 then v.1 else dMem
  let scratch_dlo3 := if bltu_3 then div128DLo v.1 else dloMem
  let scratch_un03 := if bltu_3 then div128Un0 u.2.2.2.1 else scratch_un0
  let scratch_ret2 := if bltu_2 then (base + div128CallRetOff) else scratch_ret3
  let scratch_d2 := if bltu_2 then v.1 else scratch_d3
  let scratch_dlo2 := if bltu_2 then div128DLo v.1 else scratch_dlo3
  let scratch_un02 := if bltu_2 then div128Un0 u.2.2.1 else scratch_un03
  let scratch_ret1 := if bltu_1 then (base + div128CallRetOff) else scratch_ret2
  let scratch_d1 := if bltu_1 then v.1 else scratch_d2
  let scratch_dlo1 := if bltu_1 then div128DLo v.1 else scratch_dlo2
  let scratch_un01 := if bltu_1 then div128Un0 u.2.1 else scratch_un02
  (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + div128CallRetOff) else scratch_ret1)) **
  (sp + signExtend12 3960 ↦ₘ (if bltu_0 then v.1 else scratch_d1)) **
  (sp + signExtend12 3952 ↦ₘ (if bltu_0 then div128DLo v.1 else scratch_dlo1)) **
  (sp + signExtend12 3944 ↦ₘ (if bltu_0 then div128Un0 u.1 else scratch_un01))

@[irreducible]
def fullDivN1DenormPre (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN1Shift b0
  let v := fullDivN1NormV b0 b1 b2 b3
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ sp + signExtend12 4056) ** (.x0 ↦ᵣ (0 : Word)) **
   (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ sp + signExtend12 4088) **
   (.x2 ↦ᵣ r0.2.2.2.2.1) **
   (.x10 ↦ᵣ fullDivN1C3 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) **
   ((sp + signExtend12 3992) ↦ₘ shift) **
   ((sp + signExtend12 4056) ↦ₘ r0.2.1) **
   ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
   ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) **
   ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
   ((sp + signExtend12 4088) ↦ₘ r0.1) **
   ((sp + signExtend12 4080) ↦ₘ r1.1) **
   ((sp + signExtend12 4072) ↦ₘ r2.1) **
   ((sp + signExtend12 4064) ↦ₘ r3.1) **
   ((sp + signExtend12 32) ↦ₘ v.1) **
   ((sp + signExtend12 40) ↦ₘ v.2.1) **
   ((sp + signExtend12 48) ↦ₘ v.2.2.1) **
   ((sp + signExtend12 56) ↦ₘ v.2.2.2))

@[irreducible]
def fullDivN1Frame (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    Assertion :=
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ r3.2.2.2.2.2) **
  (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  fullDivN1Scratch bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratch_un0

@[irreducible]
def fullDivN1DenormPost (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN1Shift b0
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1
    r0.1 r1.1 r2.1 r3.1 **
  ((sp + signExtend12 3992) ↦ₘ shift)

@[irreducible]
def fullDivN1UnifiedPost (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  fullDivN1DenormPost bltu_3 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
  fullDivN1Frame bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratch_un0

theorem fullDivN1Shift_unfold (b0 : Word) :
    fullDivN1Shift b0 = (clzResult b0).1 := by
  delta fullDivN1Shift
  rfl

theorem fullDivN1AntiShift_unfold (b0 : Word) :
    fullDivN1AntiShift b0 = signExtend12 (0 : BitVec 12) - fullDivN1Shift b0 := by
  delta fullDivN1AntiShift
  rfl

theorem fullDivN1NormV_unfold (b0 b1 b2 b3 : Word) :
    fullDivN1NormV b0 b1 b2 b3 =
    let shift := fullDivN1Shift b0
    let antiShift := fullDivN1AntiShift b0
    (b0 <<< (shift.toNat % 64),
     (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)),
     (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)),
     (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))) := by
  delta fullDivN1NormV
  rfl

theorem fullDivN1NormU_unfold (a0 a1 a2 a3 b0 : Word) :
    fullDivN1NormU a0 a1 a2 a3 b0 =
    let shift := fullDivN1Shift b0
    let antiShift := fullDivN1AntiShift b0
    (a0 <<< (shift.toNat % 64),
     (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)),
     (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)),
     (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)),
     a3 >>> (antiShift.toNat % 64)) := by
  delta fullDivN1NormU
  rfl

theorem fullDivN1R3_unfold (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    iterN1 bltu_3 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word) := by
  delta fullDivN1R3
  rfl

theorem fullDivN1R2_unfold (bltu_3 bltu_2 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
    iterN1 bltu_2 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.2.1 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1 := by
  delta fullDivN1R2
  rfl

theorem fullDivN1R1_unfold (bltu_3 bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    iterN1 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 := by
  delta fullDivN1R1
  rfl

theorem fullDivN1R0_unfold (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    iterN1 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
      r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
  delta fullDivN1R0
  rfl

theorem evm_div_n1_denorm_epilogue_bundled_spec
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : fullDivN1Shift b0 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (divCode base)
      (fullDivN1DenormPre bltu_3 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3)
      (fullDivN1DenormPost bltu_3 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := fullDivN1Shift b0
  let v := fullDivN1NormV b0 b1 b2 b3
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let c3 := fullDivN1C3 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  have h := evm_div_preamble_denorm_epilogue_spec sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3 r0.1 r1.1 r2.1 r3.1
    v.1 v.2.1 v.2.2.1 v.2.2.2 hshift_nz
  exact cpsTripleWithin_weaken
    (fun h hp => by
      subst shift; subst v; subst r3; subst r2; subst r1; subst r0; subst c3
      delta fullDivN1DenormPre at hp
      simp only [se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp)
    (fun h hq => by
      subst shift; subst r3; subst r2; subst r1; subst r0
      delta fullDivN1DenormPost
      xperm_hyp hq)
    h

theorem fullDivN1UnifiedPost_weaken (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (h : PartialState)
    (hq :
      (fullDivN1DenormPost bltu_3 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
       fullDivN1Frame bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
         retMem dMem dloMem scratch_un0) h) :
    fullDivN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
      retMem dMem dloMem scratch_un0 h := by
  delta fullDivN1UnifiedPost
  exact hq

theorem preloopN1UnifiedPost_to_fullDivN1DenormPre_frame
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (h : PartialState)
    (hp :
      preloopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0 h) :
    (fullDivN1DenormPre bltu_3 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN1Frame bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratch_un0) h := by
  cases bltu_3 <;> cases bltu_2 <;> cases bltu_1 <;> cases bltu_0
  all_goals
    delta preloopN1UnifiedPost loopN1UnifiedPost loopN1Iter210Post loopN1Iter10Post
      loopIterPostN1 loopIterPostN1Max loopIterPostN1Call at hp
    delta fullDivN1DenormPre fullDivN1Frame fullDivN1Scratch fullDivN1Shift
      fullDivN1AntiShift fullDivN1NormV fullDivN1NormU fullDivN1R3 fullDivN1R2
      fullDivN1R1 fullDivN1R0 fullDivN1C3
    simp (config := { decide := true }) only [iterN1_false, iterN1_true, ite_false, ite_true] at hp ⊢
    rw [loopExitPostN1_j0_eq] at hp
    simp (config := { decide := true }) only
      [n1_ub3_off4064, n1_qa3, n2_ub2_off4064, n2_qa2,
        n3_ub1_off4064, n3_qa1, se12_32, se12_40, se12_48, se12_56,
        sepConj_emp_right'] at hp ⊢
    sep_perm hp

theorem evm_div_n1_full_unified_spec
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))) :
    cpsTripleWithin 946 base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
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
      (fullDivN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0) := by
  have hA := evm_div_n1_preloop_loop_unified_spec bltu_3 bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0
    hbnz hb3z hb2z hb1z hshift_nz halign
    hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2
  have hshift_nz' : fullDivN1Shift b0 ≠ 0 := by
    rw [fullDivN1Shift_unfold]
    exact hshift_nz
  have hB := evm_div_n1_denorm_epilogue_bundled_spec
    bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz'
  have hBF := cpsTripleWithin_frameR
    (fullDivN1Frame bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
      retMem dMem dloMem scratch_un0)
    (by delta fullDivN1Frame fullDivN1Scratch; pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp =>
      preloopN1UnifiedPost_to_fullDivN1DenormPre_frame
        bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0 h hp) hA hBF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq =>
      fullDivN1UnifiedPost_weaken bltu_3 bltu_2 bltu_1 bltu_0
        sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h hq)
    hFull

end EvmAsm.Evm64
