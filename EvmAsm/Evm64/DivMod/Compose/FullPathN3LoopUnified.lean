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
open EvmAsm.Evm64.DivMod.AddrNorm (bv6_toNat_3 word_shl3_0)

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
    cpsTripleWithin 404 (base + loopBodyOff) (base + denormOff) (divCode base)
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
    cpsTripleWithin 507 base (base + denormOff) (divCode base)
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
  have hPre := evm_div_n3_to_loopSetup_spec_within sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz hb3z hb2nz hshift_nz
  -- Frame preloop with .x11, jMem, scratch cells
  have hPreF := cpsTripleWithin_frameR
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
  have hLoopF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))
    (by pcFree) hLoop
  -- 3. Compose preloop + loop
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopSetupPost at hp
      simp only [x1_val_n3] at hp
      delta loopN3PreWithScratch loopN3Pre
      simp only []
      simp only [n3_ub1_off0, n3_ub1_off4088, n3_ub1_off4080,
                  n3_ub1_off4072, n3_ub1_off4064, n3_ub0_off0,
                  n3_qa1, n3_qa0, se12_32, se12_40, se12_48, se12_56]
      xperm_hyp hp) hPreF hLoopF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopN3UnifiedPost; xperm_hyp hq)
    hFull

-- ============================================================================
-- loopExitPostN3 at j=0: concrete address specialization
-- ============================================================================

/-- Specialize `loopExitPostN3` at `j=0`: all uBase/qAddr offsets become
    flat `sp + signExtend12 K` addresses. -/
theorem loopExitPostN3_j0_eq (sp q_f c3 un0F un1F un2F un3F u4F
    v0 v1 v2 v3 : Word) :
    loopExitPostN3 sp (0 : Word) q_f c3 un0F un1F un2F un3F u4F v0 v1 v2 v3 =
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ signExtend12 4095) **
     (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ sp + signExtend12 4056) **
     (.x7 ↦ᵣ sp + signExtend12 4088) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
     (.x2 ↦ᵣ un3F) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ un0F) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ un1F) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ un2F) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ un3F) **
     ((sp + signExtend12 4024) ↦ₘ u4F) **
     ((sp + signExtend12 4088) ↦ₘ q_f)) := by
  simp only [loopExitPost_unfold]
  rw [u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
      u_base_off4072_j0, u_base_off4064_j0, u_base_j0, q_addr_j0]
  simp only [bv6_toNat_3, word_shl3_0]
  rw [show (0 : Word) + signExtend12 4095 = signExtend12 4095 from BitVec.zero_add _]

-- ============================================================================
-- Irreducible full-path intermediates for n=3
-- ============================================================================

@[irreducible]
def fullDivN3Shift (b2 : Word) : Word :=
  (clzResult b2).1

@[irreducible]
def fullDivN3AntiShift (b2 : Word) : Word :=
  signExtend12 (0 : BitVec 12) - fullDivN3Shift b2

@[irreducible]
def fullDivN3NormV (b0 b1 b2 b3 : Word) : Word × Word × Word × Word :=
  let shift := fullDivN3Shift b2
  let antiShift := fullDivN3AntiShift b2
  (b0 <<< (shift.toNat % 64),
   (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)),
   (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)),
   (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64)))

@[irreducible]
def fullDivN3NormU (a0 a1 a2 a3 b2 : Word) :
    Word × Word × Word × Word × Word :=
  let shift := fullDivN3Shift b2
  let antiShift := fullDivN3AntiShift b2
  (a0 <<< (shift.toNat % 64),
   (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)),
   (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)),
   (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)),
   a3 >>> (antiShift.toNat % 64))

@[irreducible]
def fullDivN3R1 (bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  iterN3 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word)

@[irreducible]
def fullDivN3R0 (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  iterN3 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

@[irreducible]
def fullDivN3C3 (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  if bltu_0 then
    (mulsubN4 (div128Quot r1.2.2.2.1 r1.2.2.1 v.2.2.1)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  else
    (mulsubN4 (signExtend12 4095 : Word)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2

@[irreducible]
def fullDivN3Scratch (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    Assertion :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let scratch_ret1 := if bltu_1 then (base + 516) else retMem
  let scratch_d1 := if bltu_1 then v.2.2.1 else dMem
  let scratch_dlo1 := if bltu_1 then div128DLo v.2.2.1 else dloMem
  let scratch_un01 := if bltu_1 then div128Un0 u.2.2.2.1 else scratch_un0
  (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + 516) else scratch_ret1)) **
  (sp + signExtend12 3960 ↦ₘ (if bltu_0 then v.2.2.1 else scratch_d1)) **
  (sp + signExtend12 3952 ↦ₘ (if bltu_0 then div128DLo v.2.2.1 else scratch_dlo1)) **
  (sp + signExtend12 3944 ↦ₘ (if bltu_0 then div128Un0 r1.2.2.2.1 else scratch_un01))

@[irreducible]
def fullDivN3DenormPre (bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN3Shift b2
  let v := fullDivN3NormV b0 b1 b2 b3
  let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ sp + signExtend12 4056) ** (.x0 ↦ᵣ (0 : Word)) **
   (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ sp + signExtend12 4088) **
   (.x2 ↦ᵣ r0.2.2.2.2.1) **
   (.x10 ↦ᵣ fullDivN3C3 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) **
   ((sp + signExtend12 3992) ↦ₘ shift) **
   ((sp + signExtend12 4056) ↦ₘ r0.2.1) **
   ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
   ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) **
   ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
   ((sp + signExtend12 4088) ↦ₘ r0.1) **
   ((sp + signExtend12 4080) ↦ₘ r1.1) **
   ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
   ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
   ((sp + signExtend12 32) ↦ₘ v.1) **
   ((sp + signExtend12 40) ↦ₘ v.2.1) **
   ((sp + signExtend12 48) ↦ₘ v.2.2.1) **
   ((sp + signExtend12 56) ↦ₘ v.2.2.2))

@[irreducible]
def fullDivN3Frame (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    Assertion :=
  let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  fullDivN3Scratch bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratch_un0

@[irreducible]
def fullDivN3DenormPost (bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN3Shift b2
  let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1
    r0.1 r1.1 (0 : Word) (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift)

/-- Bundled n=3 full-path postcondition. The long computation chain is hidden
    behind irreducible intermediate definitions so later wrapper proofs can
    unfold only the pieces they need. -/
@[irreducible]
def fullDivN3UnifiedPost (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  let shift := fullDivN3Shift b2
  let v := fullDivN3NormV b0 b1 b2 b3
  let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1
    r0.1 r1.1 (0 : Word) (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  fullDivN3Frame bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratch_un0 **
  ((sp + signExtend12 32) ↦ₘ v.1) **
  ((sp + signExtend12 40) ↦ₘ v.2.1) **
  ((sp + signExtend12 48) ↦ₘ v.2.2.1) **
  ((sp + signExtend12 56) ↦ₘ v.2.2.2)

theorem fullDivN3Shift_unfold (b2 : Word) :
    fullDivN3Shift b2 = (clzResult b2).1 := by
  delta fullDivN3Shift
  rfl

theorem fullDivN3AntiShift_unfold (b2 : Word) :
    fullDivN3AntiShift b2 = signExtend12 (0 : BitVec 12) - fullDivN3Shift b2 := by
  delta fullDivN3AntiShift
  rfl

theorem fullDivN3NormV_unfold (b0 b1 b2 b3 : Word) :
    fullDivN3NormV b0 b1 b2 b3 =
    let shift := fullDivN3Shift b2
    let antiShift := fullDivN3AntiShift b2
    (b0 <<< (shift.toNat % 64),
     (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)),
     (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)),
     (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))) := by
  delta fullDivN3NormV
  rfl

theorem fullDivN3NormU_unfold (a0 a1 a2 a3 b2 : Word) :
    fullDivN3NormU a0 a1 a2 a3 b2 =
    let shift := fullDivN3Shift b2
    let antiShift := fullDivN3AntiShift b2
    (a0 <<< (shift.toNat % 64),
     (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)),
     (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)),
     (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)),
     a3 >>> (antiShift.toNat % 64)) := by
  delta fullDivN3NormU
  rfl

theorem fullDivN3R1_unfold (bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN3NormV b0 b1 b2 b3
    let u := fullDivN3NormU a0 a1 a2 a3 b2
    iterN3 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) := by
  delta fullDivN3R1
  rfl

theorem fullDivN3R0_unfold (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN3NormV b0 b1 b2 b3
    let u := fullDivN3NormU a0 a1 a2 a3 b2
    let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    iterN3 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
      r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
  delta fullDivN3R0
  rfl

theorem fullDivN3DenormPre_unfold (bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN3DenormPre bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 =
    let shift := fullDivN3Shift b2
    let v := fullDivN3NormV b0 b1 b2 b3
    let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    let r0 := fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ sp + signExtend12 4056) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ sp + signExtend12 4088) **
     (.x2 ↦ᵣ r0.2.2.2.2.1) **
     (.x10 ↦ᵣ fullDivN3C3 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) **
     ((sp + signExtend12 3992) ↦ₘ shift) **
     ((sp + signExtend12 4056) ↦ₘ r0.2.1) **
     ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
     ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) **
     ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
     ((sp + signExtend12 4088) ↦ₘ r0.1) **
     ((sp + signExtend12 4080) ↦ₘ r1.1) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v.1) **
     ((sp + signExtend12 40) ↦ₘ v.2.1) **
     ((sp + signExtend12 48) ↦ₘ v.2.2.1) **
     ((sp + signExtend12 56) ↦ₘ v.2.2.2)) := by
  delta fullDivN3DenormPre
  rfl

theorem fullDivN3Frame_unfold (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    fullDivN3Frame bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
      retMem dMem dloMem scratch_un0 =
    let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    let r0 := fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
    ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
    ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
    ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
    (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
    (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
    (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
    fullDivN3Scratch bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
      retMem dMem dloMem scratch_un0 := by
  delta fullDivN3Frame
  rfl

theorem fullDivN3DenormPost_unfold (bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN3DenormPost bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 =
    let shift := fullDivN3Shift b2
    let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    let r0 := fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1
      r0.1 r1.1 (0 : Word) (0 : Word) **
    ((sp + signExtend12 3992) ↦ₘ shift) := by
  delta fullDivN3DenormPost
  rfl

theorem fullDivN3C3_false (bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN3C3 bltu_1 false a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN3NormV b0 b1 b2 b3
    let u := fullDivN3NormU a0 a1 a2 a3 b2
    let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    (mulsubN4 (signExtend12 4095 : Word)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2 := by
  delta fullDivN3C3
  rfl

theorem fullDivN3C3_true (bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN3C3 bltu_1 true a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN3NormV b0 b1 b2 b3
    let u := fullDivN3NormU a0 a1 a2 a3 b2
    let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    (mulsubN4 (div128Quot r1.2.2.2.1 r1.2.2.1 v.2.2.1)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2 := by
  delta fullDivN3C3
  rfl

theorem fullDivN3Scratch_false_false (sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratch_un0 : Word) :
    fullDivN3Scratch false false sp base a0 a1 a2 a3 b0 b1 b2 b3
      retMem dMem dloMem scratch_un0 =
    ((sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0)) := by
  delta fullDivN3Scratch
  rfl

theorem fullDivN3Scratch_false_true (sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratch_un0 : Word) :
    fullDivN3Scratch false true sp base a0 a1 a2 a3 b0 b1 b2 b3
      retMem dMem dloMem scratch_un0 =
    let v := fullDivN3NormV b0 b1 b2 b3
    let r1 := fullDivN3R1 false a0 a1 a2 a3 b0 b1 b2 b3
    ((sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v.2.2.1) **
     (sp + signExtend12 3952 ↦ₘ div128DLo v.2.2.1) **
     (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.2.2.1)) := by
  delta fullDivN3Scratch
  rfl

theorem fullDivN3Scratch_true_false (sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratch_un0 : Word) :
    fullDivN3Scratch true false sp base a0 a1 a2 a3 b0 b1 b2 b3
      retMem dMem dloMem scratch_un0 =
    let v := fullDivN3NormV b0 b1 b2 b3
    let u := fullDivN3NormU a0 a1 a2 a3 b2
    ((sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v.2.2.1) **
     (sp + signExtend12 3952 ↦ₘ div128DLo v.2.2.1) **
     (sp + signExtend12 3944 ↦ₘ div128Un0 u.2.2.2.1)) := by
  delta fullDivN3Scratch
  rfl

theorem fullDivN3Scratch_true_true (sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratch_un0 : Word) :
    fullDivN3Scratch true true sp base a0 a1 a2 a3 b0 b1 b2 b3
      retMem dMem dloMem scratch_un0 =
    let v := fullDivN3NormV b0 b1 b2 b3
    let r1 := fullDivN3R1 true a0 a1 a2 a3 b0 b1 b2 b3
    ((sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v.2.2.1) **
     (sp + signExtend12 3952 ↦ₘ div128DLo v.2.2.1) **
     (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.2.2.1)) := by
  delta fullDivN3Scratch
  rfl

theorem evm_div_n3_denorm_epilogue_bundled_spec (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : fullDivN3Shift b2 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (divCode base)
      (fullDivN3DenormPre bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3)
      (fullDivN3DenormPost bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := fullDivN3Shift b2
  let v := fullDivN3NormV b0 b1 b2 b3
  let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let c3 := fullDivN3C3 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  have h := evm_div_preamble_denorm_epilogue_spec sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3 r0.1 r1.1 (0 : Word) (0 : Word)
    v.1 v.2.1 v.2.2.1 v.2.2.2 hshift_nz
  exact cpsTripleWithin_weaken
    (fun h hp => by
      subst shift; subst v; subst r1; subst r0; subst c3
      delta fullDivN3DenormPre at hp
      simp only [se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp)
    (fun h hq => by
      subst shift; subst r1; subst r0
      delta fullDivN3DenormPost
      xperm_hyp hq)
    h

end EvmAsm.Evm64
