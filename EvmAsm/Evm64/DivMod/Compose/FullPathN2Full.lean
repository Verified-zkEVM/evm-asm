/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2Full

  Full n=2 DIV path compositions (base → base+1068).
  Composes preloop+loop (base → base+904) with denorm+epilogue (base+904 → base+1068).

  Starts with the all-max case (bltu_2 = bltu_1 = bltu_0 = false) as the foundation.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPath
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Loop
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Cases

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

-- loopExitPostN2_j0_eq is in FullPathN2Loop.lean

-- ============================================================================
-- Double-addback full path postcondition for n=2 all-max (F,F,F)
-- ============================================================================

/-- Full path postcondition for n=2 DIV with double addback
    (shift ≠ 0, all-max: bltu_2=bltu_1=bltu_0=false).
    Same as `fullDivN2AllMaxPost` but uses `iterN2Max` (with addback branching). -/
@[irreducible]
def fullDivN2AllMaxPost (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  let shift := (clzResult b1).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u0S := a0 <<< (shift.toNat % 64)
  let u1S := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2S := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  let r2 := iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Max v0' v1' v2' v3' u1S r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Max v0' v1' v2' v3' u0S r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.1 r1.1 r2.1 (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

-- ============================================================================
-- Full n=2 DIV path with double addback (all-max, shift≠0): base → base+1068
-- ============================================================================

/-- Full n=2 DIV path with double addback (shift ≠ 0, all-max: bltu_2=bltu_1=bltu_0=false).
    Composes pre-loop + three-iteration loop + denorm + epilogue. -/
theorem evm_div_n2_full_all_max_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : isTrialN2_j2 false a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 false false a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 false false false a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
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
      (fullDivN2AllMaxPost sp a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0) := by
  let shift := (clzResult b1).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u0S := a0 <<< (shift.toNat % 64)
  let u1S := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2S := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  let r2 := iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)
  let r1 := iterN2Max v0' v1' v2' v3' u1S r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2Max v0' v1' v2' v3' u0S r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  let c3_0 := (mulsubN4 (signExtend12 4095 : Word) v0' v1' v2' v3'
    u0S r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  -- 1. Pre-loop + loop body: base → base+904
  have hA := evm_div_n2_preloop_loop_unified_spec false false false sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz halign
    hbltu_2 hbltu_1 hbltu_0 hcarry2
  -- 2. Post-loop: base+904 → base+1068
  have hB := evm_div_preamble_denorm_epilogue_spec sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3_0 r0.1 r1.1 r2.1 (0 : Word)
    v0' v1' v2' v3'
    hshift_nz
  -- Frame post-loop with remainder atoms
  have hBF := cpsTriple_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hB
  -- 3. Compose A + B
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      delta preloopN2UnifiedPost loopN2UnifiedPost at hp
      simp (config := { decide := true }) only [iterN2_false, ite_false] at hp
      delta loopN2Iter10Post loopN2MaxPost loopIterPostN2Max at hp
      simp (config := { decide := true }) only [loopExitPostN2_j0_eq,
        n2_ub2_off4064, n3_ub1_off4064, n2_qa2, n3_qa1,
        se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp) hA hBF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullDivN2AllMaxPost; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

-- ============================================================================
-- Double-addback unified full path postcondition for n=2 (all 8 path combinations)
-- ============================================================================

/-- Unified full path postcondition for n=2 DIV with double addback (shift ≠ 0).
    Uses `iterN2` (which reduces to `iterN2Max`/`iterN2Call` for concrete bools).
    Scratch cells depend on the path: passthrough for all-max,
    div128 scratch for the last call-path iteration. -/
@[irreducible]
def fullDivN2UnifiedPost (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  let shift := (clzResult b1).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u0S := a0 <<< (shift.toNat % 64)
  let u1S := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2S := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  let r2 := iterN2 bltu_2 v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)
  let r1 := iterN2 bltu_1 v0' v1' v2' v3' u1S r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2 bltu_0 v0' v1' v2' v3' u0S r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.1 r1.1 r2.1 (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  -- Scratch cells: bltu_0=true → j=0 call scratch; bltu_0=false → from previous iterations
  match bltu_2, bltu_1, bltu_0 with
  | false, false, false =>
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | false, false, true  =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1)
  | false, true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r2.2.1)
  | false, true,  true  =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1)
  | true,  false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u3S)
  | true,  false, true  =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1)
  | true,  true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r2.2.1)
  | true,  true,  true  =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1)

-- ============================================================================
-- Unified full n=2 DIV path with double addback: base → base+1068
-- ============================================================================

/-- Unified full n=2 DIV path (shift ≠ 0) with double addback,
    covering all 8 path combinations.
    Dispatches to per-case  lemmas via postcondition bridge. -/
theorem evm_div_n2_full_unified_spec (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
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
      (fullDivN2UnifiedPost bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0) := by
  cases bltu_2 <;> cases bltu_1 <;> cases bltu_0 <;>
    simp only [isTrialN2_j2, isTrialN2_j1, isTrialN2_j0,
               iterN2_false, iterN2_true]
      at hbltu_2 hbltu_1 hbltu_0
  · have h_eq : fullDivN2UnifiedPost false false false sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0 =
      fullDivN2AllMaxPost sp a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 := by
      delta fullDivN2UnifiedPost fullDivN2AllMaxPost; rfl
    rw [h_eq]; exact evm_div_n2_full_all_max_spec sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
      q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0
      hbnz hb3z hb2z hb1nz hshift_nz halign
      hbltu_2 hbltu_1 hbltu_0 hcarry2
  all_goals (
    first
    | (have h_eq : fullDivN2UnifiedPost false false true sp base a0 a1 a2 a3 b0 b1 b2 b3
          retMem dMem dloMem scratch_un0 = fullDivN2_FFT_Post sp base a0 a1 a2 a3 b0 b1 b2 b3
          := by delta fullDivN2UnifiedPost fullDivN2_FFT_Post; rfl
       rw [h_eq]; exact evm_div_n2_full_FFT_spec sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
          q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 nMem shiftMem jMem
          retMem dMem dloMem scratch_un0 hbnz hb3z hb2z hb1nz hshift_nz

          halign
          hbltu_2 hbltu_1 hbltu_0 hcarry2)
    | (have h_eq : fullDivN2UnifiedPost false true false sp base a0 a1 a2 a3 b0 b1 b2 b3
          retMem dMem dloMem scratch_un0 = fullDivN2_FTF_Post sp base a0 a1 a2 a3 b0 b1 b2 b3
          := by delta fullDivN2UnifiedPost fullDivN2_FTF_Post; rfl
       rw [h_eq]; exact evm_div_n2_full_FTF_spec sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
          q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 nMem shiftMem jMem
          retMem dMem dloMem scratch_un0 hbnz hb3z hb2z hb1nz hshift_nz

          halign
          hbltu_2 hbltu_1 hbltu_0 hcarry2)
    | (have h_eq : fullDivN2UnifiedPost false true true sp base a0 a1 a2 a3 b0 b1 b2 b3
          retMem dMem dloMem scratch_un0 = fullDivN2_FTT_Post sp base a0 a1 a2 a3 b0 b1 b2 b3
          := by delta fullDivN2UnifiedPost fullDivN2_FTT_Post; rfl
       rw [h_eq]; exact evm_div_n2_full_FTT_spec sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
          q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 nMem shiftMem jMem
          retMem dMem dloMem scratch_un0 hbnz hb3z hb2z hb1nz hshift_nz

          halign
          hbltu_2 hbltu_1 hbltu_0 hcarry2)
    | (have h_eq : fullDivN2UnifiedPost true false false sp base a0 a1 a2 a3 b0 b1 b2 b3
          retMem dMem dloMem scratch_un0 = fullDivN2_TFF_Post sp base a0 a1 a2 a3 b0 b1 b2 b3
          := by delta fullDivN2UnifiedPost fullDivN2_TFF_Post; rfl
       rw [h_eq]; exact evm_div_n2_full_TFF_spec sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
          q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 nMem shiftMem jMem
          retMem dMem dloMem scratch_un0 hbnz hb3z hb2z hb1nz hshift_nz

          halign
          hbltu_2 hbltu_1 hbltu_0 hcarry2)
    | (have h_eq : fullDivN2UnifiedPost true false true sp base a0 a1 a2 a3 b0 b1 b2 b3
          retMem dMem dloMem scratch_un0 = fullDivN2_TFT_Post sp base a0 a1 a2 a3 b0 b1 b2 b3
          := by delta fullDivN2UnifiedPost fullDivN2_TFT_Post; rfl
       rw [h_eq]; exact evm_div_n2_full_TFT_spec sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
          q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 nMem shiftMem jMem
          retMem dMem dloMem scratch_un0 hbnz hb3z hb2z hb1nz hshift_nz

          halign
          hbltu_2 hbltu_1 hbltu_0 hcarry2)
    | (have h_eq : fullDivN2UnifiedPost true true false sp base a0 a1 a2 a3 b0 b1 b2 b3
          retMem dMem dloMem scratch_un0 = fullDivN2_TTF_Post sp base a0 a1 a2 a3 b0 b1 b2 b3
          := by delta fullDivN2UnifiedPost fullDivN2_TTF_Post; rfl
       rw [h_eq]; exact evm_div_n2_full_TTF_spec sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
          q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 nMem shiftMem jMem
          retMem dMem dloMem scratch_un0 hbnz hb3z hb2z hb1nz hshift_nz

          halign
          hbltu_2 hbltu_1 hbltu_0 hcarry2)
    | (have h_eq : fullDivN2UnifiedPost true true true sp base a0 a1 a2 a3 b0 b1 b2 b3
          retMem dMem dloMem scratch_un0 = fullDivN2_TTT_Post sp base a0 a1 a2 a3 b0 b1 b2 b3
          := by delta fullDivN2UnifiedPost fullDivN2_TTT_Post; rfl
       rw [h_eq]; exact evm_div_n2_full_TTT_spec sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
          q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 nMem shiftMem jMem
          retMem dMem dloMem scratch_un0 hbnz hb3z hb2z hb1nz hshift_nz

          halign
          hbltu_2 hbltu_1 hbltu_0 hcarry2))

end EvmAsm.Evm64
