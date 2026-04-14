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

-- ============================================================================
-- Condition predicates for n=1 preloop+loop composition
-- ============================================================================

/-- j=3 trial condition for n=1: `bltu_3 = BitVec.ult u_hi_norm v_top_norm`
    where `shift = clz(b0)`, `u_hi_norm = a3 >>> anti_shift`,
    `v_top_norm = b0 <<< shift`. -/
def isTrialN1_j3 (bltu_3 : Bool) (a3 b0 : Word) : Prop :=
  let shift := (clzResult b0).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  bltu_3 = BitVec.ult
    (a3 >>> (anti_shift.toNat % 64))
    (b0 <<< (shift.toNat % 64))

/-- j=2 trial condition for n=1, dependent on j=3 path (bltu_3).
    Checks the BLTU condition after the j=3 iteration result. -/
def isTrialN1_j2 (bltu_3 bltu_2 : Bool) (a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b0).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  bltu_2 = BitVec.ult
    (iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)).2.1
    v0'

/-- j=1 trial condition for n=1, dependent on j=3 and j=2 paths. -/
def isTrialN1_j1 (bltu_3 bltu_2 bltu_1 : Bool) (a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b0).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r3 := iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)
  bltu_1 = BitVec.ult
    (iterN1 bltu_2 v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1).2.1
    v0'

/-- j=0 trial condition for n=1, dependent on j=3, j=2, and j=1 paths. -/
def isTrialN1_j0 (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b0).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r3 := iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)
  let r2 := iterN1 bltu_2 v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
  bltu_0 = BitVec.ult
    (iterN1 bltu_1 v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1).2.1
    v0'

-- ============================================================================
-- Unified preloop+loop postcondition
-- ============================================================================

/-- Unified postcondition for preloop+loop at n=1.
    Wraps loopN1UnifiedPost (with normalized values computed from a[],b[])
    plus frame atoms: a[0..3], spare q3 slot, spare u7 slot, shift. -/
@[irreducible]
def preloopN1UnifiedPost (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  let shift := (clzResult b0).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  loopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base
    v0' v1' v2' v3' u3_s (a3 >>> (anti_shift.toNat % 64)) (0 : Word) (0 : Word) (0 : Word)
    u2_s u1_s u0_s
    ret_mem d_mem dlo_mem scratch_un0 **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1)

-- ============================================================================
-- Loop instantiation helper (heartbeat isolation)
-- ============================================================================

/-- Helper: instantiate unified n=1 loop with explicit normalized values.
    Separates the loop application from the composition for heartbeat budgeting. -/
private theorem evm_div_n1_loop_unified_inst
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift anti_shift v0' v1' v2' v3' u0_s u1_s u2_s u3_s u4_s : Word)
    (v10_val v11_old j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_3 : isValidDwordAccess (sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_2 : isValidDwordAccess (sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
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
      v0') :
    cpsTriple (base + 448) (base + 908) (divCode base)
      (loopN1PreWithScratch sp j_mem (1 : Word) shift u0_s v10_val v11_old anti_shift
        v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)
        u2_s u1_s u0_s (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base
        v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)
        u2_s u1_s u0_s ret_mem d_mem dlo_mem scratch_un0) :=
  divK_loop_n1_unified_divCode bltu_3 bltu_2 bltu_1 bltu_0
    sp j_mem (1 : Word) shift u0_s v10_val v11_old anti_shift
    v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)
    u2_s u1_s u0_s (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi_3 hv_ulo_3 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hv_v0 hv_v1 hv_v2 hv_v3
    hv_u0_3 hv_u1_3 hv_u2_3 hv_u3_3 hv_u4_3 hv_q3
    hv_uhi_2 hv_ulo_2 hv_u0_2 hv_q2
    hv_uhi_1 hv_ulo_1 hv_u0_1 hv_q1
    hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
    hbltu_3 hbltu_2 hbltu_1 hbltu_0

-- ============================================================================
-- Unified preloop+loop composition (base → base+904)
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Unified preloop+loop for n=1, parameterized by `(bltu_3 bltu_2 bltu_1 bltu_0 : Bool)`.
    Covers all 16 path combinations.
    Precondition always includes scratch cells.
    Composes preloop (base→base+448) with unified loop (base+448→base+904). -/
theorem evm_div_n1_preloop_loop_unified_spec
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
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
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + 908) (divCode base)
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
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_mem) **
       ((sp + signExtend12 3968) ↦ₘ ret_mem) **
       ((sp + signExtend12 3960) ↦ₘ d_mem) **
       ((sp + signExtend12 3952) ↦ₘ dlo_mem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (preloopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        ret_mem d_mem dlo_mem scratch_un0) := by
  -- 1. Pre-loop: base → base+448
  have hPre := evm_div_n1_to_loopSetup_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem
    hbnz hb3z hb2z hb1z hshift_nz hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift
  -- Frame preloop with .x11, j_mem, scratch cells
  have hPreF := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ v11_old) ** ((sp + signExtend12 3976) ↦ₘ j_mem) **
     (sp + signExtend12 3968 ↦ₘ ret_mem) **
     (sp + signExtend12 3960 ↦ₘ d_mem) **
     (sp + signExtend12 3952 ↦ₘ dlo_mem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hPre
  -- 2. Loop: base+448 → base+904 (unified, with explicit normalized values)
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
    v11_old j_mem
    ret_mem d_mem dlo_mem scratch_un0
    hv_j hv_n
    (by rw [n1_uhi_3_addr]; exact hv_u4) (by rw [n1_ulo_3_addr]; exact hv_u3)
    (by rw [n1_vtop_addr, se12_32]; exact hvalid 4 (by omega))
    hv_ret hv_d hv_dlo hv_scratch_un0 halign
    (by rw [se12_32]; exact hvalid 4 (by omega))
    (by rw [se12_40]; exact hvalid 5 (by omega))
    (by rw [se12_48]; exact hvalid 6 (by omega))
    (by rw [se12_56]; exact hvalid 7 (by omega))
    (by rw [n1_ub3_off0]; exact hv_u3) (by rw [n1_ub3_off4088]; exact hv_u4)
    (by rw [n1_ub3_off4080]; exact hv_u5) (by rw [n1_ub3_off4072]; exact hv_u6)
    (by rw [n1_ub3_off4064]; exact hv_u7) (by rw [n1_qa3]; exact hv_q3)
    (by rw [n1_uhi_2_addr]; exact hv_u3) (by rw [n1_ulo_2_addr]; exact hv_u2)
    (by rw [n2_ub2_off0]; exact hv_u2) (by rw [n2_qa2]; exact hv_q2)
    (by rw [n1_uhi_1_addr]; exact hv_u2) (by rw [n1_ulo_1_addr]; exact hv_u1)
    (by rw [n3_ub1_off0]; exact hv_u1) (by rw [n3_qa1]; exact hv_q1)
    (by rw [n1_uhi_0_addr]; exact hv_u1) (by rw [n1_ulo_0_addr]; exact hv_u0)
    (by rw [n3_ub0_off0]; exact hv_u0) (by rw [n3_qa0]; exact hv_q0)
    hbltu_3 hbltu_2 hbltu_1 hbltu_0
  -- Frame loop with a[], shift_mem (no spare q/u for n=1)
  have hLoopF := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1))
    (by pcFree) hLoop
  -- 3. Compose preloop + loop
  have hFull := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
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
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopN1UnifiedPost; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
