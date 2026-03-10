/-
  EvmAsm.Evm64.DivModSpec

  CPS specifications for the 256-bit EVM DIV and MOD programs (Knuth Algorithm D).
  Bottom-up decomposition starting from the simplest phases.
-/

import EvmAsm.Evm64.DivMod
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Zero path: b = 0, push 0. 5 instructions.
-- ============================================================================

/-- Zero path: advance sp by 32, store four zeros at the output location.
    Used when b = 0 (both DIV and MOD return 0). -/
theorem divK_zeroPath_spec (sp : Addr) (base : Addr)
    (m32 m40 m48 m56 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code :=
      (base ↦ᵢ .ADDI .x12 .x12 32) **
      ((base + 4) ↦ᵢ .SD .x12 .x0 0) **
      ((base + 8) ↦ᵢ .SD .x12 .x0 8) **
      ((base + 12) ↦ᵢ .SD .x12 .x0 16) **
      ((base + 16) ↦ᵢ .SD .x12 .x0 24)
    cpsTriple base (base + 20)
      (code **
       (.x12 ↦ᵣ sp) **
       ((sp + 32) ↦ₘ m32) ** ((sp + 40) ↦ₘ m40) **
       ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56))
      (code **
       (.x12 ↦ᵣ (sp + 32)) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  have I0 := addi_spec_gen_same .x12 sp 32 base (by nofun)
  have I1 := sd_x0_spec_gen .x12 (sp + 32) m32 0 (base + 4) (by validMem)
  have I2 := sd_x0_spec_gen .x12 (sp + 32) m40 8 (base + 8) (by validMem)
  have I3 := sd_x0_spec_gen .x12 (sp + 32) m48 16 (base + 12) (by validMem)
  have I4 := sd_x0_spec_gen .x12 (sp + 32) m56 24 (base + 16) (by validMem)
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Phase A body: OR-reduce b[0..3]. 7 instructions (straight-line).
-- Pre/post include BEQ instruction and x0 for branch composition.
-- ============================================================================

/-- Phase A body: load and OR-reduce the 4 limbs of b.
    Produces x5 = b0 ||| b1 ||| b2 ||| b3.
    The BEQ instruction at base+28 and x0 are preserved for branch composition. -/
theorem divK_phaseA_body_spec (sp : Addr) (base : Addr)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code :=
      (base ↦ᵢ .LD .x5 .x12 32) **
      ((base + 4) ↦ᵢ .LD .x10 .x12 40) **
      ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 12) ↦ᵢ .LD .x10 .x12 48) **
      ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 20) ↦ᵢ .LD .x10 .x12 56) **
      ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 28) ↦ᵢ .BEQ .x5 .x0 1016)
    cpsTriple base (base + 28)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 b0 32 base (by nofun) (by validMem)
  have I1 := ld_spec_gen .x10 .x12 sp v10 b1 40 (base + 4) (by nofun) (by validMem)
  have I2 := or_spec_gen_rd_eq_rs1 .x5 .x10 b0 b1 (base + 8) (by nofun) (by nofun)
  have I3 := ld_spec_gen .x10 .x12 sp b1 b2 48 (base + 12) (by nofun) (by validMem)
  have I4 := or_spec_gen_rd_eq_rs1 .x5 .x10 (b0 ||| b1) b2 (base + 16) (by nofun) (by nofun)
  have I5 := ld_spec_gen .x10 .x12 sp b2 b3 56 (base + 20) (by nofun) (by validMem)
  have I6 := or_spec_gen_rd_eq_rs1 .x5 .x10 (b0 ||| b1 ||| b2) b3 (base + 24) (by nofun) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5 I6

-- ============================================================================
-- Phase A: full cpsBranch (body + BEQ)
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- Phase A: OR-reduce b then BEQ to zero path. -/
theorem divK_phaseA_spec (sp : Addr) (base : Addr)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hvalid : ValidMemRange sp 8) :
    let bor := b0 ||| b1 ||| b2 ||| b3
    let code :=
      (base ↦ᵢ .LD .x5 .x12 32) **
      ((base + 4) ↦ᵢ .LD .x10 .x12 40) **
      ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 12) ↦ᵢ .LD .x10 .x12 48) **
      ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 20) ↦ᵢ .LD .x10 .x12 56) **
      ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 28) ↦ᵢ .BEQ .x5 .x0 1016)
    let post :=
      code **
      (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ bor) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
      ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)
    cpsBranch base
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      -- Taken: bor = 0
      ((base + 28) + signExtend13 1016) post
      -- Not taken: bor ≠ 0
      (base + 32) post := by
  intro bor; intro code; intro post
  -- 1. Body: 7 straight-line instructions
  have hbody := divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10 hvalid
  -- 2. BEQ: branch at base + 28, drop pure facts from postconditions
  have hbeq_raw := beq_spec_gen .x5 .x0 1016 bor (0 : Word) (base + 28)
  have ha1 : (base + 28 : Addr) + 4 = base + 32 := by bv_omega
  have hbeq : cpsBranch (base + 28)
      (((base + 28) ↦ᵢ .BEQ .x5 .x0 1016) ** (.x5 ↦ᵣ bor) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 28) + signExtend13 1016)
        (((base + 28) ↦ᵢ .BEQ .x5 .x0 1016) ** (.x5 ↦ᵣ bor) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 32)
        (((base + 28) ↦ᵢ .BEQ .x5 .x0 1016) ** (.x5 ↦ᵣ bor) ** (.x0 ↦ᵣ (0 : Word))) := by
    rw [ha1] at hbeq_raw
    exact cpsBranch_consequence (base + 28) _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      hbeq_raw
  -- 3. Frame BEQ with body code, x12, x10, and memory
  have hbeq_framed := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .LD .x5 .x12 32) **
     ((base + 4) ↦ᵢ .LD .x10 .x12 40) **
     ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LD .x10 .x12 48) **
     ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LD .x10 .x12 56) **
     ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  -- 4. Compose body → branch with permutation
  have composed := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- 5. Final permutation of postconditions
  exact cpsBranch_consequence _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

-- ============================================================================
-- Phase B init: zero out q[0..3] and u[5..7], load b[1] and b[2].
-- 9 straight-line instructions.
-- ============================================================================

/-- Phase B init part 1: zero scratch q[0..3] and u[5..7]. 7 instructions. -/
theorem divK_phaseB_init1_spec (sp : Addr) (base : Addr)
    (q0 q1 q2 q3 u5 u6 u7 : Word)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true) :
    let code :=
      (base ↦ᵢ .SD .x12 .x0 4088) **
      ((base + 4) ↦ᵢ .SD .x12 .x0 4080) **
      ((base + 8) ↦ᵢ .SD .x12 .x0 4072) **
      ((base + 12) ↦ᵢ .SD .x12 .x0 4064) **
      ((base + 16) ↦ᵢ .SD .x12 .x0 4016) **
      ((base + 20) ↦ᵢ .SD .x12 .x0 4008) **
      ((base + 24) ↦ᵢ .SD .x12 .x0 4000)
    cpsTriple base (base + 28)
      (code **
       (.x12 ↦ᵣ sp) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7))
      (code **
       (.x12 ↦ᵣ sp) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word))) := by
  have I0 := sd_x0_spec_gen .x12 sp q0 4088 base hv_q0
  have I1 := sd_x0_spec_gen .x12 sp q1 4080 (base + 4) hv_q1
  have I2 := sd_x0_spec_gen .x12 sp q2 4072 (base + 8) hv_q2
  have I3 := sd_x0_spec_gen .x12 sp q3 4064 (base + 12) hv_q3
  have I4 := sd_x0_spec_gen .x12 sp u5 4016 (base + 16) hv_u5
  have I5 := sd_x0_spec_gen .x12 sp u6 4008 (base + 20) hv_u6
  have I6 := sd_x0_spec_gen .x12 sp u7 4000 (base + 24) hv_u7
  runBlock I0 I1 I2 I3 I4 I5 I6

/-- Phase B init part 2: load b[1] and b[2]. 2 instructions. -/
theorem divK_phaseB_init2_spec (sp : Addr) (base : Addr)
    (b1 b2 : Word) (v6 v7 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code :=
      (base ↦ᵢ .LD .x6 .x12 40) **
      ((base + 4) ↦ᵢ .LD .x7 .x12 48)
    cpsTriple base (base + 8)
      (code **
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2))
      (code **
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2)) := by
  have I0 := ld_spec_gen .x6 .x12 sp v6 b1 40 base (by nofun) (by validMem)
  have I1 := ld_spec_gen .x7 .x12 sp v7 b2 48 (base + 4) (by nofun) (by validMem)
  runBlock I0 I1

-- ============================================================================
-- Phase C4: Copy a → u[0..4] unshifted (shift = 0). 9 instructions.
-- ============================================================================

/-- Copy a[0..3] to u[0..3] and set u[4] = 0 (no shift needed). -/
theorem divK_copyAU_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 u0 u1 u2 u3 u4 : Word) (v5 : Word)
    (hvalid : ValidMemRange sp 8)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true) :
    let code :=
      (base ↦ᵢ .LD .x5 .x12 0) **
      ((base + 4) ↦ᵢ .SD .x12 .x5 4056) **
      ((base + 8) ↦ᵢ .LD .x5 .x12 8) **
      ((base + 12) ↦ᵢ .SD .x12 .x5 4048) **
      ((base + 16) ↦ᵢ .LD .x5 .x12 16) **
      ((base + 20) ↦ᵢ .SD .x12 .x5 4040) **
      ((base + 24) ↦ᵢ .LD .x5 .x12 24) **
      ((base + 28) ↦ᵢ .SD .x12 .x5 4032) **
      ((base + 32) ↦ᵢ .SD .x12 .x0 4024)
    cpsTriple base (base + 36)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u4))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
       ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ (0 : Word))) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 a0 0 base (by nofun) (by validMem)
  have I1 := sd_spec_gen .x12 .x5 sp a0 u0 4056 (base + 4) hv_u0
  have I2 := ld_spec_gen .x5 .x12 sp a0 a1 8 (base + 8) (by nofun) (by validMem)
  have I3 := sd_spec_gen .x12 .x5 sp a1 u1 4048 (base + 12) hv_u1
  have I4 := ld_spec_gen .x5 .x12 sp a1 a2 16 (base + 16) (by nofun) (by validMem)
  have I5 := sd_spec_gen .x12 .x5 sp a2 u2 4040 (base + 20) hv_u2
  have I6 := ld_spec_gen .x5 .x12 sp a2 a3 24 (base + 24) (by nofun) (by validMem)
  have I7 := sd_spec_gen .x12 .x5 sp a3 u3 4032 (base + 28) hv_u3
  have I8 := sd_x0_spec_gen .x12 sp u4 4024 (base + 32) hv_u4
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8

-- ============================================================================
-- NormB: Normalize b in-place (shift > 0). 21 instructions.
-- Per-limb decomposition: 3 merge limbs (6 instr each) + 1 last limb (3 instr).
-- ============================================================================

/-- NormB merge limb (6 instructions): LD high, LD low, SLL, SRL, OR, SD.
    Computes result = (high <<< shift) ||| (low >>> anti_shift) and stores to high_off.
    x6 = shift, x2 = anti_shift (= 64 - shift as unsigned). -/
theorem divK_normB_merge_spec (high_off low_off : BitVec 12)
    (sp high low v5 v7 shift anti_shift : Word) (base : Addr)
    (hvalid_high : isValidDwordAccess (sp + signExtend12 high_off) = true)
    (hvalid_low : isValidDwordAccess (sp + signExtend12 low_off) = true) :
    let shifted_high := high <<< (shift.toNat % 64)
    let shifted_low := low >>> (anti_shift.toNat % 64)
    let result := shifted_high ||| shifted_low
    let code :=
      (base ↦ᵢ .LD .x5 .x12 high_off) **
      ((base + 4) ↦ᵢ .LD .x7 .x12 low_off) **
      ((base + 8) ↦ᵢ .SLL .x5 .x5 .x6) **
      ((base + 12) ↦ᵢ .SRL .x7 .x7 .x2) **
      ((base + 16) ↦ᵢ .OR .x5 .x5 .x7) **
      ((base + 20) ↦ᵢ .SD .x12 .x5 high_off)
    cpsTriple base (base + 24)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 high_off) ↦ₘ high) **
       ((sp + signExtend12 low_off) ↦ₘ low))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x7 ↦ᵣ shifted_low) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 high_off) ↦ₘ result) **
       ((sp + signExtend12 low_off) ↦ₘ low)) := by
  intro shifted_high; intro shifted_low; intro result; intro code
  have I0 := ld_spec_gen .x5 .x12 sp v5 high high_off base (by nofun) hvalid_high
  have I1 := ld_spec_gen .x7 .x12 sp v7 low low_off (base + 4) (by nofun) hvalid_low
  have I2 := sll_spec_gen_rd_eq_rs1 .x5 .x6 high shift (base + 8) (by nofun) (by nofun)
  have I3 := srl_spec_gen_rd_eq_rs1 .x7 .x2 low anti_shift (base + 12) (by nofun) (by nofun)
  have I4 := or_spec_gen_rd_eq_rs1 .x5 .x7 shifted_high shifted_low (base + 16) (by nofun) (by nofun)
  have I5 := sd_spec_gen .x12 .x5 sp result high high_off (base + 20) hvalid_high
  runBlock I0 I1 I2 I3 I4 I5

/-- NormB last limb (3 instructions): LD, SLL, SD.
    Computes result = val <<< shift and stores to off. -/
theorem divK_normB_last_spec (off : BitVec 12)
    (sp val v5 shift : Word) (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let result := val <<< (shift.toNat % 64)
    let code :=
      (base ↦ᵢ .LD .x5 .x12 off) **
      ((base + 4) ↦ᵢ .SLL .x5 .x5 .x6) **
      ((base + 8) ↦ᵢ .SD .x12 .x5 off)
    cpsTriple base (base + 12)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ val))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ result)) := by
  intro result; intro code
  have I0 := ld_spec_gen .x5 .x12 sp v5 val off base (by nofun) hvalid
  have I1 := sll_spec_gen_rd_eq_rs1 .x5 .x6 val shift (base + 4) (by nofun) (by nofun)
  have I2 := sd_spec_gen .x12 .x5 sp result val off (base + 8) hvalid
  runBlock I0 I1 I2

-- ============================================================================
-- NormA: Normalize a → u[0..4] (shift > 0). 20 instructions (excl. JAL).
-- Per-limb decomposition: top (3 instr) + 3 merge (5 instr each) + last (2 instr).
-- ============================================================================

/-- NormA top: LD a[3], SRL to x7, SD u[4]. 3 instructions.
    Computes u[4] = a[3] >>> anti_shift (overflow bits from top limb). -/
theorem divK_normA_top_spec (src_off dst_off : BitVec 12)
    (sp val v5 v7 anti_shift dst_old : Word) (base : Addr)
    (hvalid_src : isValidDwordAccess (sp + signExtend12 src_off) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let result := val >>> (anti_shift.toNat % 64)
    let code :=
      (base ↦ᵢ .LD .x5 .x12 src_off) **
      ((base + 4) ↦ᵢ .SRL .x7 .x5 .x2) **
      ((base + 8) ↦ᵢ .SD .x12 .x7 dst_off)
    cpsTriple base (base + 12)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 src_off) ↦ₘ val) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ val) ** (.x7 ↦ᵣ result) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 src_off) ↦ₘ val) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro result; intro code
  have I0 := ld_spec_gen .x5 .x12 sp v5 val src_off base (by nofun) hvalid_src
  have I1 := srl_spec_gen .x7 .x5 .x2 v7 val anti_shift (base + 4) (by nofun)
  have I2 := sd_spec_gen .x12 .x7 sp result dst_old dst_off (base + 8) hvalid_dst
  runBlock I0 I1 I2

/-- NormA merge type A (5 instructions): x5 holds current limb.
    LD next into x7, SLL x5 by shift, SRL x10 from x7 by anti_shift, OR into x5, SD.
    Used for u[3] and u[1] computation. -/
theorem divK_normA_mergeA_spec (next_off dst_off : BitVec 12)
    (sp current next v7 v10 shift anti_shift dst_old : Word) (base : Addr)
    (hvalid_next : isValidDwordAccess (sp + signExtend12 next_off) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let shifted_curr := current <<< (shift.toNat % 64)
    let shifted_next := next >>> (anti_shift.toNat % 64)
    let result := shifted_curr ||| shifted_next
    let code :=
      (base ↦ᵢ .LD .x7 .x12 next_off) **
      ((base + 4) ↦ᵢ .SLL .x5 .x5 .x6) **
      ((base + 8) ↦ᵢ .SRL .x10 .x7 .x2) **
      ((base + 12) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 16) ↦ᵢ .SD .x12 .x5 dst_off)
    cpsTriple base (base + 20)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ current) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x7 ↦ᵣ next) ** (.x10 ↦ᵣ shifted_next) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro shifted_curr; intro shifted_next; intro result; intro code
  have I0 := ld_spec_gen .x7 .x12 sp v7 next next_off base (by nofun) hvalid_next
  have I1 := sll_spec_gen_rd_eq_rs1 .x5 .x6 current shift (base + 4) (by nofun) (by nofun)
  have I2 := srl_spec_gen .x10 .x7 .x2 v10 next anti_shift (base + 8) (by nofun)
  have I3 := or_spec_gen_rd_eq_rs1 .x5 .x10 shifted_curr shifted_next (base + 12) (by nofun) (by nofun)
  have I4 := sd_spec_gen .x12 .x5 sp result dst_old dst_off (base + 16) hvalid_dst
  runBlock I0 I1 I2 I3 I4

/-- NormA merge type B (5 instructions): x7 holds current limb.
    LD next into x5, SLL x7 by shift, SRL x10 from x5 by anti_shift, OR into x7, SD.
    Used for u[2] computation. -/
theorem divK_normA_mergeB_spec (next_off dst_off : BitVec 12)
    (sp current next v5 v10 shift anti_shift dst_old : Word) (base : Addr)
    (hvalid_next : isValidDwordAccess (sp + signExtend12 next_off) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let shifted_curr := current <<< (shift.toNat % 64)
    let shifted_next := next >>> (anti_shift.toNat % 64)
    let result := shifted_curr ||| shifted_next
    let code :=
      (base ↦ᵢ .LD .x5 .x12 next_off) **
      ((base + 4) ↦ᵢ .SLL .x7 .x7 .x6) **
      ((base + 8) ↦ᵢ .SRL .x10 .x5 .x2) **
      ((base + 12) ↦ᵢ .OR .x7 .x7 .x10) **
      ((base + 16) ↦ᵢ .SD .x12 .x7 dst_off)
    cpsTriple base (base + 20)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ current) ** (.x10 ↦ᵣ v10) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ next) ** (.x7 ↦ᵣ result) ** (.x10 ↦ᵣ shifted_next) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro shifted_curr; intro shifted_next; intro result; intro code
  have I0 := ld_spec_gen .x5 .x12 sp v5 next next_off base (by nofun) hvalid_next
  have I1 := sll_spec_gen_rd_eq_rs1 .x7 .x6 current shift (base + 4) (by nofun) (by nofun)
  have I2 := srl_spec_gen .x10 .x5 .x2 v10 next anti_shift (base + 8) (by nofun)
  have I3 := or_spec_gen_rd_eq_rs1 .x7 .x10 shifted_curr shifted_next (base + 12) (by nofun) (by nofun)
  have I4 := sd_spec_gen .x12 .x7 sp result dst_old dst_off (base + 16) hvalid_dst
  runBlock I0 I1 I2 I3 I4

/-- NormA last limb (2 instructions): SLL x7 by shift, SD to dst_off.
    Computes u[0] = a[0] <<< shift. -/
theorem divK_normA_last_spec (dst_off : BitVec 12)
    (sp val shift dst_old : Word) (base : Addr)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let result := val <<< (shift.toNat % 64)
    let code :=
      (base ↦ᵢ .SLL .x7 .x7 .x6) **
      ((base + 4) ↦ᵢ .SD .x12 .x7 dst_off)
    cpsTriple base (base + 8)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ val) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro result; intro code
  have I0 := sll_spec_gen_rd_eq_rs1 .x7 .x6 val shift base (by nofun) (by nofun)
  have I1 := sd_spec_gen .x12 .x7 sp result dst_old dst_off (base + 4) hvalid_dst
  runBlock I0 I1

-- ============================================================================
-- Denorm: De-normalize remainder. Per-limb specs for the shift body.
-- Same structure as NormB but SRL/SLL swapped (right-shift with merge from above).
-- ============================================================================

/-- Denorm merge limb (6 instructions): LD curr, LD next, SRL, SLL, OR, SD.
    Computes result = (curr >>> shift) ||| (next <<< anti_shift) and stores to curr_off.
    x6 = shift, x2 = anti_shift. -/
theorem divK_denorm_merge_spec (curr_off next_off : BitVec 12)
    (sp curr next v5 v7 shift anti_shift : Word) (base : Addr)
    (hvalid_curr : isValidDwordAccess (sp + signExtend12 curr_off) = true)
    (hvalid_next : isValidDwordAccess (sp + signExtend12 next_off) = true) :
    let shifted_curr := curr >>> (shift.toNat % 64)
    let shifted_next := next <<< (anti_shift.toNat % 64)
    let result := shifted_curr ||| shifted_next
    let code :=
      (base ↦ᵢ .LD .x5 .x12 curr_off) **
      ((base + 4) ↦ᵢ .LD .x7 .x12 next_off) **
      ((base + 8) ↦ᵢ .SRL .x5 .x5 .x6) **
      ((base + 12) ↦ᵢ .SLL .x7 .x7 .x2) **
      ((base + 16) ↦ᵢ .OR .x5 .x5 .x7) **
      ((base + 20) ↦ᵢ .SD .x12 .x5 curr_off)
    cpsTriple base (base + 24)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 curr_off) ↦ₘ curr) **
       ((sp + signExtend12 next_off) ↦ₘ next))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x7 ↦ᵣ shifted_next) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 curr_off) ↦ₘ result) **
       ((sp + signExtend12 next_off) ↦ₘ next)) := by
  intro shifted_curr; intro shifted_next; intro result; intro code
  have I0 := ld_spec_gen .x5 .x12 sp v5 curr curr_off base (by nofun) hvalid_curr
  have I1 := ld_spec_gen .x7 .x12 sp v7 next next_off (base + 4) (by nofun) hvalid_next
  have I2 := srl_spec_gen_rd_eq_rs1 .x5 .x6 curr shift (base + 8) (by nofun) (by nofun)
  have I3 := sll_spec_gen_rd_eq_rs1 .x7 .x2 next anti_shift (base + 12) (by nofun) (by nofun)
  have I4 := or_spec_gen_rd_eq_rs1 .x5 .x7 shifted_curr shifted_next (base + 16) (by nofun) (by nofun)
  have I5 := sd_spec_gen .x12 .x5 sp result curr curr_off (base + 20) hvalid_curr
  runBlock I0 I1 I2 I3 I4 I5

/-- Denorm last limb (3 instructions): LD, SRL, SD.
    Computes result = val >>> shift and stores to off. -/
theorem divK_denorm_last_spec (off : BitVec 12)
    (sp val v5 shift : Word) (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let result := val >>> (shift.toNat % 64)
    let code :=
      (base ↦ᵢ .LD .x5 .x12 off) **
      ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
      ((base + 8) ↦ᵢ .SD .x12 .x5 off)
    cpsTriple base (base + 12)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ val))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ result)) := by
  intro result; intro code
  have I0 := ld_spec_gen .x5 .x12 sp v5 val off base (by nofun) hvalid
  have I1 := srl_spec_gen_rd_eq_rs1 .x5 .x6 val shift (base + 4) (by nofun) (by nofun)
  have I2 := sd_spec_gen .x12 .x5 sp result val off (base + 8) hvalid
  runBlock I0 I1 I2

-- ============================================================================
-- Epilogue: Copy q[0..3] or u[0..3] to output. 10 instructions each.
-- Split into load phase (4 LD) + store phase (ADDI + 4 SD) + JAL.
-- ============================================================================

/-- Epilogue load phase: load 4 values from scratch space. 4 instructions.
    Loads q[0..3] (for DIV) or u[0..3] (for MOD) into x5, x6, x7, x10. -/
theorem divK_epilogue_load_spec (off0 off1 off2 off3 : BitVec 12)
    (sp r0 r1 r2 r3 v5 v6 v7 v10 : Word) (base : Addr)
    (hv0 : isValidDwordAccess (sp + signExtend12 off0) = true)
    (hv1 : isValidDwordAccess (sp + signExtend12 off1) = true)
    (hv2 : isValidDwordAccess (sp + signExtend12 off2) = true)
    (hv3 : isValidDwordAccess (sp + signExtend12 off3) = true) :
    let code :=
      (base ↦ᵢ .LD .x5 .x12 off0) **
      ((base + 4) ↦ᵢ .LD .x6 .x12 off1) **
      ((base + 8) ↦ᵢ .LD .x7 .x12 off2) **
      ((base + 12) ↦ᵢ .LD .x10 .x12 off3)
    cpsTriple base (base + 16)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 off0) ↦ₘ r0) ** ((sp + signExtend12 off1) ↦ₘ r1) **
       ((sp + signExtend12 off2) ↦ₘ r2) ** ((sp + signExtend12 off3) ↦ₘ r3))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r0) ** (.x6 ↦ᵣ r1) ** (.x7 ↦ᵣ r2) ** (.x10 ↦ᵣ r3) **
       ((sp + signExtend12 off0) ↦ₘ r0) ** ((sp + signExtend12 off1) ↦ₘ r1) **
       ((sp + signExtend12 off2) ↦ₘ r2) ** ((sp + signExtend12 off3) ↦ₘ r3)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 r0 off0 base (by nofun) hv0
  have I1 := ld_spec_gen .x6 .x12 sp v6 r1 off1 (base + 4) (by nofun) hv1
  have I2 := ld_spec_gen .x7 .x12 sp v7 r2 off2 (base + 8) (by nofun) hv2
  have I3 := ld_spec_gen .x10 .x12 sp v10 r3 off3 (base + 12) (by nofun) hv3
  runBlock I0 I1 I2 I3

/-- Epilogue store phase: ADDI sp+32, store 4 values, JAL to exit. 6 instructions. -/
theorem divK_epilogue_store_spec (sp : Addr) (base : Addr)
    (r0 r1 r2 r3 m0 m8 m16 m24 : Word) (jal_off : BitVec 21)
    (hvalid : ValidMemRange sp 8) :
    let code :=
      (base ↦ᵢ .ADDI .x12 .x12 32) **
      ((base + 4) ↦ᵢ .SD .x12 .x5 0) **
      ((base + 8) ↦ᵢ .SD .x12 .x6 8) **
      ((base + 12) ↦ᵢ .SD .x12 .x7 16) **
      ((base + 16) ↦ᵢ .SD .x12 .x10 24) **
      ((base + 20) ↦ᵢ .JAL .x0 jal_off)
    cpsTriple base (base + 20 + signExtend21 jal_off)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r0) ** (.x6 ↦ᵣ r1) ** (.x7 ↦ᵣ r2) ** (.x10 ↦ᵣ r3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (code **
       (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r0) ** (.x6 ↦ᵣ r1) ** (.x7 ↦ᵣ r2) ** (.x10 ↦ᵣ r3) **
       ((sp + 32) ↦ₘ r0) ** ((sp + 40) ↦ₘ r1) **
       ((sp + 48) ↦ₘ r2) ** ((sp + 56) ↦ₘ r3)) := by
  have I0 := addi_spec_gen_same .x12 sp 32 base (by nofun)
  have I1 := sd_spec_gen .x12 .x5 (sp + 32) r0 m0 0 (base + 4) (by validMem)
  have I2 := sd_spec_gen .x12 .x6 (sp + 32) r1 m8 8 (base + 8) (by validMem)
  have I3 := sd_spec_gen .x12 .x7 (sp + 32) r2 m16 16 (base + 12) (by validMem)
  have I4 := sd_spec_gen .x12 .x10 (sp + 32) r3 m24 24 (base + 16) (by validMem)
  have I5 := jal_x0_spec_gen jal_off (base + 20)
  runBlock I0 I1 I2 I3 I4 I5

-- ============================================================================
-- Phase B tail: store n, compute address of b[n-1], load leading limb.
-- 5 instructions: SD, ADDI, SLLI, ADD, LD.
-- ============================================================================

/-- Phase B tail: store n to scratch, compute sp + (n-1)*8, load b[n-1].
    x5 = n on entry. On exit, x5 = leading limb b[n-1]. -/
theorem divK_phaseB_tail_spec (sp n leading_limb n_mem : Word) (base : Addr)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_limb : isValidDwordAccess
      ((sp + ((n + signExtend12 4095) <<< (3 : BitVec 6).toNat)) + signExtend12 32) = true) :
    let nm1 := n + signExtend12 4095
    let nm1_x8 := nm1 <<< (3 : BitVec 6).toNat
    let addr_lead := sp + nm1_x8
    let code :=
      (base ↦ᵢ .SD .x12 .x5 3984) **
      ((base + 4) ↦ᵢ .ADDI .x5 .x5 4095) **
      ((base + 8) ↦ᵢ .SLLI .x5 .x5 3) **
      ((base + 12) ↦ᵢ .ADD .x5 .x12 .x5) **
      ((base + 16) ↦ᵢ .LD .x5 .x5 32)
    cpsTriple base (base + 20)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
       ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((addr_lead + signExtend12 32) ↦ₘ leading_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ leading_limb) **
       ((sp + signExtend12 3984) ↦ₘ n) **
       ((addr_lead + signExtend12 32) ↦ₘ leading_limb)) := by
  intro nm1; intro nm1_x8; intro addr_lead; intro code
  have I0 := sd_spec_gen .x12 .x5 sp n n_mem 3984 base hv_n
  have I1 := addi_spec_gen_same .x5 n 4095 (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x5 nm1 3 (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs2 .x5 .x12 sp nm1_x8 (base + 12) (by nofun) (by nofun)
  have I4 := ld_spec_gen_same .x5 addr_lead leading_limb 32 (base + 16) (by nofun) hv_limb
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Phase C2 body: store shift, compute anti_shift. 3 instructions.
-- ============================================================================

/-- Phase C2 body: SD shift to scratch, ADDI x2 = 0, SUB x2 = -shift.
    Preserves x6 and x0 for the subsequent BEQ.
    The postcondition uses `signExtend12 (0 : BitVec 12) - shift` (= 0 - shift)
    to match the syntactic form produced by addi_x0_spec_gen + sub_spec_gen. -/
theorem divK_phaseC2_body_spec (sp shift v2 shift_mem : Word)
    (shift0_off : BitVec 13) (base : Addr)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true) :
    let code :=
      (base ↦ᵢ .SD .x12 .x6 3992) **
      ((base + 4) ↦ᵢ .ADDI .x2 .x0 0) **
      ((base + 8) ↦ᵢ .SUB .x2 .x2 .x6) **
      ((base + 12) ↦ᵢ .BEQ .x6 .x0 shift0_off)
    cpsTriple base (base + 12)
      (code **
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem))
      (code **
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  intro code
  have I0 := sd_spec_gen .x12 .x6 sp shift shift_mem 3992 base hv_shift
  have I1 := addi_x0_spec_gen .x2 v2 0 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x2 .x6
    (signExtend12 (0 : BitVec 12)) shift (base + 8) (by nofun) (by nofun)
  runBlock I0 I1 I2

-- ============================================================================
-- Phase C2 full: body + BEQ (shift = 0 branch). cpsBranch.
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- Phase C2: store shift, compute anti_shift, BEQ if shift=0.
    Taken: shift = 0, skip normalization.
    Not taken: shift ≠ 0, proceed to normalize.
    anti_shift = signExtend12 0 - shift (= 0 - shift = negation of shift amount). -/
theorem divK_phaseC2_spec (sp shift v2 shift_mem : Word)
    (shift0_off : BitVec 13) (base : Addr)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true) :
    let code :=
      (base ↦ᵢ .SD .x12 .x6 3992) **
      ((base + 4) ↦ᵢ .ADDI .x2 .x0 0) **
      ((base + 8) ↦ᵢ .SUB .x2 .x2 .x6) **
      ((base + 12) ↦ᵢ .BEQ .x6 .x0 shift0_off)
    let post :=
      code **
      (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) **
      (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp + signExtend12 3992) ↦ₘ shift)
    cpsBranch base
      (code **
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem))
      -- Taken: shift = 0
      ((base + 12) + signExtend13 shift0_off) post
      -- Not taken: shift ≠ 0
      (base + 16) post := by
  intro code; intro post
  -- 1. Body: SD + ADDI + SUB
  have hbody := divK_phaseC2_body_spec sp shift v2 shift_mem shift0_off base hv_shift
  -- 2. BEQ at base + 12
  have hbeq_raw := beq_spec_gen .x6 .x0 shift0_off shift (0 : Word) (base + 12)
  have ha1 : (base + 12 : Addr) + 4 = base + 16 := by bv_omega
  have hbeq : cpsBranch (base + 12)
      (((base + 12) ↦ᵢ .BEQ .x6 .x0 shift0_off) ** (.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 12) + signExtend13 shift0_off)
        (((base + 12) ↦ᵢ .BEQ .x6 .x0 shift0_off) ** (.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 16)
        (((base + 12) ↦ᵢ .BEQ .x6 .x0 shift0_off) ** (.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word))) := by
    rw [ha1] at hbeq_raw
    exact cpsBranch_consequence (base + 12) _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      hbeq_raw
  -- 3. Frame BEQ with body code and extra atoms
  have hbeq_framed := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .SD .x12 .x6 3992) **
     ((base + 4) ↦ᵢ .ADDI .x2 .x0 0) **
     ((base + 8) ↦ᵢ .SUB .x2 .x2 .x6) **
     (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  -- 4. Compose body → BEQ
  have composed := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- 5. Final permutation
  exact cpsBranch_consequence _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

-- ============================================================================
-- Phase B cascade step: ADDI x5 n_val + BNE rx x0 offset. cpsBranch.
-- Used for each "if b[k]≠0 → n=k" step in the n-computation cascade.
-- ============================================================================

/-- Single cascade step: load n_val into x5, then BNE on rx vs x0.
    Taken: rx ≠ 0 (limb is nonzero), branch to target with x5 = n_val.
    Not taken: rx = 0, fall through with x5 = n_val. -/
theorem divK_phaseB_cascade_step_spec (n_val : BitVec 12) (rx : Reg) (check v5 : Word)
    (bne_off : BitVec 13) (base : Addr) :
    let n := (0 : Word) + signExtend12 n_val
    let code :=
      (base ↦ᵢ .ADDI .x5 .x0 n_val) **
      ((base + 4) ↦ᵢ .BNE rx .x0 bne_off)
    let post :=
      code ** (.x5 ↦ᵣ n) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check)
    cpsBranch base
      (code ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check))
      -- Taken: check ≠ 0
      ((base + 4) + signExtend13 bne_off) post
      -- Not taken: check = 0
      (base + 8) post := by
  intro n; intro code; intro post
  -- 1. ADDI body (includes all atoms: BNE instr and rx are frame)
  have hbody : cpsTriple base (base + 4)
      (code ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check))
      (code ** (.x5 ↦ᵣ n) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check)) := by
    have I0 := addi_spec_gen .x5 .x0 v5 (0 : Word) n_val base (by nofun)
    runBlock I0
  -- 2. BNE at base + 4, drop pure facts
  have hbne_raw := bne_spec_gen rx .x0 bne_off check (0 : Word) (base + 4)
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have hbne : cpsBranch (base + 4)
      (((base + 4) ↦ᵢ .BNE rx .x0 bne_off) ** (rx ↦ᵣ check) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 4) + signExtend13 bne_off)
        (((base + 4) ↦ᵢ .BNE rx .x0 bne_off) ** (rx ↦ᵣ check) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 8)
        (((base + 4) ↦ᵢ .BNE rx .x0 bne_off) ** (rx ↦ᵣ check) ** (.x0 ↦ᵣ (0 : Word))) := by
    rw [ha1] at hbne_raw
    exact cpsBranch_consequence (base + 4) _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      hbne_raw
  -- 3. Frame BNE with ADDI code and x5
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .ADDI .x5 .x0 n_val) ** (.x5 ↦ᵣ n))
    (by pcFree) hbne
  -- 4. Compose body → BNE with permutation
  have composed := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_framed
  -- 5. Final permutation
  exact cpsBranch_consequence _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

-- ============================================================================
-- Loop setup: LD n, compute m = 4 - n, BLT to skip loop.
-- 4 instructions: LD, ADDI, SUB, BLT. cpsBranch.
-- ============================================================================

/-- Loop setup body: load n, compute m = 4 - n. 3 straight-line instructions.
    Uses signExtend12 4 directly to match addi_x0_spec_gen + sub_spec_gen output. -/
theorem divK_loopSetup_body_spec (sp n v1 v5 : Word)
    (blt_off : BitVec 13) (base : Addr)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true) :
    let code :=
      (base ↦ᵢ .LD .x5 .x12 3984) **
      ((base + 4) ↦ᵢ .ADDI .x1 .x0 4) **
      ((base + 8) ↦ᵢ .SUB .x1 .x1 .x5) **
      ((base + 12) ↦ᵢ .BLT .x1 .x0 blt_off)
    cpsTriple base (base + 12)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
       (.x1 ↦ᵣ (signExtend12 (4 : BitVec 12) - n)) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n)) := by
  intro code
  have I0 := ld_spec_gen .x5 .x12 sp v5 n 3984 base (by nofun) hv_n
  have I1 := addi_x0_spec_gen .x1 v1 4 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x1 .x5
    (signExtend12 (4 : BitVec 12)) n (base + 8) (by nofun) (by nofun)
  runBlock I0 I1 I2

set_option maxHeartbeats 1600000 in
/-- Loop setup: load n, compute m = 4-n, BLT if m < 0 (skip loop).
    Taken: m < 0 (n > 4, impossible in practice but handled).
    Not taken: m >= 0, proceed to loop. -/
theorem divK_loopSetup_spec (sp n v1 v5 : Word)
    (blt_off : BitVec 13) (base : Addr)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true) :
    let m := signExtend12 (4 : BitVec 12) - n
    let code :=
      (base ↦ᵢ .LD .x5 .x12 3984) **
      ((base + 4) ↦ᵢ .ADDI .x1 .x0 4) **
      ((base + 8) ↦ᵢ .SUB .x1 .x1 .x5) **
      ((base + 12) ↦ᵢ .BLT .x1 .x0 blt_off)
    let post :=
      code **
      (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** (.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp + signExtend12 3984) ↦ₘ n)
    cpsBranch base
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      -- Taken: m < 0 (signed)
      ((base + 12) + signExtend13 blt_off) post
      -- Not taken: m >= 0
      (base + 16) post := by
  intro m; intro code; intro post
  -- 1. Body: LD + ADDI + SUB
  have hbody := divK_loopSetup_body_spec sp n v1 v5 blt_off base hv_n
  -- 2. BLT at base + 12
  have hblt_raw := blt_spec_gen .x1 .x0 blt_off m (0 : Word) (base + 12)
  have ha1 : (base + 12 : Addr) + 4 = base + 16 := by bv_omega
  have hblt : cpsBranch (base + 12)
      (((base + 12) ↦ᵢ .BLT .x1 .x0 blt_off) ** (.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 12) + signExtend13 blt_off)
        (((base + 12) ↦ᵢ .BLT .x1 .x0 blt_off) ** (.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 16)
        (((base + 12) ↦ᵢ .BLT .x1 .x0 blt_off) ** (.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word))) := by
    rw [ha1] at hblt_raw
    exact cpsBranch_consequence (base + 12) _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      hblt_raw
  -- 3. Frame BLT with body code and extra atoms
  have hblt_framed := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .LD .x5 .x12 3984) **
     ((base + 4) ↦ᵢ .ADDI .x1 .x0 4) **
     ((base + 8) ↦ᵢ .SUB .x1 .x1 .x5) **
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
     ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hblt
  -- 4. Compose body → BLT (body postcondition has signExtend12 4 - n, frame has m via let)
  have composed := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hblt_framed
  -- 5. Final permutation
  exact cpsBranch_consequence _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

-- ============================================================================
-- CLZ init: ADDI x6 x0 0. 1 instruction.
-- ============================================================================

/-- CLZ init: set x6 = 0 (count register). -/
theorem divK_clz_init_spec (v6 : Word) (base : Addr) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .ADDI .x6 .x0 0) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      ((base ↦ᵢ .ADDI .x6 .x0 0) ** (.x6 ↦ᵣ signExtend12 (0 : BitVec 12)) **
       (.x0 ↦ᵣ (0 : Word))) := by
  have I0 := addi_x0_spec_gen .x6 v6 0 base (by nofun)
  runBlock I0

-- ============================================================================
-- CLZ per-stage specs: SRLI x7 x5 K + BNE x7 x0 12 + SLLI x5 x5 M + ADDI x6 x6 M.
-- Two specs per stage: taken (shifted ≠ 0) and not-taken (shifted = 0).
-- Uses cpsBranch_elim_taken/ntaken to extract deterministic paths.
-- K : BitVec 6 (SRLI shamt), M_s : BitVec 6 (SLLI shamt), M_a : BitVec 12 (ADDI imm).
-- ============================================================================

/-- CLZ stage, taken branch: val >>> K ≠ 0, skip SLLI+ADDI.
    x5 = val (unchanged), x6 = count (unchanged), x7 = val >>> K. -/
theorem divK_clz_stage_taken_spec (K M_s : BitVec 6) (M_a : BitVec 12) (val count v7 : Word)
    (base : Addr)
    (hne : val >>> K.toNat ≠ 0) :
    let code :=
      (base ↦ᵢ .SRLI .x7 .x5 K) **
      ((base + 4) ↦ᵢ .BNE .x7 .x0 12) **
      ((base + 8) ↦ᵢ .SLLI .x5 .x5 M_s) **
      ((base + 12) ↦ᵢ .ADDI .x6 .x6 M_a)
    cpsTriple base (base + 16)
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) **
              (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro code
  -- 1. SRLI body
  have I0 := srli_spec_gen .x7 .x5 v7 val K base (by nofun)
  -- 2. BNE at base+4: taken → base+16 (skip SLLI+ADDI)
  have hbne_raw := bne_spec_gen .x7 .x0 (12 : BitVec 13) (val >>> K.toNat) (0 : Word) (base + 4)
  have hsig : signExtend13 (12 : BitVec 13) = (12 : Word) := by native_decide
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [hsig]; bv_omega
  have ha_f : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  rw [ha_t, ha_f] at hbne_raw
  -- 3. Frame BNE with SRLI code, SLLI code, ADDI code, x5, x6
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .SRLI .x7 .x5 K) **
     ((base + 8) ↦ᵢ .SLLI .x5 .x5 M_s) **
     ((base + 12) ↦ᵢ .ADDI .x6 .x6 M_a) **
     (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  -- 4. SRLI body (1 instruction, rest is frame)
  have hbody : cpsTriple base (base + 4)
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  -- 5. Compose SRLI body → BNE
  have composed := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_framed
  -- 6. Eliminate not-taken path (has ⌜val >>> K.toNat = 0⌝ which contradicts hne)
  have taken := cpsBranch_elim_taken _ _ _ _ _ _ composed (fun hp hQf => by
    obtain ⟨_, _, _, _, h_inner, _⟩ := hQf
    obtain ⟨_, _, _, _, _, h_rest⟩ := h_inner
    obtain ⟨_, _, _, _, _, h_x0p⟩ := h_rest
    exact hne ((sepConj_pure_right _ _ _).1 h_x0p).2)
  -- 7. Drop pure fact ⌜val >>> K.toNat ≠ 0⌝ from taken postcondition, then permute
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => hp)
    (fun h hp => by
      have hp' := sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (fun h hp => ((sepConj_pure_right _ _ h).1 hp).1))) h hp
      xperm_hyp hp')
    taken

/-- CLZ stage, not-taken branch: val >>> K = 0, execute SLLI+ADDI.
    x5 = val <<< M, x6 = count + signExtend12 M, x7 = 0. -/
theorem divK_clz_stage_ntaken_spec (K M_s : BitVec 6) (M_a : BitVec 12) (val count v7 : Word)
    (base : Addr)
    (heq : val >>> K.toNat = 0) :
    let code :=
      (base ↦ᵢ .SRLI .x7 .x5 K) **
      ((base + 4) ↦ᵢ .BNE .x7 .x0 12) **
      ((base + 8) ↦ᵢ .SLLI .x5 .x5 M_s) **
      ((base + 12) ↦ᵢ .ADDI .x6 .x6 M_a)
    cpsTriple base (base + 16)
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      (code ** (.x5 ↦ᵣ (val <<< M_s.toNat)) ** (.x6 ↦ᵣ (count + signExtend12 M_a)) **
              (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro code
  -- 1. SRLI body
  have I0 := srli_spec_gen .x7 .x5 v7 val K base (by nofun)
  -- 2. BNE at base+4
  have hbne_raw := bne_spec_gen .x7 .x0 (12 : BitVec 13) (val >>> K.toNat) (0 : Word) (base + 4)
  have hsig : signExtend13 (12 : BitVec 13) = (12 : Word) := by native_decide
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [hsig]; bv_omega
  have ha_f : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  rw [ha_t, ha_f] at hbne_raw
  -- 3. Frame BNE
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .SRLI .x7 .x5 K) **
     ((base + 8) ↦ᵢ .SLLI .x5 .x5 M_s) **
     ((base + 12) ↦ᵢ .ADDI .x6 .x6 M_a) **
     (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  -- 4. SRLI body (1 instruction, rest is frame)
  have hbody : cpsTriple base (base + 4)
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  -- 5. Compose SRLI body → BNE
  have composed := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_framed
  -- 6. Eliminate taken path (has ⌜val >>> K.toNat ≠ 0⌝ which contradicts heq)
  have ntaken := cpsBranch_elim_ntaken _ _ _ _ _ _ composed (fun hp hQt => by
    obtain ⟨_, _, _, _, h_inner, _⟩ := hQt
    obtain ⟨_, _, _, _, _, h_rest⟩ := h_inner
    obtain ⟨_, _, _, _, _, h_x0p⟩ := h_rest
    exact ((sepConj_pure_right _ _ _).1 h_x0p).2 (by rw [heq]))
  -- 6. SLLI + ADDI from base+8 to base+16
  have I1 := slli_spec_gen_same .x5 val M_s (base + 8) (by nofun)
  have I2 := addi_spec_gen_same .x6 count M_a (base + 12) (by nofun)
  have hslli_addi : cpsTriple (base + 8) (base + 16)
      (((base + 8) ↦ᵢ .SLLI .x5 .x5 M_s) ** ((base + 12) ↦ᵢ .ADDI .x6 .x6 M_a) **
       (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
      (((base + 8) ↦ᵢ .SLLI .x5 .x5 M_s) ** ((base + 12) ↦ᵢ .ADDI .x6 .x6 M_a) **
       (.x5 ↦ᵣ (val <<< M_s.toNat)) ** (.x6 ↦ᵣ (count + signExtend12 M_a))) := by
    runBlock I1 I2
  have hframed := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .SRLI .x7 .x5 K) **
     ((base + 4) ↦ᵢ .BNE .x7 .x0 12) **
     (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hslli_addi
  -- 7. Strip pure fact from ntaken, permute to match hframed's precondition, compose
  have full := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by
      have hp' := sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (fun h hp => ((sepConj_pure_right _ _ h).1 hp).1))) h hp
      xperm_hyp hp')
    ntaken hframed
  -- 8. Final permutation + rewrite x7 = 0
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => hp)
    (fun h hp => by rw [heq] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- CLZ last stage (stage 5): SRLI x7 x5 63 + BNE(8) + ADDI x6 x6 1
-- 3 instructions. BNE offset = 8 (not 12), no SLLI.
-- ============================================================================

/-- CLZ last stage, taken: val >>> 63 ≠ 0 (MSB is 1), skip ADDI.
    x5 unchanged, x6 unchanged, x7 = val >>> 63. -/
theorem divK_clz_last_taken_spec (val count v7 : Word) (base : Addr)
    (hne : val >>> 63 ≠ 0) :
    let code :=
      (base ↦ᵢ .SRLI .x7 .x5 63) **
      ((base + 4) ↦ᵢ .BNE .x7 .x0 8) **
      ((base + 8) ↦ᵢ .ADDI .x6 .x6 1)
    cpsTriple base (base + 12)
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) **
              (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro code
  have I0 := srli_spec_gen .x7 .x5 v7 val 63 base (by nofun)
  have h63 : (63 : BitVec 6).toNat = 63 := by native_decide
  simp only [h63] at I0
  have hbne_raw := bne_spec_gen .x7 .x0 (8 : BitVec 13) (val >>> 63) (0 : Word) (base + 4)
  have hsig : signExtend13 (8 : BitVec 13) = (8 : Word) := by native_decide
  have ha_t : (base + 4) + signExtend13 (8 : BitVec 13) = base + 12 := by rw [hsig]; bv_omega
  have ha_f : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  rw [ha_t, ha_f] at hbne_raw
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .SRLI .x7 .x5 63) **
     ((base + 8) ↦ᵢ .ADDI .x6 .x6 1) **
     (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  have hbody : cpsTriple base (base + 4)
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  have composed := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_framed
  have taken := cpsBranch_elim_taken _ _ _ _ _ _ composed (fun hp hQf => by
    obtain ⟨_, _, _, _, h_inner, _⟩ := hQf
    obtain ⟨_, _, _, _, _, h_rest⟩ := h_inner
    obtain ⟨_, _, _, _, _, h_x0p⟩ := h_rest
    exact hne ((sepConj_pure_right _ _ _).1 h_x0p).2)
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => hp)
    (fun h hp => by
      have hp' := sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (fun h hp => ((sepConj_pure_right _ _ h).1 hp).1))) h hp
      xperm_hyp hp')
    taken

/-- CLZ last stage, ntaken: val >>> 63 = 0, execute ADDI.
    x5 unchanged, x6 = count + 1, x7 = 0. -/
theorem divK_clz_last_ntaken_spec (val count v7 : Word) (base : Addr)
    (heq : val >>> 63 = 0) :
    let code :=
      (base ↦ᵢ .SRLI .x7 .x5 63) **
      ((base + 4) ↦ᵢ .BNE .x7 .x0 8) **
      ((base + 8) ↦ᵢ .ADDI .x6 .x6 1)
    cpsTriple base (base + 12)
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ (count + signExtend12 (1 : BitVec 12))) **
              (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro code
  have I0 := srli_spec_gen .x7 .x5 v7 val 63 base (by nofun)
  have h63 : (63 : BitVec 6).toNat = 63 := by native_decide
  simp only [h63] at I0
  have hbne_raw := bne_spec_gen .x7 .x0 (8 : BitVec 13) (val >>> 63) (0 : Word) (base + 4)
  have hsig : signExtend13 (8 : BitVec 13) = (8 : Word) := by native_decide
  have ha_t : (base + 4) + signExtend13 (8 : BitVec 13) = base + 12 := by rw [hsig]; bv_omega
  have ha_f : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  rw [ha_t, ha_f] at hbne_raw
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .SRLI .x7 .x5 63) **
     ((base + 8) ↦ᵢ .ADDI .x6 .x6 1) **
     (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  have hbody : cpsTriple base (base + 4)
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      (code ** (.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  have composed := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_framed
  have ntaken := cpsBranch_elim_ntaken _ _ _ _ _ _ composed (fun hp hQt => by
    obtain ⟨_, _, _, _, h_inner, _⟩ := hQt
    obtain ⟨_, _, _, _, _, h_rest⟩ := h_inner
    obtain ⟨_, _, _, _, _, h_x0p⟩ := h_rest
    exact ((sepConj_pure_right _ _ _).1 h_x0p).2 (by rw [heq]))
  -- ADDI from base+8 to base+12
  have I1 := addi_spec_gen_same .x6 count (1 : BitVec 12) (base + 8) (by nofun)
  have ha12 : (base + 8 : Addr) + 4 = base + 12 := by bv_omega
  rw [ha12] at I1
  have hframed := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .SRLI .x7 .x5 63) **
     ((base + 4) ↦ᵢ .BNE .x7 .x0 8) **
     (.x5 ↦ᵣ val) ** (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) I1
  have full := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by
      have hp' := sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (fun h hp => ((sepConj_pure_right _ _ h).1 hp).1))) h hp
      xperm_hyp hp')
    ntaken hframed
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => hp)
    (fun h hp => by rw [heq] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- Mul-sub limb: 11 instructions, core of the loop body.
-- q_hat * v[i] + carry_in, subtract from u[j+i].
-- ============================================================================

/-- Mul-sub limb Part A: LD v[i], MUL, MULHU, ADD, SLTU, ADD.
    6 instructions. Produces full_sub (x7) and partial_carry (x10). -/
theorem divK_mulsub_partA_spec (sp q_hat carry_in v5_old v7_old v_i : Word)
    (v_off : BitVec 12) (base : Addr)
    (hv : isValidDwordAccess (sp + signExtend12 v_off) = true) :
    let prod_lo := q_hat * v_i
    let prod_hi := rv64_mulhu q_hat v_i
    let full_sub := prod_lo + carry_in
    let borrow_add := if BitVec.ult full_sub carry_in then (1 : Word) else 0
    let partial_carry := borrow_add + prod_hi
    let code :=
      (base ↦ᵢ .LD .x5 .x12 v_off) **
      ((base + 4) ↦ᵢ .MUL .x7 .x11 .x5) **
      ((base + 8) ↦ᵢ .MULHU .x5 .x11 .x5) **
      ((base + 12) ↦ᵢ .ADD .x7 .x7 .x10) **
      ((base + 16) ↦ᵢ .SLTU .x10 .x7 .x10) **
      ((base + 20) ↦ᵢ .ADD .x10 .x10 .x5)
    cpsTriple base (base + 24)
      (code ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i))
      (code ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ partial_carry) **
       (.x5 ↦ᵣ prod_hi) ** (.x7 ↦ᵣ full_sub) **
       ((sp + signExtend12 v_off) ↦ₘ v_i)) := by
  intro prod_lo; intro prod_hi; intro full_sub; intro borrow_add; intro partial_carry; intro code
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun) hv
  have I1 := mul_spec_gen .x7 .x11 .x5 v7_old q_hat v_i (base + 4) (by nofun)
  have I2 := mulhu_spec_gen_rd_eq_rs2 .x5 .x11 q_hat v_i (base + 8) (by nofun) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1 .x7 .x10 prod_lo carry_in (base + 12) (by nofun) (by nofun)
  have I4 := sltu_spec_gen_rd_eq_rs2 .x10 .x7 full_sub carry_in (base + 16) (by nofun) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1 .x10 .x5 borrow_add prod_hi (base + 20) (by nofun) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5

/-- Mul-sub limb Part B: LD u[j+i], SLTU, SUB, ADD, SD.
    5 instructions. Produces carry_out (x10) and stores u_new. -/
theorem divK_mulsub_partB_spec (u_base partial_carry prod_hi full_sub v2_old u_i : Word)
    (u_off : BitVec 12) (base : Addr)
    (hv : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let borrow_sub := if BitVec.ult u_i full_sub then (1 : Word) else 0
    let u_new := u_i - full_sub
    let carry_out := partial_carry + borrow_sub
    let code :=
      (base ↦ᵢ .LD .x2 .x6 u_off) **
      ((base + 4) ↦ᵢ .SLTU .x5 .x2 .x7) **
      ((base + 8) ↦ᵢ .SUB .x2 .x2 .x7) **
      ((base + 12) ↦ᵢ .ADD .x10 .x10 .x5) **
      ((base + 16) ↦ᵢ .SD .x6 .x2 u_off)
    cpsTriple base (base + 20)
      (code ** (.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ partial_carry) **
       (.x5 ↦ᵣ prod_hi) ** (.x7 ↦ᵣ full_sub) ** (.x2 ↦ᵣ v2_old) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      (code ** (.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_out) **
       (.x5 ↦ᵣ borrow_sub) ** (.x7 ↦ᵣ full_sub) ** (.x2 ↦ᵣ u_new) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro borrow_sub; intro u_new; intro carry_out; intro code
  have I0 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off base (by nofun) hv
  have I1 := sltu_spec_gen .x5 .x2 .x7 prod_hi u_i full_sub (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x2 .x7 u_i full_sub (base + 8) (by nofun) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1 .x10 .x5 partial_carry borrow_sub (base + 12) (by nofun) (by nofun)
  have I4 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 16) hv
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Add-back correction limb: 8 instructions per limb.
-- u[j+i] += v[i] + carry_in, with carry propagation.
-- ============================================================================

/-- Add-back Part A: LD v[i], LD u[j+i], ADD carry, SLTU carry1, ADD v[i].
    5 instructions. Produces sum (x2) and carry1 (x7). -/
theorem divK_addback_partA_spec (sp u_base carry_in v5_old v2_old v_i u_i : Word)
    (v_off : BitVec 12) (u_off : BitVec 12) (base : Addr)
    (hv_v : isValidDwordAccess (sp + signExtend12 v_off) = true)
    (hv_u : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let u_plus_carry := u_i + carry_in
    let carry1 := if BitVec.ult u_plus_carry carry_in then (1 : Word) else 0
    let u_new := u_plus_carry + v_i
    let code :=
      (base ↦ᵢ .LD .x5 .x12 v_off) **
      ((base + 4) ↦ᵢ .LD .x2 .x6 u_off) **
      ((base + 8) ↦ᵢ .ADD .x2 .x2 .x7) **
      ((base + 12) ↦ᵢ .SLTU .x7 .x2 .x7) **
      ((base + 16) ↦ᵢ .ADD .x2 .x2 .x5)
    cpsTriple base (base + 20)
      (code ** (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      (code ** (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry1) **
       (.x5 ↦ᵣ v_i) ** (.x2 ↦ᵣ u_new) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i)) := by
  intro u_plus_carry; intro carry1; intro u_new; intro code
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun) hv_v
  have I1 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off (base + 4) (by nofun) hv_u
  have I2 := add_spec_gen_rd_eq_rs1 .x2 .x7 u_i carry_in (base + 8) (by nofun) (by nofun)
  have I3 := sltu_spec_gen_rd_eq_rs2 .x7 .x2 u_plus_carry carry_in (base + 12) (by nofun) (by nofun)
  have I4 := add_spec_gen_rd_eq_rs1 .x2 .x5 u_plus_carry v_i (base + 16) (by nofun) (by nofun)
  runBlock I0 I1 I2 I3 I4

/-- Add-back Part B: SLTU carry2, OR carry_out, SD u_new.
    3 instructions. Produces carry_out (x7) and stores u_new. -/
theorem divK_addback_partB_spec (u_base carry1 v_i u_new u_i : Word)
    (u_off : BitVec 12) (base : Addr)
    (hv_u : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let carry2 := if BitVec.ult u_new v_i then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    let code :=
      (base ↦ᵢ .SLTU .x5 .x2 .x5) **
      ((base + 4) ↦ᵢ .OR .x7 .x7 .x5) **
      ((base + 8) ↦ᵢ .SD .x6 .x2 u_off)
    cpsTriple base (base + 12)
      (code ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry1) **
       (.x5 ↦ᵣ v_i) ** (.x2 ↦ᵣ u_new) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      (code ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_out) **
       (.x5 ↦ᵣ carry2) ** (.x2 ↦ᵣ u_new) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro carry2; intro carry_out; intro code
  have I0 := sltu_spec_gen_rd_eq_rs2 .x5 .x2 u_new v_i base (by nofun) (by nofun)
  have I1 := or_spec_gen_rd_eq_rs1 .x7 .x5 carry1 carry2 (base + 4) (by nofun) (by nofun)
  have I2 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 8) hv_u
  runBlock I0 I1 I2

-- ============================================================================
-- Subtract carry from u[j+4]: 4 instructions after mul-sub limbs.
-- ============================================================================

/-- Subtract carry from u[j+4].
    4 instructions: LD, SLTU, SUB, SD. Produces borrow (x7). -/
theorem divK_sub_carry_spec (u_base carry_in v5_old v7_old u_top : Word)
    (u_off : BitVec 12) (base : Addr)
    (hv : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let borrow := if BitVec.ult u_top carry_in then (1 : Word) else 0
    let u_new := u_top - carry_in
    let code :=
      (base ↦ᵢ .LD .x5 .x6 u_off) **
      ((base + 4) ↦ᵢ .SLTU .x7 .x5 .x10) **
      ((base + 8) ↦ᵢ .SUB .x5 .x5 .x10) **
      ((base + 12) ↦ᵢ .SD .x6 .x5 u_off)
    cpsTriple base (base + 16)
      (code ** (.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       ((u_base + signExtend12 u_off) ↦ₘ u_top))
      (code ** (.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ u_new) ** (.x7 ↦ᵣ borrow) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro borrow; intro u_new; intro code
  have I0 := ld_spec_gen .x5 .x6 u_base v5_old u_top u_off base (by nofun) hv
  have I1 := sltu_spec_gen .x7 .x5 .x10 v7_old u_top carry_in (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x5 .x10 u_top carry_in (base + 8) (by nofun) (by nofun)
  have I3 := sd_spec_gen .x6 .x5 u_base u_new u_top u_off (base + 12) hv
  runBlock I0 I1 I2 I3

-- ============================================================================
-- Store q[j]: 4 instructions.
-- ============================================================================

/-- Store q[j]: compute &q[j] = sp+4088 - j*8, store q_hat.
    First 3 instructions compute q_addr. Then SD stores. Split into 3+1. -/
theorem divK_store_qj_addr_spec (sp j v5_old v7_old : Word)
    (base : Addr) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let sp_m8 := sp + signExtend12 4088
    let q_addr := sp_m8 - j_x8
    let code :=
      (base ↦ᵢ .SLLI .x5 .x1 3) **
      ((base + 4) ↦ᵢ .ADDI .x7 .x12 4088) **
      ((base + 8) ↦ᵢ .SUB .x7 .x7 .x5)
    cpsTriple base (base + 12)
      (code ** (.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old))
      (code ** (.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr)) := by
  intro j_x8; intro sp_m8; intro q_addr; intro code
  have I0 := slli_spec_gen .x5 .x1 v5_old j 3 base (by nofun)
  have I1 := addi_spec_gen .x7 .x12 v7_old sp 4088 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x7 .x5 sp_m8 j_x8 (base + 8) (by nofun) (by nofun)
  runBlock I0 I1 I2

/-- Store q[j]: SD q_hat at q_addr. 1 instruction. -/
theorem divK_store_qj_write_spec (q_addr q_hat q_old : Word) (base : Addr)
    (hv : isValidDwordAccess q_addr = true) :
    let code := (base ↦ᵢ .SD .x7 .x11 0)
    cpsTriple base (base + 4)
      (code ** (.x7 ↦ᵣ q_addr) ** (.x11 ↦ᵣ q_hat) ** (q_addr ↦ₘ q_old))
      (code ** (.x7 ↦ᵣ q_addr) ** (.x11 ↦ᵣ q_hat) ** (q_addr ↦ₘ q_hat)) := by
  intro code
  have hse : signExtend12 (0 : BitVec 12) = (0 : Word) := by native_decide
  have haddr : q_addr + signExtend12 (0 : BitVec 12) = q_addr := by rw [hse]; bv_omega
  have hv' : isValidDwordAccess (q_addr + signExtend12 0) = true := by rw [haddr]; exact hv
  have I0 := sd_spec_gen .x7 .x11 q_addr q_hat q_old 0 base hv'
  rw [haddr] at I0
  runBlock I0

-- ============================================================================
-- Add-back finalization: u[j+4] += carry, q_hat--.
-- 4 instructions: LD + ADD + SD + ADDI.
-- ============================================================================

/-- Add-back finalization after limb corrections. -/
theorem divK_addback_final_spec (u_base carry q_hat v5_old u_top : Word)
    (u_off : BitVec 12) (base : Addr)
    (hv : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let u_new := u_top + carry
    let q_hat' := q_hat + signExtend12 4095
    let code :=
      (base ↦ᵢ .LD .x5 .x6 u_off) **
      ((base + 4) ↦ᵢ .ADD .x5 .x5 .x7) **
      ((base + 8) ↦ᵢ .SD .x6 .x5 u_off) **
      ((base + 12) ↦ᵢ .ADDI .x11 .x11 4095)
    cpsTriple base (base + 16)
      (code ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (u_base + signExtend12 u_off ↦ₘ u_top))
      (code ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry) ** (.x11 ↦ᵣ q_hat') **
       (.x5 ↦ᵣ u_new) ** (u_base + signExtend12 u_off ↦ₘ u_new)) := by
  intro u_new; intro q_hat'; intro code
  have I0 := ld_spec_gen .x5 .x6 u_base v5_old u_top u_off base (by nofun) hv
  have I1 := add_spec_gen_rd_eq_rs1 .x5 .x7 u_top carry (base + 4) (by nofun) (by nofun)
  have I2 := sd_spec_gen .x6 .x5 u_base u_new u_top u_off (base + 8) hv
  have I3 := addi_spec_gen_same .x11 q_hat 4095 (base + 12) (by nofun)
  runBlock I0 I1 I2 I3

-- ============================================================================
-- Loop control: j-- and BGE loop back.
-- 2 instructions: ADDI + BGE.
-- ============================================================================

set_option maxRecDepth 1024 in
/-- Loop control: decrement j and branch back if j >= 0. -/
theorem divK_loop_control_spec (j : Word) (loop_back_off : BitVec 13)
    (base : Addr) :
    let j' := j + signExtend12 4095
    let code :=
      (base ↦ᵢ .ADDI .x1 .x1 4095) **
      ((base + 4) ↦ᵢ .BGE .x1 .x0 loop_back_off)
    cpsBranch base
      (code ** (.x1 ↦ᵣ j) ** (.x0 ↦ᵣ 0))
      (base + 4 + signExtend13 loop_back_off)
      (code ** (.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      (base + 8)
      (code ** (.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) := by
  intro j'; intro code
  -- 1. ADDI body
  have hbody : cpsTriple base (base + 4)
      (code ** (.x1 ↦ᵣ j) ** (.x0 ↦ᵣ 0))
      (code ** (.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) := by
    have I0 := addi_spec_gen_same .x1 j 4095 base (by nofun)
    runBlock I0
  -- 2. BGE, drop pure facts
  have hbge_raw := bge_spec_gen .x1 .x0 loop_back_off j' 0 (base + 4)
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have hbge : cpsBranch (base + 4)
      (((base + 4) ↦ᵢ .BGE .x1 .x0 loop_back_off) ** (.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      ((base + 4) + signExtend13 loop_back_off)
        (((base + 4) ↦ᵢ .BGE .x1 .x0 loop_back_off) ** (.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      (base + 8)
        (((base + 4) ↦ᵢ .BGE .x1 .x0 loop_back_off) ** (.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) := by
    rw [ha1] at hbge_raw
    exact cpsBranch_consequence (base + 4) _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      hbge_raw
  -- 3. Frame BGE with ADDI code
  have hbge_framed := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .ADDI .x1 .x1 4095))
    (by pcFree) hbge
  -- 4. Compose body → BGE
  have composed := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbge_framed
  -- 5. Final permutation
  exact cpsBranch_consequence _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

-- ============================================================================
-- Mul-sub setup: restore j, compute u_base = &u[j], init carry = 0.
-- 5 instructions: LD + SLLI + ADDI + SUB + ADDI.
-- ============================================================================

/-- Mul-sub setup: restore j from scratch, compute u_base, zero carry. -/
theorem divK_mulsub_setup_spec (sp q_hat j v1_old v5_old v6_old v10_old : Word)
    (base : Addr)
    (hv : isValidDwordAccess (sp + signExtend12 3976) = true) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let sp_m40 := sp + signExtend12 4056
    let u_base := sp_m40 - j_x8
    let code :=
      (base ↦ᵢ .LD .x1 .x12 3976) **
      ((base + 4) ↦ᵢ .SLLI .x5 .x1 3) **
      ((base + 8) ↦ᵢ .ADDI .x6 .x12 4056) **
      ((base + 12) ↦ᵢ .SUB .x6 .x6 .x5) **
      ((base + 16) ↦ᵢ .ADDI .x10 .x0 0)
    cpsTriple base (base + 20)
      (code ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x1 ↦ᵣ v1_old) ** (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x10 ↦ᵣ v10_old) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j))
      (code ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ j_x8) ** (.x6 ↦ᵣ u_base) **
       (.x10 ↦ᵣ signExtend12 0) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j)) := by
  intro j_x8; intro sp_m40; intro u_base; intro code
  have I0 := ld_spec_gen .x1 .x12 sp v1_old j 3976 base (by nofun) hv
  have I1 := slli_spec_gen .x5 .x1 v5_old j 3 (base + 4) (by nofun)
  have I2 := addi_spec_gen .x6 .x12 v6_old sp 4056 (base + 8) (by nofun)
  have I3 := sub_spec_gen_rd_eq_rs1 .x6 .x5 sp_m40 j_x8 (base + 12) (by nofun) (by nofun)
  have I4 := addi_x0_spec_gen .x10 v10_old 0 (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Save j: 1 instruction SD.
-- ============================================================================

/-- Save j to scratch memory. -/
theorem divK_save_j_spec (sp j j_old : Word) (base : Addr)
    (hv : isValidDwordAccess (sp + signExtend12 3976) = true) :
    let code := (base ↦ᵢ .SD .x12 .x1 3976)
    cpsTriple base (base + 4)
      (code ** (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) ** (sp + signExtend12 3976 ↦ₘ j_old))
      (code ** (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) ** (sp + signExtend12 3976 ↦ₘ j)) := by
  intro code
  have I0 := sd_spec_gen .x12 .x1 sp j j_old 3976 base hv
  runBlock I0

-- ============================================================================
-- Addback carry init: ADDI x7 x0 0 (set carry = 0).
-- ============================================================================

/-- Initialize add-back carry to 0. -/
theorem divK_addback_init_spec (v7_old : Word) (base : Addr) :
    let code := (base ↦ᵢ .ADDI .x7 .x0 0)
    cpsTriple base (base + 4)
      (code ** (.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ 0))
      (code ** (.x7 ↦ᵣ signExtend12 0) ** (.x0 ↦ᵣ 0)) := by
  intro code
  have I0 := addi_x0_spec_gen .x7 v7_old 0 base (by nofun)
  runBlock I0

-- ============================================================================
-- Addback condition: BEQ x7 x0 (skip correction if no borrow).
-- ============================================================================

/-- Correction condition: branch if borrow (x7) is zero. -/
theorem divK_correction_branch_spec (borrow : Word) (skip_off : BitVec 13) (base : Addr) :
    let code := (base ↦ᵢ .BEQ .x7 .x0 skip_off)
    cpsBranch base
      (code ** (.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ 0))
      (base + signExtend13 skip_off)
      (code ** (.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ 0))
      (base + 4)
      (code ** (.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ 0)) := by
  intro code
  exact cpsBranch_consequence _ _ _ _ _ _ _ _ _
    (fun _ hp => hp)
    (fun h hp => sepConj_mono_right (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
    (fun h hp => sepConj_mono_right (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
    (beq_spec_gen .x7 .x0 skip_off borrow 0 base)

-- ============================================================================
-- Trial quotient: load u[j+n], u[j+n-1].
-- 7 instructions: LD + ADD + SLLI + ADDI + SUB + LD + LD.
-- ============================================================================

/-- Load u_hi = u[j+n] and u_lo = u[j+n-1] for trial quotient estimation.
    u_addr = sp + signExtend12 4056 - (j + n) <<< 3.
    u_hi = mem[u_addr], u_lo = mem[u_addr + 8]. -/
theorem divK_trial_load_u_spec (sp j n v5_old v7_old u_hi u_lo : Word)
    (base : Addr)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) + 8) = true) :
    let jpn := j + n
    let jpn_x8 := jpn <<< (3 : BitVec 6).toNat
    let u0_base := sp + signExtend12 4056
    let u_addr := u0_base - jpn_x8
    let code :=
      (base ↦ᵢ .LD .x5 .x12 3984) **
      ((base + 4) ↦ᵢ .ADD .x7 .x1 .x5) **
      ((base + 8) ↦ᵢ .SLLI .x7 .x7 3) **
      ((base + 12) ↦ᵢ .ADDI .x5 .x12 4056) **
      ((base + 16) ↦ᵢ .SUB .x5 .x5 .x7) **
      ((base + 20) ↦ᵢ .LD .x7 .x5 0) **
      ((base + 24) ↦ᵢ .LD .x5 .x5 8)
    cpsTriple base (base + 28)
      (code ** (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo))
      (code ** (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u_lo) ** (.x7 ↦ᵣ u_hi) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo)) := by
  intro jpn; intro jpn_x8; intro u0_base; intro u_addr; intro code
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by native_decide
  have haddr0 : u_addr + signExtend12 (0 : BitVec 12) = u_addr := by rw [hse0]; bv_omega
  have hv_uhi' : isValidDwordAccess (u_addr + signExtend12 0) = true := by rw [haddr0]; exact hv_uhi
  have I0 := ld_spec_gen .x5 .x12 sp v5_old n 3984 base (by nofun) hv_n
  have I1 := add_spec_gen .x7 .x1 .x5 j n v7_old (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x7 jpn 3 (base + 8) (by nofun)
  have I3 := addi_spec_gen .x5 .x12 n sp 4056 (base + 12) (by nofun)
  have I4 := sub_spec_gen_rd_eq_rs1 .x5 .x7 u0_base jpn_x8 (base + 16) (by nofun) (by nofun)
  have I5 := ld_spec_gen .x7 .x5 u_addr jpn_x8 u_hi 0 (base + 20) (by nofun) hv_uhi'
  rw [haddr0] at I5
  have I6 := ld_spec_gen_same .x5 u_addr u_lo 8 (base + 24) (by nofun) hv_ulo
  runBlock I0 I1 I2 I3 I4 I5 I6

-- ============================================================================
-- Trial quotient: load v_top = b[n-1].
-- 5 instructions: LD + ADDI + SLLI + ADD + LD.
-- ============================================================================

/-- Load v_top = b[n-1] for trial quotient estimation.
    vtop_addr = sp + (n + signExtend12 4095) <<< 3.
    v_top = mem[vtop_addr + 32]. -/
theorem divK_trial_load_vtop_spec (sp n v6_old v10_old v_top : Word)
    (base : Addr)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_vtop : isValidDwordAccess (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true) :
    let nm1 := n + signExtend12 4095
    let nm1_x8 := nm1 <<< (3 : BitVec 6).toNat
    let vtop_base := sp + nm1_x8
    let code :=
      (base ↦ᵢ .LD .x6 .x12 3984) **
      ((base + 4) ↦ᵢ .ADDI .x6 .x6 4095) **
      ((base + 8) ↦ᵢ .SLLI .x6 .x6 3) **
      ((base + 12) ↦ᵢ .ADD .x6 .x12 .x6) **
      ((base + 16) ↦ᵢ .LD .x10 .x6 32)
    cpsTriple base (base + 20)
      (code ** (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6_old) ** (.x10 ↦ᵣ v10_old) **
       (sp + signExtend12 3984 ↦ₘ n) ** (vtop_base + signExtend12 32 ↦ₘ v_top))
      (code ** (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ vtop_base) ** (.x10 ↦ᵣ v_top) **
       (sp + signExtend12 3984 ↦ₘ n) ** (vtop_base + signExtend12 32 ↦ₘ v_top)) := by
  intro nm1; intro nm1_x8; intro vtop_base; intro code
  have I0 := ld_spec_gen .x6 .x12 sp v6_old n 3984 base (by nofun) hv_n
  have I1 := addi_spec_gen_same .x6 n 4095 (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x6 nm1 3 (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs2 .x6 .x12 sp nm1_x8 (base + 12) (by nofun) (by nofun)
  have I4 := ld_spec_gen .x10 .x6 vtop_base v10_old v_top 32 (base + 16) (by nofun) hv_vtop
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Trial quotient: MAX path (u_hi >= v_top).
-- 2 instructions: ADDI x11 x0 4095 + JAL x0 8.
-- ============================================================================

/-- Trial quotient MAX path: set q_hat = MAX64, jump over div128 call. -/
theorem divK_trial_max_spec (v11_old : Word) (base : Addr) :
    let code :=
      (base ↦ᵢ .ADDI .x11 .x0 4095) **
      ((base + 4) ↦ᵢ .JAL .x0 8)
    cpsTriple base (base + 12)
      (code ** (.x11 ↦ᵣ v11_old) ** (.x0 ↦ᵣ 0))
      (code ** (.x11 ↦ᵣ signExtend12 4095) ** (.x0 ↦ᵣ 0)) := by
  intro code
  have hj : signExtend21 (8 : BitVec 21) = (8 : Addr) := by native_decide
  have I0 := addi_x0_spec_gen .x11 v11_old 4095 base (by nofun)
  have I1 := jal_x0_spec_gen 8 (base + 4)
  rw [hj] at I1
  have ha : (base + 4 : Addr) + 8 = base + 12 := by bv_omega
  rw [ha] at I1
  runBlock I0 I1

-- ============================================================================
-- div128 subroutine: Phase 1a — save return addr and d, split d.
-- 6 instructions: SD + SD + SRLI + SLLI + SRLI + SD.
-- ============================================================================

/-- div128 Phase 1a: save x2 (return addr) and x10 (d), compute d_hi and d_lo. -/
theorem divK_div128_save_split_d_spec (sp ret_addr d v1_old v6_old
    ret_mem d_mem dlo_mem : Word) (base : Addr)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true) :
    let d_hi := d >>> (32 : BitVec 6).toNat
    let d_lo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let code :=
      (base ↦ᵢ .SD .x12 .x2 3968) **
      ((base + 4) ↦ᵢ .SD .x12 .x10 3960) **
      ((base + 8) ↦ᵢ .SRLI .x6 .x10 32) **
      ((base + 12) ↦ᵢ .SLLI .x1 .x10 32) **
      ((base + 16) ↦ᵢ .SRLI .x1 .x1 32) **
      ((base + 20) ↦ᵢ .SD .x12 .x1 3952)
    cpsTriple base (base + 24)
      (code ** (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x6 ↦ᵣ v6_old) ** (.x1 ↦ᵣ v1_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem))
      (code ** (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x6 ↦ᵣ d_hi) ** (.x1 ↦ᵣ d_lo) **
       (sp + signExtend12 3968 ↦ₘ ret_addr) **
       (sp + signExtend12 3960 ↦ₘ d) **
       (sp + signExtend12 3952 ↦ₘ d_lo)) := by
  intro d_hi; intro d_lo; intro code
  have I0 := sd_spec_gen .x12 .x2 sp ret_addr ret_mem 3968 base hv_ret
  have I1 := sd_spec_gen .x12 .x10 sp d d_mem 3960 (base + 4) hv_d
  have I2 := srli_spec_gen .x6 .x10 v6_old d 32 (base + 8) (by nofun)
  have I3 := slli_spec_gen .x1 .x10 v1_old d 32 (base + 12) (by nofun)
  have I4 := srli_spec_gen_same .x1 (d <<< (32 : BitVec 6).toNat) 32 (base + 16) (by nofun)
  have I5 := sd_spec_gen .x12 .x1 sp d_lo dlo_mem 3952 (base + 20) hv_dlo
  runBlock I0 I1 I2 I3 I4 I5

-- ============================================================================
-- div128 subroutine: Phase 1b — split u_lo into un1, un0, save un0.
-- 4 instructions: SRLI + SLLI + SRLI + SD.
-- ============================================================================

/-- div128 Phase 1b: split u_lo into un1 (x11) and un0 (x5), save un0. -/
theorem divK_div128_split_ulo_spec (sp u_lo v11_old un0_mem : Word) (base : Addr)
    (hv_un0 : isValidDwordAccess (sp + signExtend12 3944) = true) :
    let un1 := u_lo >>> (32 : BitVec 6).toNat
    let un0 := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let code :=
      (base ↦ᵢ .SRLI .x11 .x5 32) **
      ((base + 4) ↦ᵢ .SLLI .x5 .x5 32) **
      ((base + 8) ↦ᵢ .SRLI .x5 .x5 32) **
      ((base + 12) ↦ᵢ .SD .x12 .x5 3944)
    cpsTriple base (base + 16)
      (code ** (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u_lo) ** (.x11 ↦ᵣ v11_old) **
       (sp + signExtend12 3944 ↦ₘ un0_mem))
      (code ** (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ un0) ** (.x11 ↦ᵣ un1) **
       (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro un1; intro un0; intro code
  have I0 := srli_spec_gen .x11 .x5 v11_old u_lo 32 base (by nofun)
  have I1 := slli_spec_gen_same .x5 u_lo 32 (base + 4) (by nofun)
  have I2 := srli_spec_gen_same .x5 (u_lo <<< (32 : BitVec 6).toNat) 32 (base + 8) (by nofun)
  have I3 := sd_spec_gen .x12 .x5 sp un0 un0_mem 3944 (base + 12) hv_un0
  runBlock I0 I1 I2 I3

-- ============================================================================
-- div128 subroutine: Step 1 initial — DIVU q1, compute rhat.
-- 3 instructions: DIVU + MUL + SUB.
-- ============================================================================

/-- div128 Step 1: q1 = DIVU(u_hi, d_hi), rhat = u_hi - q1 * d_hi. -/
theorem divK_div128_step1_init_spec (u_hi d_hi v5_old v10_old : Word) (base : Addr) :
    let q1 := rv64_divu u_hi d_hi
    let rhat := u_hi - q1 * d_hi
    let code :=
      (base ↦ᵢ .DIVU .x10 .x7 .x6) **
      ((base + 4) ↦ᵢ .MUL .x5 .x10 .x6) **
      ((base + 8) ↦ᵢ .SUB .x7 .x7 .x5)
    cpsTriple base (base + 12)
      (code ** (.x7 ↦ᵣ u_hi) ** (.x6 ↦ᵣ d_hi) **
       (.x10 ↦ᵣ v10_old) ** (.x5 ↦ᵣ v5_old))
      (code ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi) **
       (.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q1 * d_hi)) := by
  intro q1; intro rhat; intro code
  have I0 := divu_spec_gen .x10 .x7 .x6 v10_old u_hi d_hi base (by nofun)
  have I1 := mul_spec_gen .x5 .x10 .x6 v5_old q1 d_hi (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x7 .x5 u_hi (q1 * d_hi) (base + 8) (by nofun) (by nofun)
  runBlock I0 I1 I2

-- ============================================================================
-- div128 subroutine: Compute un21 from rhat, un1, q1, d_lo.
-- 5 instructions: LD + SLLI + OR + MUL + SUB.
-- ============================================================================

/-- div128 un21 = rhat*2^32 + un1 - q1*d_lo.
    Loads d_lo from scratch memory. -/
theorem divK_div128_compute_un21_spec (sp q1 rhat un1 v1_old v5_old dlo_mem : Word) (base : Addr)
    (hv : isValidDwordAccess (sp + signExtend12 3952) = true) :
    let rhat_hi := rhat <<< (32 : BitVec 6).toNat
    let rhat_un1 := rhat_hi ||| un1
    let q1_dlo := q1 * dlo_mem
    let un21 := rhat_un1 - q1_dlo
    let code :=
      (base ↦ᵢ .LD .x1 .x12 3952) **
      ((base + 4) ↦ᵢ .SLLI .x5 .x7 32) **
      ((base + 8) ↦ᵢ .OR .x5 .x5 .x11) **
      ((base + 12) ↦ᵢ .MUL .x1 .x10 .x1) **
      ((base + 16) ↦ᵢ .SUB .x7 .x5 .x1)
    cpsTriple base (base + 20)
      (code ** (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) **
       (.x11 ↦ᵣ un1) ** (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem))
      (code ** (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ un21) **
       (.x11 ↦ᵣ un1) ** (.x5 ↦ᵣ rhat_un1) ** (.x1 ↦ᵣ q1_dlo) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem)) := by
  intro rhat_hi; intro rhat_un1; intro q1_dlo; intro un21; intro code
  have I0 := ld_spec_gen .x1 .x12 sp v1_old dlo_mem 3952 base (by nofun) hv
  have I1 := slli_spec_gen .x5 .x7 v5_old rhat 32 (base + 4) (by nofun)
  have I2 := or_spec_gen_rd_eq_rs1 .x5 .x11 rhat_hi un1 (base + 8) (by nofun) (by nofun)
  have I3 := mul_spec_gen_rd_eq_rs2 .x1 .x10 q1 dlo_mem (base + 12) (by nofun) (by nofun)
  have I4 := sub_spec_gen .x7 .x5 .x1 rhat_un1 q1_dlo rhat (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4


-- ============================================================================
-- div128 subroutine: Product check body (before BLTU).
-- 4 instructions: LD + MUL + SLLI + OR.
-- ============================================================================

/-- div128 product check body: compute q*d_lo and rhat*2^32+un1 for comparison. -/
theorem divK_div128_prodcheck_body_spec (sp q rhat un1 v1_old v5_old dlo : Word) (base : Addr)
    (hv : isValidDwordAccess (sp + signExtend12 3952) = true) :
    let q_dlo := q * dlo
    let rhat_hi := rhat <<< (32 : BitVec 6).toNat
    let rhat_un1 := rhat_hi ||| un1
    let code :=
      (base ↦ᵢ .LD .x1 .x12 3952) **
      ((base + 4) ↦ᵢ .MUL .x5 .x10 .x1) **
      ((base + 8) ↦ᵢ .SLLI .x1 .x7 32) **
      ((base + 12) ↦ᵢ .OR .x1 .x1 .x11)
    cpsTriple base (base + 16)
      (code ** (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) ** (sp + signExtend12 3952 ↦ₘ dlo))
      (code ** (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ q_dlo) ** (.x1 ↦ᵣ rhat_un1) ** (sp + signExtend12 3952 ↦ₘ dlo)) := by
  intro q_dlo; intro rhat_hi; intro rhat_un1; intro code
  have I0 := ld_spec_gen .x1 .x12 sp v1_old dlo 3952 base (by nofun) hv
  have I1 := mul_spec_gen .x5 .x10 .x1 v5_old q dlo (base + 4) (by nofun)
  have I2 := slli_spec_gen .x1 .x7 dlo rhat 32 (base + 8) (by nofun)
  have I3 := or_spec_gen_rd_eq_rs1 .x1 .x11 (rhat <<< (32 : BitVec 6).toNat) un1 (base + 12) (by nofun) (by nofun)
  runBlock I0 I1 I2 I3

-- ============================================================================
-- div128 subroutine: Correction path (2 instrs: ADDI q-- + ADD rhat+=d_hi).
-- Used after product check BLTU taken, and also after q1/q0 clamp BEQ ntaken.
-- ============================================================================

/-- div128 correction: q-- and rhat += d_hi. Generic for q1 (x10) or q0 (x5). -/
theorem divK_div128_correct_q1_spec (q rhat d_hi : Word) (base : Addr) :
    let q' := q + signExtend12 4095
    let rhat' := rhat + d_hi
    let code :=
      (base ↦ᵢ .ADDI .x10 .x10 4095) **
      ((base + 4) ↦ᵢ .ADD .x7 .x7 .x6)
    cpsTriple base (base + 8)
      (code ** (.x10 ↦ᵣ q) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi))
      (code ** (.x10 ↦ᵣ q') ** (.x7 ↦ᵣ rhat') ** (.x6 ↦ᵣ d_hi)) := by
  intro q'; intro rhat'; intro code
  have I0 := addi_spec_gen_same .x10 q 4095 base (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1 .x7 .x6 rhat d_hi (base + 4) (by nofun) (by nofun)
  runBlock I0 I1

/-- div128 correction for q0: q0-- and rhat2 += d_hi. -/
theorem divK_div128_correct_q0_spec (q0 rhat2 d_hi : Word) (base : Addr) :
    let q0' := q0 + signExtend12 4095
    let rhat2' := rhat2 + d_hi
    let code :=
      (base ↦ᵢ .ADDI .x5 .x5 4095) **
      ((base + 4) ↦ᵢ .ADD .x11 .x11 .x6)
    cpsTriple base (base + 8)
      (code ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi))
      (code ** (.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ rhat2') ** (.x6 ↦ᵣ d_hi)) := by
  intro q0'; intro rhat2'; intro code
  have I0 := addi_spec_gen_same .x5 q0 4095 base (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1 .x11 .x6 rhat2 d_hi (base + 4) (by nofun) (by nofun)
  runBlock I0 I1

-- ============================================================================
-- div128 subroutine: q1 clamp body (SRLI test, before BEQ).
-- 1 instruction: SRLI x5 x10 32.
-- ============================================================================

/-- div128 q1 clamp test: x5 = q1 >>> 32 (nonzero iff q1 >= 2^32). -/
theorem divK_div128_clamp_test_q1_spec (q1 v5_old : Word) (base : Addr) :
    let hi := q1 >>> (32 : BitVec 6).toNat
    let code := (base ↦ᵢ .SRLI .x5 .x10 32)
    cpsTriple base (base + 4)
      (code ** (.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ v5_old))
      (code ** (.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ hi)) := by
  intro hi; intro code
  have I0 := srli_spec_gen .x5 .x10 v5_old q1 32 base (by nofun)
  runBlock I0

/-- div128 q0 clamp test: x1 = q0 >>> 32. -/
theorem divK_div128_clamp_test_q0_spec (q0 v1_old : Word) (base : Addr) :
    let hi := q0 >>> (32 : BitVec 6).toNat
    let code := (base ↦ᵢ .SRLI .x1 .x5 32)
    cpsTriple base (base + 4)
      (code ** (.x5 ↦ᵣ q0) ** (.x1 ↦ᵣ v1_old))
      (code ** (.x5 ↦ᵣ q0) ** (.x1 ↦ᵣ hi)) := by
  intro hi; intro code
  have I0 := srli_spec_gen .x1 .x5 v1_old q0 32 base (by nofun)
  runBlock I0

-- ============================================================================
-- div128 subroutine: Step 2 initial — DIVU q0, compute rhat2.
-- 3 instructions: DIVU + MUL + SUB.
-- ============================================================================

/-- div128 Step 2: q0 = DIVU(un21, d_hi), rhat2 = un21 - q0 * d_hi. -/
theorem divK_div128_step2_init_spec (un21 d_hi v1_old v5_old v11_old : Word) (base : Addr) :
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let code :=
      (base ↦ᵢ .DIVU .x5 .x7 .x6) **
      ((base + 4) ↦ᵢ .MUL .x1 .x5 .x6) **
      ((base + 8) ↦ᵢ .SUB .x11 .x7 .x1)
    cpsTriple base (base + 12)
      (code ** (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) ** (.x11 ↦ᵣ v11_old))
      (code ** (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ q0) ** (.x1 ↦ᵣ q0 * d_hi) ** (.x11 ↦ᵣ rhat2)) := by
  intro q0; intro rhat2; intro code
  have I0 := divu_spec_gen .x5 .x7 .x6 v5_old un21 d_hi base (by nofun)
  have I1 := mul_spec_gen .x1 .x5 .x6 v1_old q0 d_hi (base + 4) (by nofun)
  have I2 := sub_spec_gen .x11 .x7 .x1 un21 (q0 * d_hi) v11_old (base + 8) (by nofun)
  runBlock I0 I1 I2

-- ============================================================================
-- div128 subroutine: Product check 2 body (instrs 37-41).
-- 5 instructions: LD + MUL + SLLI + LD + OR.
-- ============================================================================

/-- div128 product check 2: compute q0*d_lo and rhat2*2^32+un0 for comparison. -/
theorem divK_div128_prodcheck2_body_spec (sp q0 rhat2 v1_old v7_old dlo un0 : Word)
    (base : Addr)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_un0 : isValidDwordAccess (sp + signExtend12 3944) = true) :
    let q0_dlo := q0 * dlo
    let rhat2_hi := rhat2 <<< (32 : BitVec 6).toNat
    let rhat2_un0 := rhat2_hi ||| un0
    let code :=
      (base ↦ᵢ .LD .x1 .x12 3952) **
      ((base + 4) ↦ᵢ .MUL .x7 .x5 .x1) **
      ((base + 8) ↦ᵢ .SLLI .x1 .x11 32) **
      ((base + 12) ↦ᵢ .LD .x11 .x12 3944) **
      ((base + 16) ↦ᵢ .OR .x1 .x1 .x11)
    cpsTriple base (base + 20)
      (code ** (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) **
       (.x7 ↦ᵣ v7_old) ** (.x1 ↦ᵣ v1_old) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (code ** (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
       (.x7 ↦ᵣ q0_dlo) ** (.x1 ↦ᵣ rhat2_un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0_dlo; intro rhat2_hi; intro rhat2_un0; intro code
  have I0 := ld_spec_gen .x1 .x12 sp v1_old dlo 3952 base (by nofun) hv_dlo
  have I1 := mul_spec_gen .x7 .x5 .x1 v7_old q0 dlo (base + 4) (by nofun)
  have I2 := slli_spec_gen .x1 .x11 dlo rhat2 32 (base + 8) (by nofun)
  have I3 := ld_spec_gen .x11 .x12 sp rhat2 un0 3944 (base + 12) (by nofun) hv_un0
  have I4 := or_spec_gen_rd_eq_rs1 .x1 .x11 rhat2_hi un0 (base + 16) (by nofun) (by nofun)
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- div128 subroutine: Single-instr ADDI correction (product check 2, q0--).
-- 1 instruction: ADDI x5 x5 4095.
-- ============================================================================

/-- div128 product check 2 correction: q0--. -/
theorem divK_div128_correct_q0_single_spec (q0 : Word) (base : Addr) :
    let q0' := q0 + signExtend12 4095
    let code := (base ↦ᵢ .ADDI .x5 .x5 4095)
    cpsTriple base (base + 4)
      (code ** (.x5 ↦ᵣ q0))
      (code ** (.x5 ↦ᵣ q0')) := by
  intro q0'; intro code
  have I0 := addi_spec_gen_same .x5 q0 4095 base (by nofun)
  runBlock I0

-- ============================================================================
-- div128 subroutine: Combine q = q1<<32 | q0 (instrs 45-46).
-- 2 instructions: SLLI + OR.
-- ============================================================================

/-- div128 combine: x11 = q1<<32 | q0. -/
theorem divK_div128_combine_q_spec (q1 q0 v11_old : Word) (base : Addr) :
    let q1_hi := q1 <<< (32 : BitVec 6).toNat
    let q := q1_hi ||| q0
    let code :=
      (base ↦ᵢ .SLLI .x11 .x10 32) **
      ((base + 4) ↦ᵢ .OR .x11 .x11 .x5)
    cpsTriple base (base + 8)
      (code ** (.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ v11_old))
      (code ** (.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ q)) := by
  intro q1_hi; intro q; intro code
  have I0 := slli_spec_gen .x11 .x10 v11_old q1 32 base (by nofun)
  have I1 := or_spec_gen_rd_eq_rs1 .x11 .x5 q1_hi q0 (base + 4) (by nofun) (by nofun)
  runBlock I0 I1

-- ============================================================================
-- div128 subroutine: Restore return addr + JALR return (instrs 47-48).
-- 2 instructions: LD + JALR.
-- ============================================================================

/-- div128 restore and return: load return addr, JALR x0 x2 0. -/
theorem divK_div128_restore_return_spec (sp v2_old ret_addr : Word) (base : Addr)
    (hv : isValidDwordAccess (sp + signExtend12 3968) = true)
    (halign : (ret_addr + signExtend12 0) &&& ~~~1 = ret_addr) :
    let code :=
      (base ↦ᵢ .LD .x2 .x12 3968) **
      ((base + 4) ↦ᵢ .JALR .x0 .x2 0)
    cpsTriple base ret_addr
      (code ** (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2_old) ** (sp + signExtend12 3968 ↦ₘ ret_addr))
      (code ** (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (sp + signExtend12 3968 ↦ₘ ret_addr)) := by
  intro code
  have I0 := ld_spec_gen .x2 .x12 sp v2_old ret_addr 3968 base (by nofun) hv
  have I1 := jalr_x0_spec_gen .x2 ret_addr 0 (base + 4)
  rw [halign] at I1
  runBlock I0 I1

-- ============================================================================
-- Helper: strip pure assertion from a ** chain at depth 3.
-- A ** B ** C ** ⌜P⌝ ** D  →  A ** B ** C ** D
-- ============================================================================

private theorem sepConj_strip_pure_depth3 (A B C D : Assertion) (P : Prop) :
    ∀ h, (A ** B ** C ** ⌜P⌝ ** D) h → (A ** B ** C ** D) h :=
  fun h hp => sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (fun hd hpd => ((sepConj_pure_left P D hd).1 hpd).2))) h hp

private theorem sepConj_strip_pure_end3 (A B C : Assertion) (P : Prop) :
    ∀ h, (A ** B ** C ** ⌜P⌝) h → (A ** B ** C) h :=
  fun h hp => sepConj_mono_right (sepConj_mono_right
    (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp

-- ============================================================================
-- div128 subroutine: Clamp q1 section [13]-[16].
-- 4 instructions: SRLI + BEQ + ADDI + ADD.
-- BEQ skips correction if q1 < 2^32, else q1-- and rhat+=d_hi.
-- ============================================================================

set_option maxRecDepth 1024 in
/-- div128 clamp q1: test q1 >= 2^32, conditionally decrement and adjust rhat.
    Instrs [13]-[16]. Both BEQ paths merge at base+16. -/
theorem divK_div128_clamp_q1_merged_spec (q1 rhat d_hi v5_old : Word) (base : Addr) :
    let hi := q1 >>> (32 : BitVec 6).toNat
    let q1' := if hi = 0 then q1 else q1 + signExtend12 4095
    let rhat' := if hi = 0 then rhat else rhat + d_hi
    let code :=
      (base ↦ᵢ .SRLI .x5 .x10 32) **
      ((base + 4) ↦ᵢ .BEQ .x5 .x0 12) **
      ((base + 8) ↦ᵢ .ADDI .x10 .x10 4095) **
      ((base + 12) ↦ᵢ .ADD .x7 .x7 .x6)
    cpsTriple base (base + 16)
      (code ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ v5_old) ** (.x0 ↦ᵣ 0))
      (code ** (.x10 ↦ᵣ q1') ** (.x7 ↦ᵣ rhat') ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
  intro hi; intro q1'; intro rhat'; intro code
  -- 1. SRLI body with full code
  have hbody : cpsTriple base (base + 4)
      (code ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ v5_old) ** (.x0 ↦ᵣ 0))
      (code ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
    have I0 := srli_spec_gen .x5 .x10 v5_old q1 32 base (by nofun)
    runBlock I0
  -- 2. BEQ branch at [14]
  have hsig : signExtend13 (12 : BitVec 13) = (12 : Word) := by native_decide
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [hsig]; bv_omega
  have hbeq := beq_spec_gen .x5 .x0 12 hi 0 (base + 4)
  rw [ha_t] at hbeq
  -- 3. Frame BEQ with all remaining atoms (srli, addi, add code + regs)
  have hbeq_framed := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .SRLI .x5 .x10 32) **
     ((base + 8) ↦ᵢ .ADDI .x10 .x10 4095) **
     ((base + 12) ↦ᵢ .ADD .x7 .x7 .x6) **
     (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi))
    (by pcFree) hbeq
  -- 4. Compose SRLI → BEQ into cpsBranch
  have hbranch := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- 5. Case split on condition
  by_cases hcond : hi = 0
  · -- Taken: BEQ jumps to base+16, no correction needed
    simp only [q1', rhat', hcond, ↓reduceIte]
    -- Extract taken path (ntaken is absurd because ⌜hi≠0⌝ contradicts hi=0)
    simp only [hcond] at hbranch
    have h_elim := cpsBranch_elim_taken _ _ _ _ _ _ hbranch (fun hp hQf => by
      obtain ⟨h1, h2, _, _, h1p, _⟩ := hQf
      obtain ⟨_, h1b, _, _, _, h1bp⟩ := h1p
      obtain ⟨_, h1c, _, _, _, h1cp⟩ := h1bp
      exact absurd rfl ((sepConj_pure_right _ _ h1c).1 h1cp).2)
    -- Weaken postcondition: strip ⌜hi=0⌝ from end and rearrange
    -- Q_t_framed left factor: BEQ ** x5 ** x0 ** ⌜hi=0⌝
    exact cpsTriple_consequence _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => by
        have hp' := sepConj_mono_left
          (sepConj_strip_pure_end3 _ _ _ True) h hp
        xperm_hyp hp')
      h_elim
  · -- Not-taken: fall through to ADDI+ADD correction
    have hne : hi ≠ 0 := hcond
    simp only [q1', rhat', show (hi = 0) = False from propext ⟨hne.elim, False.elim⟩, ↓reduceIte]
    -- Extract not-taken path (taken is absurd because ⌜hi=0⌝ contradicts hi≠0)
    have h_elim := cpsBranch_elim_ntaken _ _ _ _ _ _ hbranch (fun hp hQt => by
      obtain ⟨h1, h2, _, _, h1p, _⟩ := hQt
      obtain ⟨_, h1b, _, _, _, h1bp⟩ := h1p
      obtain ⟨_, h1c, _, _, _, h1cp⟩ := h1bp
      exact hcond ((sepConj_pure_right _ _ h1c).1 h1cp).2)
    -- Normalize exit address: base+4+4 → base+8
    have ha8 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
    rw [ha8] at h_elim
    -- Correction: ADDI + ADD from base+8 to base+16
    have ha12 : (base + 8 : Addr) + 4 = base + 12 := by bv_omega
    have ha16 : (base + 8 : Addr) + 8 = base + 16 := by bv_omega
    have hcorr := divK_div128_correct_q1_spec q1 rhat d_hi (base + 8)
    rw [ha12, ha16] at hcorr
    -- Frame correction with BEQ code + x5 + x0 + ⌜hi≠0⌝ + SRLI (keep pure in frame)
    have hcorr_framed := cpsTriple_frame_left _ _ _ _
      (((base + 4) ↦ᵢ .BEQ .x5 .x0 12) ** (.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ 0) **
       ⌜hi ≠ 0⌝ ** (base ↦ᵢ .SRLI .x5 .x10 32))
      (by pcFree) hcorr
    -- Compose: h_elim → hcorr_framed (xperm handles permutation, ⌜hi≠0⌝ stays)
    have h_composed := cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) h_elim hcorr_framed
    -- Weaken post: strip ⌜hi≠0⌝ and rearrange
    -- h_composed post: corr_post ** (BEQ ** x5 ** x0 ** ⌜hi≠0⌝ ** SRLI)
    exact cpsTriple_consequence _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => by
        have hp' := sepConj_mono_right
          (sepConj_strip_pure_depth3 _ _ _ _ (hi ≠ 0)) h hp
        xperm_hyp hp')
      h_composed

-- ============================================================================
-- div128 subroutine: Product check 1 section [17]-[24].
-- 8 instructions: LD+MUL+SLLI+OR (body) + BLTU+JAL (branch) + ADDI+ADD (correction).
-- BLTU taken → correction, BLTU ntaken → JAL skip. Both merge at base+32.
-- ============================================================================

set_option maxRecDepth 1024 in
/-- div128 product check 1: compute q1*d_lo vs rhat*2^32+un1, conditionally correct.
    Instrs [17]-[24]. Both BLTU paths merge at base+32. -/
theorem divK_div128_prodcheck1_merged_spec
    (sp q1 rhat d_hi un1 v1_old v5_old dlo : Word) (base : Addr)
    (hv : isValidDwordAccess (sp + signExtend12 3952) = true) :
    let q_dlo := q1 * dlo
    let rhat_un1 := (rhat <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1 + signExtend12 4095 else q1
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhat + d_hi else rhat
    let code :=
      (base ↦ᵢ .LD .x1 .x12 3952) **
      ((base + 4) ↦ᵢ .MUL .x5 .x10 .x1) **
      ((base + 8) ↦ᵢ .SLLI .x1 .x7 32) **
      ((base + 12) ↦ᵢ .OR .x1 .x1 .x11) **
      ((base + 16) ↦ᵢ .BLTU .x1 .x5 8) **
      ((base + 20) ↦ᵢ .JAL .x0 12) **
      ((base + 24) ↦ᵢ .ADDI .x10 .x10 4095) **
      ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6)
    cpsTriple base (base + 32)
      (code ** (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) ** (.x6 ↦ᵣ d_hi) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      (code ** (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1') ** (.x7 ↦ᵣ rhat') ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ q_dlo) ** (.x1 ↦ᵣ rhat_un1) ** (.x6 ↦ᵣ d_hi) **
       (sp + signExtend12 3952 ↦ₘ dlo)) := by
  intro q_dlo; intro rhat_un1; intro q1'; intro rhat'; intro code
  -- 1. Prodcheck body [17]-[20], framed with branch/correction code + x6
  have hbody_raw := divK_div128_prodcheck_body_spec sp q1 rhat un1 v1_old v5_old dlo base hv
  have hbody := cpsTriple_frame_left _ _ _ _
    (((base + 16) ↦ᵢ .BLTU .x1 .x5 8) **
     ((base + 20) ↦ᵢ .JAL .x0 12) **
     ((base + 24) ↦ᵢ .ADDI .x10 .x10 4095) **
     ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6) **
     (.x6 ↦ᵣ d_hi))
    (by pcFree) hbody_raw
  -- 2. BLTU branch at [21]
  have hsig : signExtend13 (8 : BitVec 13) = (8 : Word) := by native_decide
  have ha_t : (base + 16) + signExtend13 (8 : BitVec 13) = base + 24 := by rw [hsig]; bv_omega
  have hbltu := bltu_spec_gen .x1 .x5 8 rhat_un1 q_dlo (base + 16)
  rw [ha_t] at hbltu
  -- 3. Frame BLTU with remaining atoms
  have hbltu_framed := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .LD .x1 .x12 3952) **
     ((base + 4) ↦ᵢ .MUL .x5 .x10 .x1) **
     ((base + 8) ↦ᵢ .SLLI .x1 .x7 32) **
     ((base + 12) ↦ᵢ .OR .x1 .x1 .x11) **
     ((base + 20) ↦ᵢ .JAL .x0 12) **
     ((base + 24) ↦ᵢ .ADDI .x10 .x10 4095) **
     ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6) **
     (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
     (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo))
    (by pcFree) hbltu
  -- 4. Compose framed body → framed BLTU into cpsBranch
  have hbranch := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbltu_framed
  -- 5. Case split on condition
  by_cases hcond : BitVec.ult rhat_un1 q_dlo = true
  · -- Taken: BLTU jumps to base+24, correction needed
    simp only [q1', rhat', hcond, ↓reduceIte]
    simp only [hcond] at hbranch
    -- Extract taken path (ntaken absurd: ⌜¬True⌝ → False)
    have h_elim := cpsBranch_elim_taken _ _ _ _ _ _ hbranch (fun hp hQf => by
      obtain ⟨h1, h2, _, _, h1p, _⟩ := hQf
      obtain ⟨_, h1b, _, _, _, h1bp⟩ := h1p
      obtain ⟨_, h1c, _, _, _, h1cp⟩ := h1bp
      exact absurd trivial ((sepConj_pure_right _ _ h1c).1 h1cp).2)
    -- Correction [23-24]: ADDI + ADD from base+24 to base+32
    have ha28 : (base + 24 : Addr) + 4 = base + 28 := by bv_omega
    have ha32c : (base + 24 : Addr) + 8 = base + 32 := by bv_omega
    have hcorr := divK_div128_correct_q1_spec q1 rhat d_hi (base + 24)
    rw [ha28, ha32c] at hcorr
    -- Frame correction with all non-correction atoms
    have hcorr_framed := cpsTriple_frame_left _ _ _ _
      (((base + 16) ↦ᵢ .BLTU .x1 .x5 8) ** (.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo) **
       ⌜True⌝ **
       (base ↦ᵢ .LD .x1 .x12 3952) **
       ((base + 4) ↦ᵢ .MUL .x5 .x10 .x1) **
       ((base + 8) ↦ᵢ .SLLI .x1 .x7 32) **
       ((base + 12) ↦ᵢ .OR .x1 .x1 .x11) **
       ((base + 20) ↦ᵢ .JAL .x0 12) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ un1) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      (by pcFree) hcorr
    -- Compose h_elim → hcorr_framed
    have h_composed := cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) h_elim hcorr_framed
    -- Weaken: rearrange pre, strip ⌜True⌝ and rearrange post
    exact cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        have hp' := sepConj_mono_right
          (sepConj_strip_pure_depth3 _ _ _ _ True) h hp
        xperm_hyp hp')
      h_composed
  · -- Not-taken: fall through to JAL skip at [22]
    have hne : ¬(BitVec.ult rhat_un1 q_dlo = true) := hcond
    have hf : BitVec.ult rhat_un1 q_dlo = false := Bool.eq_false_iff.mpr hne
    simp only [q1', rhat', hf, if_neg (show ¬((false : Bool) = true) from by decide)]
    simp only [hf] at hbranch
    -- Extract ntaken path (taken absurd: ⌜false = true⌝ → False)
    have h_elim := cpsBranch_elim_ntaken _ _ _ _ _ _ hbranch (fun hp hQt => by
      obtain ⟨h1, h2, _, _, h1p, _⟩ := hQt
      obtain ⟨_, h1b, _, _, _, h1bp⟩ := h1p
      obtain ⟨_, h1c, _, _, _, h1cp⟩ := h1bp
      exact absurd ((sepConj_pure_right _ _ h1c).1 h1cp).2 (by decide))
    -- Normalize exit address: base+16+4 → base+20
    have ha20 : (base + 16 : Addr) + 4 = base + 20 := by bv_omega
    rw [ha20] at h_elim
    -- JAL x0 12 at [22]: unconditional jump base+20 → base+32
    have hsig21 : signExtend21 (12 : BitVec 21) = (12 : Word) := by native_decide
    have ha32j : (base + 20 : Addr) + signExtend21 (12 : BitVec 21) = base + 32 := by
      rw [hsig21]; bv_omega
    have hjal := jal_x0_spec_gen (12 : BitVec 21) (base + 20)
    rw [ha32j] at hjal
    -- Frame JAL with all remaining atoms
    have hjal_framed := cpsTriple_frame_left _ _ _ _
      (((base + 16) ↦ᵢ .BLTU .x1 .x5 8) ** (.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo) **
       ⌜¬(false = true)⌝ **
       (base ↦ᵢ .LD .x1 .x12 3952) **
       ((base + 4) ↦ᵢ .MUL .x5 .x10 .x1) **
       ((base + 8) ↦ᵢ .SLLI .x1 .x7 32) **
       ((base + 12) ↦ᵢ .OR .x1 .x1 .x11) **
       ((base + 24) ↦ᵢ .ADDI .x10 .x10 4095) **
       ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6) **
       (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo))
      (by pcFree) hjal
    -- Compose h_elim → hjal_framed
    have h_composed := cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) h_elim hjal_framed
    -- Weaken: rearrange pre, strip ⌜¬(false = true)⌝ and rearrange post
    exact cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        have hp' := sepConj_mono_right
          (sepConj_strip_pure_depth3 _ _ _ _ (¬(false = true))) h hp
        xperm_hyp hp')
      h_composed

end EvmAsm.Rv64
