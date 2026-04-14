/-
  EvmAsm.Evm64.DivModSpec

  CPS specifications for the 256-bit EVM DIV and MOD programs (Knuth Algorithm D).
  Bottom-up decomposition starting from the simplest phases.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Zero path: b = 0, push 0. 5 instructions.
-- ============================================================================

abbrev divK_zeroPath_code (base : Word) : CodeReq :=
  CodeReq.ofProg base divK_zeroPath

/-- Zero path: advance sp by 32, store four zeros at the output location.
    Used when b = 0 (both DIV and MOD return 0). -/
theorem divK_zeroPath_spec (sp : Word) (base : Word)
    (m32 m40 m48 m56 : Word)
    (hvalid : ValidMemRange sp 8) :
    let cr := divK_zeroPath_code base
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) **
       ((sp + 32) ↦ₘ m32) ** ((sp + 40) ↦ₘ m40) **
       ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56))
      ((.x12 ↦ᵣ (sp + 32)) **
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

abbrev divK_phaseA_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseA 1016)

/-- Phase A body: load and OR-reduce the 4 limbs of b.
    Produces x5 = b0 ||| b1 ||| b2 ||| b3.
    The BEQ instruction at base+28 and x0 are preserved for branch composition. -/
theorem divK_phaseA_body_spec (sp : Word) (base : Word)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hvalid : ValidMemRange sp 8) :
    let cr := divK_phaseA_code base
    cpsTriple base (base + 28) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 b0 32 base (by nofun) (by validMem)
  have I1 := ld_spec_gen .x10 .x12 sp v10 b1 40 (base + 4) (by nofun) (by validMem)
  have I2 := or_spec_gen_rd_eq_rs1 .x5 .x10 b0 b1 (base + 8) (by nofun)
  have I3 := ld_spec_gen .x10 .x12 sp b1 b2 48 (base + 12) (by nofun) (by validMem)
  have I4 := or_spec_gen_rd_eq_rs1 .x5 .x10 (b0 ||| b1) b2 (base + 16) (by nofun)
  have I5 := ld_spec_gen .x10 .x12 sp b2 b3 56 (base + 20) (by nofun) (by validMem)
  have I6 := or_spec_gen_rd_eq_rs1 .x5 .x10 (b0 ||| b1 ||| b2) b3 (base + 24) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5 I6

-- ============================================================================
-- Phase A: full cpsBranch (body + BEQ)
-- ============================================================================

/-- Phase A: OR-reduce b then BEQ to zero path. -/
theorem divK_phaseA_spec (sp : Word) (base : Word)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hvalid : ValidMemRange sp 8) :
    let bor := b0 ||| b1 ||| b2 ||| b3
    let cr := divK_phaseA_code base
    let post :=
      (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ bor) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
      ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)
    cpsBranch base cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      -- Taken: bor = 0
      ((base + 28) + signExtend13 1016) post
      -- Not taken: bor ≠ 0
      (base + 32) post := by
  intro bor cr post
  -- 1. Body: 7 straight-line instructions
  have hbody := divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10 hvalid
  -- 2. BEQ: branch at base + 28, drop pure facts
  have hbeq_raw := beq_spec_gen .x5 .x0 1016 bor (0 : Word) (base + 28)
  have ha1 : (base + 28 : Word) + 4 = base + 32 := by bv_addr
  rw [ha1] at hbeq_raw
  have hbeq := cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
    (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
    hbeq_raw
  -- 3. Frame BEQ with remaining registers and memory
  have hbeq_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  -- 4. Extend BEQ branch to full cr (singleton ⊆ full code)
  have hbeq_ext := cpsBranch_extend_code (cr' := cr) (fun a i h => by
    simp only [CodeReq.singleton] at h
    split at h <;> simp_all only [Option.some.injEq, beq_iff_eq, reduceCtorEq]
    -- a = base + 28, i = .BEQ .x5 .x0 1016
    subst_vars
    show divK_phaseA_code base (base + 28) = _
    exact CodeReq.ofProg_lookup base (divK_phaseA 1016) 7
      (by decide) (by decide)
    ) hbeq_framed
  -- 5. Compose body → BEQ with permutation (same CR)
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_ext
  -- 6. Final permutation of postconditions
  exact cpsBranch_consequence _ _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed
-- ============================================================================
-- Phase B init: zero out q[0..3] and u[5..7], load b[1] and b[2].
-- 9 straight-line instructions.
-- ============================================================================

abbrev divK_phaseB_init1_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseB.take 7)

/-- Phase B init part 1: zero scratch q[0..3] and u[5..7]. 7 instructions. -/
theorem divK_phaseB_init1_spec (sp : Word) (base : Word)
    (q0 q1 q2 q3 u5 u6 u7 : Word)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true) :
    let cr := divK_phaseB_init1_code base
    cpsTriple base (base + 28) cr
      (
       (.x12 ↦ᵣ sp) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7))
      (
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

abbrev divK_phaseB_init2_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseB.drop 7 |>.take 2)

/-- Phase B init part 2: load b[1] and b[2]. 2 instructions. -/
theorem divK_phaseB_init2_spec (sp : Word) (base : Word)
    (b1 b2 : Word) (v6 v7 : Word)
    (hvalid : ValidMemRange sp 8) :
    let cr := divK_phaseB_init2_code base
    cpsTriple base (base + 8) cr
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2))
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2)) := by
  have I0 := ld_spec_gen .x6 .x12 sp v6 b1 40 base (by nofun) (by validMem)
  have I1 := ld_spec_gen .x7 .x12 sp v7 b2 48 (base + 4) (by nofun) (by validMem)
  runBlock I0 I1

-- ============================================================================
-- Phase C4: Copy a → u[0..4] unshifted (shift = 0). 9 instructions.
-- ============================================================================

abbrev divK_copyAU_code (base : Word) : CodeReq :=
  CodeReq.ofProg base divK_copyAU

/-- Copy a[0..3] to u[0..3] and set u[4] = 0 (no shift needed). -/
theorem divK_copyAU_spec (sp : Word) (base : Word)
    (a0 a1 a2 a3 u0 u1 u2 u3 u4 : Word) (v5 : Word)
    (hvalid : ValidMemRange sp 8)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true) :
    let cr := divK_copyAU_code base
    cpsTriple base (base + 36) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u4))
      (
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

def divK_normB_merge_prog (high_off low_off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 high_off, .LD .x7 .x12 low_off, .SLL .x5 .x5 .x6,
   .SRL .x7 .x7 .x2, .OR .x5 .x5 .x7, .SD .x12 .x5 high_off]

abbrev divK_normB_merge_code (high_off low_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normB_merge_prog high_off low_off)

/-- NormB merge limb (6 instructions): LD high, LD low, SLL, SRL, OR, SD.
    Computes result = (high <<< shift) ||| (low >>> anti_shift) and stores to high_off.
    x6 = shift, x2 = anti_shift (= 64 - shift as unsigned). -/
theorem divK_normB_merge_spec (high_off low_off : BitVec 12)
    (sp high low v5 v7 shift anti_shift : Word) (base : Word)
    (hvalid_high : isValidDwordAccess (sp + signExtend12 high_off) = true)
    (hvalid_low : isValidDwordAccess (sp + signExtend12 low_off) = true) :
    let shifted_high := high <<< (shift.toNat % 64)
    let shifted_low := low >>> (anti_shift.toNat % 64)
    let result := shifted_high ||| shifted_low
    let cr := divK_normB_merge_code high_off low_off base
    cpsTriple base (base + 24) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 high_off) ↦ₘ high) **
       ((sp + signExtend12 low_off) ↦ₘ low))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x7 ↦ᵣ shifted_low) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 high_off) ↦ₘ result) **
       ((sp + signExtend12 low_off) ↦ₘ low)) := by
  intro shifted_high shifted_low result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 high high_off base (by nofun) hvalid_high
  have I1 := ld_spec_gen .x7 .x12 sp v7 low low_off (base + 4) (by nofun) hvalid_low
  have I2 := sll_spec_gen_rd_eq_rs1 .x5 .x6 high shift (base + 8) (by nofun)
  have I3 := srl_spec_gen_rd_eq_rs1 .x7 .x2 low anti_shift (base + 12) (by nofun)
  have I4 := or_spec_gen_rd_eq_rs1 .x5 .x7 shifted_high shifted_low (base + 16) (by nofun)
  have I5 := sd_spec_gen .x12 .x5 sp result high high_off (base + 20) hvalid_high
  runBlock I0 I1 I2 I3 I4 I5

def divK_normB_last_prog (off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 off, .SLL .x5 .x5 .x6, .SD .x12 .x5 off]

abbrev divK_normB_last_code (off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normB_last_prog off)

/-- NormB last limb (3 instructions): LD, SLL, SD.
    Computes result = val <<< shift and stores to off. -/
theorem divK_normB_last_spec (off : BitVec 12)
    (sp val v5 shift : Word) (base : Word)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let result := val <<< (shift.toNat % 64)
    let cr := divK_normB_last_code off base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ val))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ result)) := by
  intro result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 val off base (by nofun) hvalid
  have I1 := sll_spec_gen_rd_eq_rs1 .x5 .x6 val shift (base + 4) (by nofun)
  have I2 := sd_spec_gen .x12 .x5 sp result val off (base + 8) hvalid
  runBlock I0 I1 I2

-- ============================================================================
-- NormA: Normalize a → u[0..4] (shift > 0). 20 instructions (excl. JAL).
-- Per-limb decomposition: top (3 instr) + 3 merge (5 instr each) + last (2 instr).
-- ============================================================================

def divK_normA_top_prog (src_off dst_off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 src_off, .SRL .x7 .x5 .x2, .SD .x12 .x7 dst_off]

abbrev divK_normA_top_code (src_off dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normA_top_prog src_off dst_off)

/-- NormA top: LD a[3], SRL to x7, SD u[4]. 3 instructions.
    Computes u[4] = a[3] >>> anti_shift (overflow bits from top limb). -/
theorem divK_normA_top_spec (src_off dst_off : BitVec 12)
    (sp val v5 v7 anti_shift dst_old : Word) (base : Word)
    (hvalid_src : isValidDwordAccess (sp + signExtend12 src_off) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let result := val >>> (anti_shift.toNat % 64)
    let cr := divK_normA_top_code src_off dst_off base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 src_off) ↦ₘ val) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ val) ** (.x7 ↦ᵣ result) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 src_off) ↦ₘ val) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 val src_off base (by nofun) hvalid_src
  have I1 := srl_spec_gen .x7 .x5 .x2 v7 val anti_shift (base + 4) (by nofun)
  have I2 := sd_spec_gen .x12 .x7 sp result dst_old dst_off (base + 8) hvalid_dst
  runBlock I0 I1 I2

def divK_normA_mergeA_prog (next_off dst_off : BitVec 12) : List Instr :=
  [.LD .x7 .x12 next_off, .SLL .x5 .x5 .x6, .SRL .x10 .x7 .x2,
   .OR .x5 .x5 .x10, .SD .x12 .x5 dst_off]

abbrev divK_normA_mergeA_code (next_off dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normA_mergeA_prog next_off dst_off)

/-- NormA merge type A (5 instructions): x5 holds current limb.
    LD next into x7, SLL x5 by shift, SRL x10 from x7 by anti_shift, OR into x5, SD.
    Used for u[3] and u[1] computation. -/
theorem divK_normA_mergeA_spec (next_off dst_off : BitVec 12)
    (sp current next v7 v10 shift anti_shift dst_old : Word) (base : Word)
    (hvalid_next : isValidDwordAccess (sp + signExtend12 next_off) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let shifted_curr := current <<< (shift.toNat % 64)
    let shifted_next := next >>> (anti_shift.toNat % 64)
    let result := shifted_curr ||| shifted_next
    let cr := divK_normA_mergeA_code next_off dst_off base
    cpsTriple base (base + 20) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ current) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x7 ↦ᵣ next) ** (.x10 ↦ᵣ shifted_next) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro shifted_curr shifted_next result cr
  have I0 := ld_spec_gen .x7 .x12 sp v7 next next_off base (by nofun) hvalid_next
  have I1 := sll_spec_gen_rd_eq_rs1 .x5 .x6 current shift (base + 4) (by nofun)
  have I2 := srl_spec_gen .x10 .x7 .x2 v10 next anti_shift (base + 8) (by nofun)
  have I3 := or_spec_gen_rd_eq_rs1 .x5 .x10 shifted_curr shifted_next (base + 12) (by nofun)
  have I4 := sd_spec_gen .x12 .x5 sp result dst_old dst_off (base + 16) hvalid_dst
  runBlock I0 I1 I2 I3 I4

def divK_normA_mergeB_prog (next_off dst_off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 next_off, .SLL .x7 .x7 .x6, .SRL .x10 .x5 .x2,
   .OR .x7 .x7 .x10, .SD .x12 .x7 dst_off]

abbrev divK_normA_mergeB_code (next_off dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normA_mergeB_prog next_off dst_off)

/-- NormA merge type B (5 instructions): x7 holds current limb.
    LD next into x5, SLL x7 by shift, SRL x10 from x5 by anti_shift, OR into x7, SD.
    Used for u[2] computation. -/
theorem divK_normA_mergeB_spec (next_off dst_off : BitVec 12)
    (sp current next v5 v10 shift anti_shift dst_old : Word) (base : Word)
    (hvalid_next : isValidDwordAccess (sp + signExtend12 next_off) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let shifted_curr := current <<< (shift.toNat % 64)
    let shifted_next := next >>> (anti_shift.toNat % 64)
    let result := shifted_curr ||| shifted_next
    let cr := divK_normA_mergeB_code next_off dst_off base
    cpsTriple base (base + 20) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ current) ** (.x10 ↦ᵣ v10) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ next) ** (.x7 ↦ᵣ result) ** (.x10 ↦ᵣ shifted_next) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 next_off) ↦ₘ next) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro shifted_curr shifted_next result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 next next_off base (by nofun) hvalid_next
  have I1 := sll_spec_gen_rd_eq_rs1 .x7 .x6 current shift (base + 4) (by nofun)
  have I2 := srl_spec_gen .x10 .x5 .x2 v10 next anti_shift (base + 8) (by nofun)
  have I3 := or_spec_gen_rd_eq_rs1 .x7 .x10 shifted_curr shifted_next (base + 12) (by nofun)
  have I4 := sd_spec_gen .x12 .x7 sp result dst_old dst_off (base + 16) hvalid_dst
  runBlock I0 I1 I2 I3 I4

def divK_normA_last_prog (dst_off : BitVec 12) : List Instr :=
  [.SLL .x7 .x7 .x6, .SD .x12 .x7 dst_off]

abbrev divK_normA_last_code (dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_normA_last_prog dst_off)

/-- NormA last limb (2 instructions): SLL x7 by shift, SD to dst_off.
    Computes u[0] = a[0] <<< shift. -/
theorem divK_normA_last_spec (dst_off : BitVec 12)
    (sp val shift dst_old : Word) (base : Word)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let result := val <<< (shift.toNat % 64)
    let cr := divK_normA_last_code dst_off base
    cpsTriple base (base + 8) cr
      (
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ val) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 dst_off) ↦ₘ dst_old))
      (
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 dst_off) ↦ₘ result)) := by
  intro result cr
  have I0 := sll_spec_gen_rd_eq_rs1 .x7 .x6 val shift base (by nofun)
  have I1 := sd_spec_gen .x12 .x7 sp result dst_old dst_off (base + 4) hvalid_dst
  runBlock I0 I1

-- ============================================================================
-- Denorm: De-normalize remainder. Per-limb specs for the shift body.
-- Same structure as NormB but SRL/SLL swapped (right-shift with merge from above).
-- ============================================================================

def divK_denorm_merge_prog (curr_off next_off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 curr_off, .LD .x7 .x12 next_off, .SRL .x5 .x5 .x6,
   .SLL .x7 .x7 .x2, .OR .x5 .x5 .x7, .SD .x12 .x5 curr_off]

abbrev divK_denorm_merge_code (curr_off next_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_denorm_merge_prog curr_off next_off)

/-- Denorm merge limb (6 instructions): LD curr, LD next, SRL, SLL, OR, SD.
    Computes result = (curr >>> shift) ||| (next <<< anti_shift) and stores to curr_off.
    x6 = shift, x2 = anti_shift. -/
theorem divK_denorm_merge_spec (curr_off next_off : BitVec 12)
    (sp curr next v5 v7 shift anti_shift : Word) (base : Word)
    (hvalid_curr : isValidDwordAccess (sp + signExtend12 curr_off) = true)
    (hvalid_next : isValidDwordAccess (sp + signExtend12 next_off) = true) :
    let shifted_curr := curr >>> (shift.toNat % 64)
    let shifted_next := next <<< (anti_shift.toNat % 64)
    let result := shifted_curr ||| shifted_next
    let cr := divK_denorm_merge_code curr_off next_off base
    cpsTriple base (base + 24) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 curr_off) ↦ₘ curr) **
       ((sp + signExtend12 next_off) ↦ₘ next))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x7 ↦ᵣ shifted_next) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + signExtend12 curr_off) ↦ₘ result) **
       ((sp + signExtend12 next_off) ↦ₘ next)) := by
  intro shifted_curr shifted_next result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 curr curr_off base (by nofun) hvalid_curr
  have I1 := ld_spec_gen .x7 .x12 sp v7 next next_off (base + 4) (by nofun) hvalid_next
  have I2 := srl_spec_gen_rd_eq_rs1 .x5 .x6 curr shift (base + 8) (by nofun)
  have I3 := sll_spec_gen_rd_eq_rs1 .x7 .x2 next anti_shift (base + 12) (by nofun)
  have I4 := or_spec_gen_rd_eq_rs1 .x5 .x7 shifted_curr shifted_next (base + 16) (by nofun)
  have I5 := sd_spec_gen .x12 .x5 sp result curr curr_off (base + 20) hvalid_curr
  runBlock I0 I1 I2 I3 I4 I5

def divK_denorm_last_prog (off : BitVec 12) : List Instr :=
  [.LD .x5 .x12 off, .SRL .x5 .x5 .x6, .SD .x12 .x5 off]

abbrev divK_denorm_last_code (off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_denorm_last_prog off)

/-- Denorm last limb (3 instructions): LD, SRL, SD.
    Computes result = val >>> shift and stores to off. -/
theorem divK_denorm_last_spec (off : BitVec 12)
    (sp val v5 shift : Word) (base : Word)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let result := val >>> (shift.toNat % 64)
    let cr := divK_denorm_last_code off base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ val))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift) **
       ((sp + signExtend12 off) ↦ₘ result)) := by
  intro result cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 val off base (by nofun) hvalid
  have I1 := srl_spec_gen_rd_eq_rs1 .x5 .x6 val shift (base + 4) (by nofun)
  have I2 := sd_spec_gen .x12 .x5 sp result val off (base + 8) hvalid
  runBlock I0 I1 I2

-- ============================================================================
-- Epilogue: Copy q[0..3] or u[0..3] to output. 10 instructions each.
-- Split into load phase (4 LD) + store phase (ADDI + 4 SD) + JAL.
-- ============================================================================

def divK_epilogue_load_prog (off0 off1 off2 off3 : BitVec 12) : List Instr :=
  [.LD .x5 .x12 off0, .LD .x6 .x12 off1, .LD .x7 .x12 off2, .LD .x10 .x12 off3]

abbrev divK_epilogue_load_code (off0 off1 off2 off3 : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_epilogue_load_prog off0 off1 off2 off3)

/-- Epilogue load phase: load 4 values from scratch space. 4 instructions.
    Loads q[0..3] (for DIV) or u[0..3] (for MOD) into x5, x6, x7, x10. -/
theorem divK_epilogue_load_spec (off0 off1 off2 off3 : BitVec 12)
    (sp r0 r1 r2 r3 v5 v6 v7 v10 : Word) (base : Word)
    (hv0 : isValidDwordAccess (sp + signExtend12 off0) = true)
    (hv1 : isValidDwordAccess (sp + signExtend12 off1) = true)
    (hv2 : isValidDwordAccess (sp + signExtend12 off2) = true)
    (hv3 : isValidDwordAccess (sp + signExtend12 off3) = true) :
    let cr := divK_epilogue_load_code off0 off1 off2 off3 base
    cpsTriple base (base + 16) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 off0) ↦ₘ r0) ** ((sp + signExtend12 off1) ↦ₘ r1) **
       ((sp + signExtend12 off2) ↦ₘ r2) ** ((sp + signExtend12 off3) ↦ₘ r3))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r0) ** (.x6 ↦ᵣ r1) ** (.x7 ↦ᵣ r2) ** (.x10 ↦ᵣ r3) **
       ((sp + signExtend12 off0) ↦ₘ r0) ** ((sp + signExtend12 off1) ↦ₘ r1) **
       ((sp + signExtend12 off2) ↦ₘ r2) ** ((sp + signExtend12 off3) ↦ₘ r3)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 r0 off0 base (by nofun) hv0
  have I1 := ld_spec_gen .x6 .x12 sp v6 r1 off1 (base + 4) (by nofun) hv1
  have I2 := ld_spec_gen .x7 .x12 sp v7 r2 off2 (base + 8) (by nofun) hv2
  have I3 := ld_spec_gen .x10 .x12 sp v10 r3 off3 (base + 12) (by nofun) hv3
  runBlock I0 I1 I2 I3

def divK_epilogue_store_prog (jal_off : BitVec 21) : List Instr :=
  [.ADDI .x12 .x12 32, .SD .x12 .x5 0, .SD .x12 .x6 8,
   .SD .x12 .x7 16, .SD .x12 .x10 24, .JAL .x0 jal_off]

abbrev divK_epilogue_store_code (jal_off : BitVec 21) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_epilogue_store_prog jal_off)

/-- Epilogue store phase: ADDI sp+32, store 4 values, JAL to exit. 6 instructions. -/
theorem divK_epilogue_store_spec (sp : Word) (base : Word)
    (r0 r1 r2 r3 m0 m8 m16 m24 : Word) (jal_off : BitVec 21)
    (hvalid : ValidMemRange sp 8) :
    let cr := divK_epilogue_store_code jal_off base
    cpsTriple base (base + 20 + signExtend21 jal_off) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r0) ** (.x6 ↦ᵣ r1) ** (.x7 ↦ᵣ r2) ** (.x10 ↦ᵣ r3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (
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

abbrev divK_phaseB_tail_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseB.drop 16)

/-- Phase B tail: store n to scratch, compute sp + (n-1)*8, load b[n-1].
    x5 = n on entry. On exit, x5 = leading limb b[n-1]. -/
theorem divK_phaseB_tail_spec (sp n leading_limb n_mem : Word) (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_limb : isValidDwordAccess
      ((sp + ((n + signExtend12 4095) <<< (3 : BitVec 6).toNat)) + signExtend12 32) = true) :
    let nm1 := n + signExtend12 4095
    let nm1_x8 := nm1 <<< (3 : BitVec 6).toNat
    let addr_lead := sp + nm1_x8
    let cr := divK_phaseB_tail_code base
    cpsTriple base (base + 20) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
       ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((addr_lead + signExtend12 32) ↦ₘ leading_limb))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ leading_limb) **
       ((sp + signExtend12 3984) ↦ₘ n) **
       ((addr_lead + signExtend12 32) ↦ₘ leading_limb)) := by
  intro nm1 nm1_x8 addr_lead cr
  have I0 := sd_spec_gen .x12 .x5 sp n n_mem 3984 base hv_n
  have I1 := addi_spec_gen_same .x5 n 4095 (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x5 nm1 3 (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs2 .x5 .x12 sp nm1_x8 (base + 12) (by nofun)
  have I4 := ld_spec_gen_same .x5 addr_lead leading_limb 32 (base + 16) (by nofun) hv_limb
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Phase C2 body: store shift, compute anti_shift. 3 instructions.
-- ============================================================================

abbrev divK_phaseC2_code (shift0_off : BitVec 13) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseC2 shift0_off)

/-- Phase C2 body: SD shift to scratch, ADDI x2 = 0, SUB x2 = -shift.
    Preserves x6 and x0 for the subsequent BEQ.
    The postcondition uses `signExtend12 (0 : BitVec 12) - shift` (= 0 - shift)
    to match the syntactic form produced by addi_x0_spec_gen + sub_spec_gen. -/
theorem divK_phaseC2_body_spec (sp shift v2 shift_mem : Word)
    (shift0_off : BitVec 13) (base : Word)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true) :
    let cr := divK_phaseC2_code shift0_off base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem))
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  intro cr
  have I0 := sd_spec_gen .x12 .x6 sp shift shift_mem 3992 base hv_shift
  have I1 := addi_x0_spec_gen .x2 v2 0 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x2 .x6
    (signExtend12 (0 : BitVec 12)) shift (base + 8) (by nofun)
  runBlock I0 I1 I2

-- ============================================================================
-- Phase C2 full: body + BEQ (shift = 0 branch). cpsBranch.
-- ============================================================================

set_option maxRecDepth 1024 in
/-- Phase C2: store shift, compute anti_shift, BEQ if shift=0.
    Taken: shift = 0, skip normalization.
    Not taken: shift ≠ 0, proceed to normalize.
    anti_shift = signExtend12 0 - shift (= 0 - shift = negation of shift amount). -/
theorem divK_phaseC2_spec (sp shift v2 shift_mem : Word)
    (shift0_off : BitVec 13) (base : Word)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true) :
    let cr := divK_phaseC2_code shift0_off base
    let post :=
      (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) **
      (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp + signExtend12 3992) ↦ₘ shift)
    cpsBranch base cr
      (
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem))
      -- Taken: shift = 0
      ((base + 12) + signExtend13 shift0_off) post
      -- Not taken: shift ≠ 0
      (base + 16) post := by
  intro cr post
  have hbody := divK_phaseC2_body_spec sp shift v2 shift_mem shift0_off base hv_shift
  have hbeq_raw := beq_spec_gen .x6 .x0 shift0_off shift (0 : Word) (base + 12)
  have ha1 : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  rw [ha1] at hbeq_raw
  have hbeq : cpsBranch (base + 12) _
      ((.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 12) + signExtend13 shift0_off)
        ((.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 16)
        ((.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      hbeq_raw
  have hbeq_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hbeq_ext := cpsBranch_extend_code (cr' := cr) (fun a i h => by
    simp only [CodeReq.singleton] at h
    split at h
    · next heq =>
      rw [beq_iff_eq] at heq; subst heq
      simp only [Option.some.injEq] at h; subst h
      show divK_phaseC2_code shift0_off base (base + 12) = _
      have hlen : (divK_phaseC2 shift0_off).length = 4 := by
        unfold divK_phaseC2 SD ADDI single seq; rfl
      exact CodeReq.ofProg_lookup base (divK_phaseC2 shift0_off) 3
        (by omega) (by omega)
    · simp at h) hbeq_framed
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_ext
  exact cpsBranch_consequence _ _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed
-- ============================================================================
-- Phase B cascade step: ADDI x5 n_val + BNE rx x0 offset. cpsBranch.
-- Used for each "if b[k]≠0 → n=k" step in the n-computation cascade.
-- ============================================================================

abbrev divK_phaseB_cascade_step_code (n_val : BitVec 12) (rx : Reg) (bne_off : BitVec 13)
    (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x5 .x0 n_val))
   (CodeReq.singleton (base + 4) (.BNE rx .x0 bne_off))

/-- Single cascade step: load n_val into x5, then BNE on rx vs x0.
    Taken: rx ≠ 0 (limb is nonzero), branch to target with x5 = n_val.
    Not taken: rx = 0, fall through with x5 = n_val. -/
theorem divK_phaseB_cascade_step_spec (n_val : BitVec 12) (rx : Reg) (check v5 : Word)
    (bne_off : BitVec 13) (base : Word) :
    let n := (0 : Word) + signExtend12 n_val
    let cr := divK_phaseB_cascade_step_code n_val rx bne_off base
    let post :=
      (.x5 ↦ᵣ n) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check)
    cpsBranch base cr
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check))
      -- Taken: check ≠ 0
      ((base + 4) + signExtend13 bne_off) post
      -- Not taken: check = 0
      (base + 8) post := by
  intro n cr post
  -- 1. ADDI body
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check))
      ((.x5 ↦ᵣ n) ** (.x0 ↦ᵣ (0 : Word)) ** (rx ↦ᵣ check)) := by
    have I0 := addi_spec_gen .x5 .x0 v5 (0 : Word) n_val base (by nofun)
    runBlock I0
  -- 2. BNE at base + 4, drop pure facts
  have hbne_raw := bne_spec_gen rx .x0 bne_off check (0 : Word) (base + 4)
  have ha1 : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha1] at hbne_raw
  have hbne : cpsBranch (base + 4) _
      ((rx ↦ᵣ check) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 4) + signExtend13 bne_off)
        ((rx ↦ᵣ check) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 8)
        ((rx ↦ᵣ check) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      hbne_raw
  -- 3. Frame BNE with x5
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    (.x5 ↦ᵣ n)
    (by pcFree) hbne
  -- 4. Extend to full cr
  have hbne_ext := cpsBranch_extend_code (cr' := cr) (fun a i h => by
    simp only [CodeReq.singleton] at h
    split at h
    · next heq =>
      rw [beq_iff_eq] at heq; subst heq
      simp only [Option.some.injEq] at h; subst h
      show divK_phaseB_cascade_step_code n_val rx bne_off base (base + 4) = _
      simp only [divK_phaseB_cascade_step_code, CodeReq.union, CodeReq.singleton]
      have h0 : ¬(base + 4 = base) := by bv_omega
      simp only [beq_iff_eq, h0, ↓reduceIte]
    · simp at h) hbne_framed
  -- 5. Compose
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  exact cpsBranch_consequence _ _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed
-- ============================================================================
-- Loop setup: LD n, compute m = 4 - n, BLT to skip loop.
-- 4 instructions: LD, ADDI, SUB, BLT. cpsBranch.
-- ============================================================================

abbrev divK_loopSetup_code (blt_off : BitVec 13) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_loopSetup blt_off)

/-- Loop setup body: load n, compute m = 4 - n. 3 straight-line instructions.
    Uses signExtend12 4 directly to match addi_x0_spec_gen + sub_spec_gen output. -/
theorem divK_loopSetup_body_spec (sp n v1 v5 : Word)
    (blt_off : BitVec 13) (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true) :
    let cr := divK_loopSetup_code blt_off base
    cpsTriple base (base + 12) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
       (.x1 ↦ᵣ (signExtend12 (4 : BitVec 12) - n)) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n)) := by
  intro cr
  have I0 := ld_spec_gen .x5 .x12 sp v5 n 3984 base (by nofun) hv_n
  have I1 := addi_x0_spec_gen .x1 v1 4 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x1 .x5
    (signExtend12 (4 : BitVec 12)) n (base + 8) (by nofun)
  runBlock I0 I1 I2

/-- Loop setup: load n, compute m = 4-n, BLT if m < 0 (skip loop).
    Taken: m < 0 (n > 4, impossible in practice but handled).
    Not taken: m >= 0, proceed to loop. -/
theorem divK_loopSetup_spec (sp n v1 v5 : Word)
    (blt_off : BitVec 13) (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true) :
    let m := signExtend12 (4 : BitVec 12) - n
    let cr := divK_loopSetup_code blt_off base
    let post :=
      (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** (.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp + signExtend12 3984) ↦ₘ n)
    cpsBranch base cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      -- Taken: m < 0 (signed)
      ((base + 12) + signExtend13 blt_off) post
      -- Not taken: m >= 0
      (base + 16) post := by
  intro m cr post
  have hbody := divK_loopSetup_body_spec sp n v1 v5 blt_off base hv_n
  have hblt_raw := blt_spec_gen .x1 .x0 blt_off m (0 : Word) (base + 12)
  have ha1 : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  rw [ha1] at hblt_raw
  have hblt : cpsBranch (base + 12) _
      ((.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)))
      ((base + 12) + signExtend13 blt_off)
        ((.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 16)
        ((.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      hblt_raw
  have hblt_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
     ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hblt
  have hblt_ext := cpsBranch_extend_code (cr' := cr) (fun a i h => by
    simp only [CodeReq.singleton] at h
    split at h
    · next heq =>
      rw [beq_iff_eq] at heq; subst heq
      simp only [Option.some.injEq] at h; subst h
      show divK_loopSetup_code blt_off base (base + 12) = _
      have hlen : (divK_loopSetup blt_off).length = 4 := by
        unfold divK_loopSetup LD ADDI single seq; rfl
      exact CodeReq.ofProg_lookup base (divK_loopSetup blt_off) 3
        (by omega) (by omega)
    · simp at h) hblt_framed
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hblt_ext
  exact cpsBranch_consequence _ _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed
-- ============================================================================
-- CLZ init: ADDI x6 x0 0. 1 instruction.
-- ============================================================================

/-- CLZ init: set x6 = 0 (count register). -/
theorem divK_clz_init_spec (v6 : Word) (base : Word) :
    let cr := CodeReq.singleton base (.ADDI .x6 .x0 0)
    cpsTriple base (base + 4) cr
      ((.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ signExtend12 (0 : BitVec 12)) **
       (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  have I0 := addi_x0_spec_gen .x6 v6 0 base (by nofun)
  runBlock I0
-- ============================================================================
-- CLZ per-stage specs: SRLI x7 x5 K + BNE x7 x0 12 + SLLI x5 x5 M + ADDI x6 x6 M.
-- Two specs per stage: taken (shifted ≠ 0) and not-taken (shifted = 0).
-- Uses cpsBranch_elim_taken/ntaken to extract deterministic paths.
-- K : BitVec 6 (SRLI shamt), M_s : BitVec 6 (SLLI shamt), M_a : BitVec 12 (ADDI imm).
-- ============================================================================

def divK_clz_stage_prog (K M_s : BitVec 6) (M_a : BitVec 12) : List Instr :=
  [.SRLI .x7 .x5 K, .BNE .x7 .x0 12, .SLLI .x5 .x5 M_s, .ADDI .x6 .x6 M_a]

abbrev divK_clz_stage_code (K M_s : BitVec 6) (M_a : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_clz_stage_prog K M_s M_a)

/-- CLZ stage, taken branch: val >>> K ≠ 0, skip SLLI+ADDI.
    x5 = val (unchanged), x6 = count (unchanged), x7 = val >>> K. -/
theorem divK_clz_stage_taken_spec (K M_s : BitVec 6) (M_a : BitVec 12) (val count v7 : Word)
    (base : Word)
    (hne : val >>> K.toNat ≠ 0) :
    let cr := divK_clz_stage_code K M_s M_a base
    cpsTriple base (base + 16) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) **
              (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  -- 1. SRLI body
  have I0 := srli_spec_gen .x7 .x5 v7 val K base (by nofun)
  -- 2. BNE at base+4: taken → base+16
  have hbne_raw := bne_spec_gen .x7 .x0 (12 : BitVec 13) (val >>> K.toNat) (0 : Word) (base + 4)
  have hsig : signExtend13 (12 : BitVec 13) = (12 : Word) := by decide
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbne_raw
  -- 3. Frame BNE with x5, x6
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  -- 4. Extend to full cr
  have hbne_ext : cpsBranch (base + 4) cr
      (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 16)
        (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> K.toNat ≠ 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 8)
        (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> K.toNat = 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))) :=
    fun R hR s hcr hPR hpc =>
      hbne_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show divK_clz_stage_code K M_s M_a base (base + 4) = _
        simp only [divK_clz_stage_code, divK_clz_stage_prog,
          CodeReq.ofProg_cons, CodeReq.ofProg_nil,
          CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  -- 5. SRLI body
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  -- 6. Compose SRLI → BNE
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  -- 7. Eliminate not-taken path (contradicts hne)
  have taken := cpsBranch_elim_taken _ _ _ _ _ _ _ composed (fun hp hQf => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
    exact hne ((sepConj_pure_right _ _ _).1 h_x0p).2)
  -- 8. Strip pure fact from taken postcondition, then permute
  -- taken postcondition: ((x7 ** x0 ** pure) ** (x5 ** x6))
  -- target postcondition: (x5 ** x6 ** x7 ** x0)
  -- Need intermediate: first strip pure, then xperm
  -- Use direct definition to avoid lambda wrapping
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := taken R hR s hcr hPR hpc
  exact ⟨k, s', hstep, hpc', by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
      xperm_hyp hp') hp hpq⟩⟩
/-- CLZ stage, not-taken branch: val >>> K = 0, execute SLLI+ADDI.
    x5 = val <<< M, x6 = count + signExtend12 M, x7 = 0. -/
theorem divK_clz_stage_ntaken_spec (K M_s : BitVec 6) (M_a : BitVec 12) (val count v7 : Word)
    (base : Word)
    (heq : val >>> K.toNat = 0) :
    let cr := divK_clz_stage_code K M_s M_a base
    cpsTriple base (base + 16) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (val <<< M_s.toNat)) ** (.x6 ↦ᵣ (count + signExtend12 M_a)) **
              (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  -- 1. SRLI body
  have I0 := srli_spec_gen .x7 .x5 v7 val K base (by nofun)
  -- 2. BNE at base+4
  have hbne_raw := bne_spec_gen .x7 .x0 (12 : BitVec 13) (val >>> K.toNat) (0 : Word) (base + 4)
  have hsig : signExtend13 (12 : BitVec 13) = (12 : Word) := by decide
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbne_raw
  -- 3. Frame BNE with x5, x6
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  -- 4. Extend BNE to full cr
  have hbne_ext : cpsBranch (base + 4) cr
      (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 16)
        (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> K.toNat ≠ 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 8)
        (((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> K.toNat = 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))) :=
    fun R hR s hcr hPR hpc =>
      hbne_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show divK_clz_stage_code K M_s M_a base (base + 4) = _
        simp only [divK_clz_stage_code, divK_clz_stage_prog,
          CodeReq.ofProg_cons, CodeReq.ofProg_nil,
          CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  -- 5. SRLI body
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  -- 6. Compose SRLI → BNE
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  -- 7. Eliminate taken path (contradicts heq)
  have ntaken := cpsBranch_elim_ntaken _ _ _ _ _ _ _ composed (fun hp hQt => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
    exact ((sepConj_pure_right _ _ _).1 h_x0p).2 (by rw [heq]))
  -- 8. SLLI + ADDI from base+8 to base+16
  have I1 := slli_spec_gen_same .x5 val M_s (base + 8) (by nofun)
  have I2 := addi_spec_gen_same .x6 count M_a (base + 12) (by nofun)
  have hslli_addi : cpsTriple (base + 8) (base + 16) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
      ((.x5 ↦ᵣ (val <<< M_s.toNat)) ** (.x6 ↦ᵣ (count + signExtend12 M_a))) := by
    runBlock I1 I2
  have hframed := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hslli_addi
  -- 9. Strip pure from ntaken, compose with SLLI+ADDI
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
      xperm_hyp hp')
    ntaken hframed
  -- 10. Final permutation + rewrite x7 = 0
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => hp)
    (fun h hp => by rw [heq] at hp; xperm_hyp hp)
    full
-- ============================================================================
-- CLZ last stage (stage 5): SRLI x7 x5 63 + BNE(8) + ADDI x6 x6 1
-- 3 instructions. BNE offset = 8 (not 12), no SLLI.
-- ============================================================================

def divK_clz_last_prog : List Instr :=
  [.SRLI .x7 .x5 63, .BNE .x7 .x0 8, .ADDI .x6 .x6 1]

abbrev divK_clz_last_code (base : Word) : CodeReq :=
  CodeReq.ofProg base divK_clz_last_prog

/-- CLZ last stage, taken: val >>> 63 ≠ 0 (MSB is 1), skip ADDI.
    x5 unchanged, x6 unchanged, x7 = val >>> 63. -/
theorem divK_clz_last_taken_spec (val count v7 : Word) (base : Word)
    (hne : val >>> 63 ≠ 0) :
    let cr := divK_clz_last_code base
    cpsTriple base (base + 12) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) **
              (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  have I0 := srli_spec_gen .x7 .x5 v7 val 63 base (by nofun)
  have h63 : (63 : BitVec 6).toNat = 63 := by decide
  simp only [h63] at I0
  have hbne_raw := bne_spec_gen .x7 .x0 (8 : BitVec 13) (val >>> 63) (0 : Word) (base + 4)
  have hsig : signExtend13 (8 : BitVec 13) = (8 : Word) := by decide
  have ha_t : (base + 4) + signExtend13 (8 : BitVec 13) = base + 12 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbne_raw
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  have hbne_ext : cpsBranch (base + 4) cr
      (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 12)
        (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> 63 ≠ 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 8)
        (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> 63 = 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))) :=
    fun R hR s hcr hPR hpc =>
      hbne_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show divK_clz_last_code base (base + 4) = _
        simp only [divK_clz_last_code, divK_clz_last_prog,
          CodeReq.ofProg_cons, CodeReq.ofProg_nil,
          CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  have taken := cpsBranch_elim_taken _ _ _ _ _ _ _ composed (fun hp hQf => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
    exact hne ((sepConj_pure_right _ _ _).1 h_x0p).2)
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := taken R hR s hcr hPR hpc
  exact ⟨k, s', hstep, hpc', by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
      xperm_hyp hp') hp hpq⟩⟩
/-- CLZ last stage, ntaken: val >>> 63 = 0, execute ADDI.
    x5 unchanged, x6 = count + 1, x7 = 0. -/
theorem divK_clz_last_ntaken_spec (val count v7 : Word) (base : Word)
    (heq : val >>> 63 = 0) :
    let cr := divK_clz_last_code base
    cpsTriple base (base + 12) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ (count + signExtend12 (1 : BitVec 12))) **
              (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr
  have I0 := srli_spec_gen .x7 .x5 v7 val 63 base (by nofun)
  have h63 : (63 : BitVec 6).toNat = 63 := by decide
  simp only [h63] at I0
  have hbne_raw := bne_spec_gen .x7 .x0 (8 : BitVec 13) (val >>> 63) (0 : Word) (base + 4)
  have hsig : signExtend13 (8 : BitVec 13) = (8 : Word) := by decide
  have ha_t : (base + 4) + signExtend13 (8 : BitVec 13) = base + 12 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbne_raw
  have hbne_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))
    (by pcFree) hbne_raw
  have hbne_ext : cpsBranch (base + 4) cr
      (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 12)
        (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> 63 ≠ 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count)))
      (base + 8)
        (((.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜val >>> 63 = 0⌝) **
         ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count))) :=
    fun R hR s hcr hPR hpc =>
      hbne_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show divK_clz_last_code base (base + 4) = _
        simp only [divK_clz_last_code, divK_clz_last_prog,
          CodeReq.ofProg_cons, CodeReq.ofProg_nil,
          CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) := by
    runBlock I0
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbne_ext
  -- Eliminate taken path (contradicts heq)
  have ntaken := cpsBranch_elim_ntaken _ _ _ _ _ _ _ composed (fun hp hQt => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
    exact ((sepConj_pure_right _ _ _).1 h_x0p).2 (by rw [heq]))
  -- ADDI from base+8 to base+12
  have I2 := addi_spec_gen_same .x6 count 1 (base + 8) (by nofun)
  have haddi : cpsTriple (base + 8) (base + 12) cr
      (.x6 ↦ᵣ count)
      (.x6 ↦ᵣ (count + signExtend12 (1 : BitVec 12))) := by
    runBlock I2
  have hframed := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ val) ** (.x7 ↦ᵣ (val >>> 63)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) haddi
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
      xperm_hyp hp')
    ntaken hframed
  exact cpsTriple_consequence _ _ _ _ _ _ _
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
    (v_off : BitVec 12) (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 v_off) = true) :
    let prod_lo := q_hat * v_i
    let prod_hi := rv64_mulhu q_hat v_i
    let full_sub := prod_lo + carry_in
    let borrow_add := if BitVec.ult full_sub carry_in then (1 : Word) else 0
    let partial_carry := borrow_add + prod_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.MULHU .x5 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x7 .x7 .x10))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x10 .x7 .x10))
       (CodeReq.singleton (base + 20) (.ADD .x10 .x10 .x5))))))
    cpsTriple base (base + 24) cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ partial_carry) **
       (.x5 ↦ᵣ prod_hi) ** (.x7 ↦ᵣ full_sub) **
       ((sp + signExtend12 v_off) ↦ₘ v_i)) := by
  intro prod_lo prod_hi full_sub borrow_add partial_carry cr
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun) hv
  have I1 := mul_spec_gen .x7 .x11 .x5 v7_old q_hat v_i (base + 4) (by nofun)
  have I2 := mulhu_spec_gen_rd_eq_rs2 .x5 .x11 q_hat v_i (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1 .x7 .x10 prod_lo carry_in (base + 12) (by nofun)
  have I4 := sltu_spec_gen_rd_eq_rs2 .x10 .x7 full_sub carry_in (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1 .x10 .x5 borrow_add prod_hi (base + 20) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5

/-- Mul-sub limb Part B: LD u[j+i], SLTU, SUB, ADD, SD.
    5 instructions. Produces carry_out (x10) and stores u_new. -/
theorem divK_mulsub_partB_spec (u_base partial_carry prod_hi full_sub v2_old u_i : Word)
    (u_off : BitVec 12) (base : Word)
    (hv : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let borrow_sub := if BitVec.ult u_i full_sub then (1 : Word) else 0
    let u_new := u_i - full_sub
    let carry_out := partial_carry + borrow_sub
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLTU .x5 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x10 .x10 .x5))
       (CodeReq.singleton (base + 16) (.SD .x6 .x2 u_off)))))
    cpsTriple base (base + 20) cr
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ partial_carry) **
       (.x5 ↦ᵣ prod_hi) ** (.x7 ↦ᵣ full_sub) ** (.x2 ↦ᵣ v2_old) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_out) **
       (.x5 ↦ᵣ borrow_sub) ** (.x7 ↦ᵣ full_sub) ** (.x2 ↦ᵣ u_new) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro borrow_sub u_new carry_out cr
  have I0 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off base (by nofun) hv
  have I1 := sltu_spec_gen .x5 .x2 .x7 prod_hi u_i full_sub (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x2 .x7 u_i full_sub (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1 .x10 .x5 partial_carry borrow_sub (base + 12) (by nofun)
  have I4 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 16) hv
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Add-back correction limb: 8 instructions per limb.
-- u[j+i] += v[i] + carry_in, with carry propagation.
-- ============================================================================

/-- Add-back Part A: LD v[i], LD u[j+i], ADD carry, SLTU carry1, ADD v[i].
    5 instructions. Produces sum (x2) and carry1 (x7). -/
theorem divK_addback_partA_spec (sp u_base carry_in v5_old v2_old v_i u_i : Word)
    (v_off : BitVec 12) (u_off : BitVec 12) (base : Word)
    (hv_v : isValidDwordAccess (sp + signExtend12 v_off) = true)
    (hv_u : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let u_plus_carry := u_i + carry_in
    let carry1 := if BitVec.ult u_plus_carry carry_in then (1 : Word) else 0
    let u_new := u_plus_carry + v_i
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x7 .x2 .x7))
       (CodeReq.singleton (base + 16) (.ADD .x2 .x2 .x5)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry1) **
       (.x5 ↦ᵣ v_i) ** (.x2 ↦ᵣ u_new) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i)) := by
  intro u_plus_carry carry1 u_new cr
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun) hv_v
  have I1 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off (base + 4) (by nofun) hv_u
  have I2 := add_spec_gen_rd_eq_rs1 .x2 .x7 u_i carry_in (base + 8) (by nofun)
  have I3 := sltu_spec_gen_rd_eq_rs2 .x7 .x2 u_plus_carry carry_in (base + 12) (by nofun)
  have I4 := add_spec_gen_rd_eq_rs1 .x2 .x5 u_plus_carry v_i (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

/-- Add-back Part B: SLTU carry2, OR carry_out, SD u_new.
    3 instructions. Produces carry_out (x7) and stores u_new. -/
theorem divK_addback_partB_spec (u_base carry1 v_i u_new u_i : Word)
    (u_off : BitVec 12) (base : Word)
    (hv_u : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let carry2 := if BitVec.ult u_new v_i then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLTU .x5 .x2 .x5))
      (CodeReq.union (CodeReq.singleton (base + 4) (.OR .x7 .x7 .x5))
       (CodeReq.singleton (base + 8) (.SD .x6 .x2 u_off)))
    cpsTriple base (base + 12) cr
      ((.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry1) **
       (.x5 ↦ᵣ v_i) ** (.x2 ↦ᵣ u_new) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_out) **
       (.x5 ↦ᵣ carry2) ** (.x2 ↦ᵣ u_new) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro carry2 carry_out cr
  have I0 := sltu_spec_gen_rd_eq_rs2 .x5 .x2 u_new v_i base (by nofun)
  have I1 := or_spec_gen_rd_eq_rs1 .x7 .x5 carry1 carry2 (base + 4) (by nofun)
  have I2 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 8) hv_u
  runBlock I0 I1 I2

-- ============================================================================
-- Subtract carry from u[j+4]: 4 instructions after mul-sub limbs.
-- ============================================================================

/-- Subtract carry from u[j+4].
    4 instructions: LD, SLTU, SUB, SD. Produces borrow (x7). -/
theorem divK_sub_carry_spec (u_base carry_in v5_old v7_old u_top : Word)
    (u_off : BitVec 12) (base : Word)
    (hv : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let borrow := if BitVec.ult u_top carry_in then (1 : Word) else 0
    let u_new := u_top - carry_in
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLTU .x7 .x5 .x10))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x5 .x5 .x10))
       (CodeReq.singleton (base + 12) (.SD .x6 .x5 u_off))))
    cpsTriple base (base + 16) cr
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       ((u_base + signExtend12 u_off) ↦ₘ u_top))
      ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ u_new) ** (.x7 ↦ᵣ borrow) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro borrow u_new cr
  have I0 := ld_spec_gen .x5 .x6 u_base v5_old u_top u_off base (by nofun) hv
  have I1 := sltu_spec_gen .x7 .x5 .x10 v7_old u_top carry_in (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x5 .x10 u_top carry_in (base + 8) (by nofun)
  have I3 := sd_spec_gen .x6 .x5 u_base u_new u_top u_off (base + 12) hv
  runBlock I0 I1 I2 I3

-- ============================================================================
-- Store q[j]: 4 instructions.
-- ============================================================================

/-- Store q[j]: compute &q[j] = sp+4088 - j*8, store q_hat.
    First 3 instructions compute q_addr. Then SD stores. Split into 3+1. -/
theorem divK_store_qj_addr_spec (sp j v5_old v7_old : Word)
    (base : Word) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let sp_m8 := sp + signExtend12 4088
    let q_addr := sp_m8 - j_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x5 .x1 3))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x7 .x12 4088))
       (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5)))
    cpsTriple base (base + 12) cr
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old))
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr)) := by
  intro j_x8 sp_m8 q_addr cr
  have I0 := slli_spec_gen .x5 .x1 v5_old j 3 base (by nofun)
  have I1 := addi_spec_gen .x7 .x12 v7_old sp 4088 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x7 .x5 sp_m8 j_x8 (base + 8) (by nofun)
  runBlock I0 I1 I2

/-- Store q[j]: SD q_hat at q_addr. 1 instruction. -/
theorem divK_store_qj_write_spec (q_addr q_hat q_old : Word) (base : Word)
    (hv : isValidDwordAccess q_addr = true) :
    let cr := CodeReq.singleton base (.SD .x7 .x11 0)
    cpsTriple base (base + 4) cr
      ((.x7 ↦ᵣ q_addr) ** (.x11 ↦ᵣ q_hat) ** (q_addr ↦ₘ q_old))
      ((.x7 ↦ᵣ q_addr) ** (.x11 ↦ᵣ q_hat) ** (q_addr ↦ₘ q_hat)) := by
  intro cr
  have hse : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
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
    (u_off : BitVec 12) (base : Word)
    (hv : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let u_new := u_top + carry
    let q_hat' := q_hat + signExtend12 4095
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x5 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SD .x6 .x5 u_off))
       (CodeReq.singleton (base + 12) (.ADDI .x11 .x11 4095))))
    cpsTriple base (base + 16) cr
      ((.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (u_base + signExtend12 u_off ↦ₘ u_top))
      ((.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry) ** (.x11 ↦ᵣ q_hat') **
       (.x5 ↦ᵣ u_new) ** (u_base + signExtend12 u_off ↦ₘ u_new)) := by
  intro u_new q_hat' cr
  have I0 := ld_spec_gen .x5 .x6 u_base v5_old u_top u_off base (by nofun) hv
  have I1 := add_spec_gen_rd_eq_rs1 .x5 .x7 u_top carry (base + 4) (by nofun)
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
    (base : Word) :
    let j' := j + signExtend12 4095
    let cr :=
      CodeReq.union (CodeReq.singleton base (.ADDI .x1 .x1 4095))
       (CodeReq.singleton (base + 4) (.BGE .x1 .x0 loop_back_off))
    cpsBranch base cr
      ((.x1 ↦ᵣ j) ** (.x0 ↦ᵣ 0))
      (base + 4 + signExtend13 loop_back_off)
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      (base + 8)
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) := by
  intro j' cr
  -- 1. ADDI body
  have hbody : cpsTriple base (base + 4) cr
      ((.x1 ↦ᵣ j) ** (.x0 ↦ᵣ 0))
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) := by
    have I0 := addi_spec_gen_same .x1 j 4095 base (by nofun)
    runBlock I0
  -- 2. BGE, drop pure facts
  have hbge_raw := bge_spec_gen .x1 .x0 loop_back_off j' 0 (base + 4)
  have ha1 : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha1] at hbge_raw
  have hbge : cpsBranch (base + 4) _
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      ((base + 4) + signExtend13 loop_back_off)
        ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      (base + 8)
        ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) :=
    cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      hbge_raw
  -- 3. Extend BGE to full cr
  have hbge_ext : cpsBranch (base + 4) cr
      ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      ((base + 4) + signExtend13 loop_back_off) ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0))
      (base + 8) ((.x1 ↦ᵣ j') ** (.x0 ↦ᵣ 0)) :=
    fun R hR s hcr hPR hpc =>
      hbge R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show CodeReq.union (CodeReq.singleton base (.ADDI .x1 .x1 4095))
          (CodeReq.singleton (base + 4) (.BGE .x1 .x0 loop_back_off)) (base + 4) = _
        simp only [CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  -- 4. Compose
  exact cpsTriple_seq_cpsBranch_same_cr _ _ _ _ _ _ _ _ _ hbody hbge_ext
-- ============================================================================
-- Mul-sub setup: restore j, compute u_base = &u[j], init carry = 0.
-- 5 instructions: LD + SLLI + ADDI + SUB + ADDI.
-- ============================================================================

/-- Mul-sub setup: restore j from scratch, compute u_base, zero carry. -/
theorem divK_mulsub_setup_spec (sp q_hat j v1_old v5_old v6_old v10_old : Word)
    (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 3976) = true) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let sp_m40 := sp + signExtend12 4056
    let u_base := sp_m40 - j_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3976))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLLI .x5 .x1 3))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x6 .x12 4056))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x6 .x6 .x5))
       (CodeReq.singleton (base + 16) (.ADDI .x10 .x0 0)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x1 ↦ᵣ v1_old) ** (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x10 ↦ᵣ v10_old) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ j_x8) ** (.x6 ↦ᵣ u_base) **
       (.x10 ↦ᵣ signExtend12 0) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j)) := by
  intro j_x8 sp_m40 u_base cr
  have I0 := ld_spec_gen .x1 .x12 sp v1_old j 3976 base (by nofun) hv
  have I1 := slli_spec_gen .x5 .x1 v5_old j 3 (base + 4) (by nofun)
  have I2 := addi_spec_gen .x6 .x12 v6_old sp 4056 (base + 8) (by nofun)
  have I3 := sub_spec_gen_rd_eq_rs1 .x6 .x5 sp_m40 j_x8 (base + 12) (by nofun)
  have I4 := addi_x0_spec_gen .x10 v10_old 0 (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Save j: 1 instruction SD.
-- ============================================================================

/-- Save j to scratch memory. -/
theorem divK_save_j_spec (sp j j_old : Word) (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 3976) = true) :
    let cr := CodeReq.singleton base (.SD .x12 .x1 3976)
    cpsTriple base (base + 4) cr
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) ** (sp + signExtend12 3976 ↦ₘ j_old))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) ** (sp + signExtend12 3976 ↦ₘ j)) := by
  intro cr
  have I0 := sd_spec_gen .x12 .x1 sp j j_old 3976 base hv
  runBlock I0

-- ============================================================================
-- Addback carry init: ADDI x7 x0 0 (set carry = 0).
-- ============================================================================

/-- Initialize add-back carry to 0. -/
theorem divK_addback_init_spec (v7_old : Word) (base : Word) :
    let cr := CodeReq.singleton base (.ADDI .x7 .x0 0)
    cpsTriple base (base + 4) cr
      ((.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ 0))
      ((.x7 ↦ᵣ signExtend12 0) ** (.x0 ↦ᵣ 0)) := by
  intro cr
  have I0 := addi_x0_spec_gen .x7 v7_old 0 base (by nofun)
  runBlock I0

-- ============================================================================
-- Addback condition: BEQ x7 x0 (skip correction if no borrow).
-- ============================================================================

/-- Correction condition: branch if borrow (x7) is zero. -/
theorem divK_correction_branch_spec (borrow : Word) (skip_off : BitVec 13) (base : Word) :
    let cr := CodeReq.singleton base (.BEQ .x7 .x0 skip_off)
    cpsBranch base cr
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ 0))
      (base + signExtend13 skip_off)
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ 0))
      (base + 4)
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ 0)) := by
  intro cr
  have hbeq := beq_spec_gen .x7 .x0 skip_off borrow 0 base
  exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
    (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
    hbeq
-- ============================================================================
-- Trial quotient: load u[j+n], u[j+n-1].
-- 7 instructions: LD + ADD + SLLI + ADDI + SUB + LD + LD.
-- ============================================================================

/-- Load u_hi = u[j+n] and u_lo = u[j+n-1] for trial quotient estimation.
    u_addr = sp + signExtend12 4056 - (j + n) <<< 3.
    u_hi = mem[u_addr], u_lo = mem[u_addr + 8]. -/
theorem divK_trial_load_u_spec (sp j n v5_old v7_old u_hi u_lo : Word)
    (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) + 8) = true) :
    let jpn := j + n
    let jpn_x8 := jpn <<< (3 : BitVec 6).toNat
    let u0_base := sp + signExtend12 4056
    let u_addr := u0_base - jpn_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x7 .x1 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x7 .x7 3))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADDI .x5 .x12 4056))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x5 0))
       (CodeReq.singleton (base + 24) (.LD .x5 .x5 8)))))))
    cpsTriple base (base + 28) cr
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u_lo) ** (.x7 ↦ᵣ u_hi) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo)) := by
  intro jpn jpn_x8 u0_base u_addr cr
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr0 : u_addr + signExtend12 (0 : BitVec 12) = u_addr := by rw [hse0]; bv_omega
  have hv_uhi' : isValidDwordAccess (u_addr + signExtend12 0) = true := by rw [haddr0]; exact hv_uhi
  have I0 := ld_spec_gen .x5 .x12 sp v5_old n 3984 base (by nofun) hv_n
  have I1 := add_spec_gen .x7 .x1 .x5 j n v7_old (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x7 jpn 3 (base + 8) (by nofun)
  have I3 := addi_spec_gen .x5 .x12 n sp 4056 (base + 12) (by nofun)
  have I4 := sub_spec_gen_rd_eq_rs1 .x5 .x7 u0_base jpn_x8 (base + 16) (by nofun)
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
    (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_vtop : isValidDwordAccess (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true) :
    let nm1 := n + signExtend12 4095
    let nm1_x8 := nm1 <<< (3 : BitVec 6).toNat
    let vtop_base := sp + nm1_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x6 .x6 4095))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x6 .x6 3))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x6 .x12 .x6))
       (CodeReq.singleton (base + 16) (.LD .x10 .x6 32)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6_old) ** (.x10 ↦ᵣ v10_old) **
       (sp + signExtend12 3984 ↦ₘ n) ** (vtop_base + signExtend12 32 ↦ₘ v_top))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ vtop_base) ** (.x10 ↦ᵣ v_top) **
       (sp + signExtend12 3984 ↦ₘ n) ** (vtop_base + signExtend12 32 ↦ₘ v_top)) := by
  intro nm1 nm1_x8 vtop_base cr
  have I0 := ld_spec_gen .x6 .x12 sp v6_old n 3984 base (by nofun) hv_n
  have I1 := addi_spec_gen_same .x6 n 4095 (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x6 nm1 3 (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs2 .x6 .x12 sp nm1_x8 (base + 12) (by nofun)
  have I4 := ld_spec_gen .x10 .x6 vtop_base v10_old v_top 32 (base + 16) (by nofun) hv_vtop
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Trial quotient: MAX path (u_hi >= v_top).
-- 2 instructions: ADDI x11 x0 4095 + JAL x0 8.
-- ============================================================================

/-- Trial quotient MAX path: set q_hat = MAX64, jump over div128 call. -/
theorem divK_trial_max_spec (v11_old : Word) (base : Word) :
    let cr :=
      CodeReq.union (CodeReq.singleton base (.ADDI .x11 .x0 4095))
       (CodeReq.singleton (base + 4) (.JAL .x0 8))
    cpsTriple base (base + 12) cr
      ((.x11 ↦ᵣ v11_old) ** (.x0 ↦ᵣ 0))
      ((.x11 ↦ᵣ signExtend12 4095) ** (.x0 ↦ᵣ 0)) := by
  intro cr
  have hj : signExtend21 (8 : BitVec 21) = (8 : Word) := by decide
  have I0 := addi_x0_spec_gen .x11 v11_old 4095 base (by nofun)
  have I1 := jal_x0_spec_gen 8 (base + 4)
  rw [hj] at I1
  have ha : (base + 4 : Word) + 8 = base + 12 := by bv_addr
  rw [ha] at I1
  runBlock I0 I1

-- ============================================================================
-- div128 subroutine: Phase 1a — save return addr and d, split d.
-- 6 instructions: SD + SD + SRLI + SLLI + SRLI + SD.
-- ============================================================================

/-- div128 Phase 1a: save x2 (return addr) and x10 (d), compute d_hi and d_lo. -/
theorem divK_div128_save_split_d_spec (sp ret_addr d v1_old v6_old
    ret_mem d_mem dlo_mem : Word) (base : Word)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true) :
    let d_hi := d >>> (32 : BitVec 6).toNat
    let d_lo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SD .x12 .x2 3968))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SD .x12 .x10 3960))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SRLI .x6 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLLI .x1 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SRLI .x1 .x1 32))
       (CodeReq.singleton (base + 20) (.SD .x12 .x1 3952))))))
    cpsTriple base (base + 24) cr
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x6 ↦ᵣ v6_old) ** (.x1 ↦ᵣ v1_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem))
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x6 ↦ᵣ d_hi) ** (.x1 ↦ᵣ d_lo) **
       (sp + signExtend12 3968 ↦ₘ ret_addr) **
       (sp + signExtend12 3960 ↦ₘ d) **
       (sp + signExtend12 3952 ↦ₘ d_lo)) := by
  intro d_hi d_lo cr
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
theorem divK_div128_split_ulo_spec (sp u_lo v11_old un0_mem : Word) (base : Word)
    (hv_un0 : isValidDwordAccess (sp + signExtend12 3944) = true) :
    let un1 := u_lo >>> (32 : BitVec 6).toNat
    let un0 := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SRLI .x11 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLLI .x5 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SRLI .x5 .x5 32))
       (CodeReq.singleton (base + 12) (.SD .x12 .x5 3944))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u_lo) ** (.x11 ↦ᵣ v11_old) **
       (sp + signExtend12 3944 ↦ₘ un0_mem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ un0) ** (.x11 ↦ᵣ un1) **
       (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro un1 un0 cr
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
theorem divK_div128_step1_init_spec (u_hi d_hi v5_old v10_old : Word) (base : Word) :
    let q1 := rv64_divu u_hi d_hi
    let rhat := u_hi - q1 * d_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x10 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x6))
       (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5)))
    cpsTriple base (base + 12) cr
      ((.x7 ↦ᵣ u_hi) ** (.x6 ↦ᵣ d_hi) **
       (.x10 ↦ᵣ v10_old) ** (.x5 ↦ᵣ v5_old))
      ((.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi) **
       (.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q1 * d_hi)) := by
  intro q1 rhat cr
  have I0 := divu_spec_gen .x10 .x7 .x6 v10_old u_hi d_hi base (by nofun)
  have I1 := mul_spec_gen .x5 .x10 .x6 v5_old q1 d_hi (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x7 .x5 u_hi (q1 * d_hi) (base + 8) (by nofun)
  runBlock I0 I1 I2

-- ============================================================================
-- div128 subroutine: Compute un21 from rhat, un1, q1, d_lo.
-- 5 instructions: LD + SLLI + OR + MUL + SUB.
-- ============================================================================

/-- div128 un21 = rhat*2^32 + un1 - q1*d_lo.
    Loads d_lo from scratch memory. -/
theorem divK_div128_compute_un21_spec (sp q1 rhat un1 v1_old v5_old dlo_mem : Word) (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 3952) = true) :
    let rhat_hi := rhat <<< (32 : BitVec 6).toNat
    let rhat_un1 := rhat_hi ||| un1
    let q1_dlo := q1 * dlo_mem
    let un21 := rhat_un1 - q1_dlo
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLLI .x5 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 8) (.OR .x5 .x5 .x11))
      (CodeReq.union (CodeReq.singleton (base + 12) (.MUL .x1 .x10 .x1))
       (CodeReq.singleton (base + 16) (.SUB .x7 .x5 .x1)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) **
       (.x11 ↦ᵣ un1) ** (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ un21) **
       (.x11 ↦ᵣ un1) ** (.x5 ↦ᵣ rhat_un1) ** (.x1 ↦ᵣ q1_dlo) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem)) := by
  intro rhat_hi rhat_un1 q1_dlo un21 cr
  have I0 := ld_spec_gen .x1 .x12 sp v1_old dlo_mem 3952 base (by nofun) hv
  have I1 := slli_spec_gen .x5 .x7 v5_old rhat 32 (base + 4) (by nofun)
  have I2 := or_spec_gen_rd_eq_rs1 .x5 .x11 rhat_hi un1 (base + 8) (by nofun)
  have I3 := mul_spec_gen_rd_eq_rs2 .x1 .x10 q1 dlo_mem (base + 12) (by nofun)
  have I4 := sub_spec_gen .x7 .x5 .x1 rhat_un1 q1_dlo rhat (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4


-- ============================================================================
-- div128 subroutine: Product check body (before BLTU).
-- 4 instructions: LD + MUL + SLLI + OR.
-- ============================================================================

/-- div128 product check body: compute q*d_lo and rhat*2^32+un1 for comparison. -/
theorem divK_div128_prodcheck_body_spec (sp q rhat un1 v1_old v5_old dlo : Word) (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 3952) = true) :
    let q_dlo := q * dlo
    let rhat_hi := rhat <<< (32 : BitVec 6).toNat
    let rhat_un1 := rhat_hi ||| un1
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x1 .x7 32))
       (CodeReq.singleton (base + 12) (.OR .x1 .x1 .x11))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) ** (sp + signExtend12 3952 ↦ₘ dlo))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ q_dlo) ** (.x1 ↦ᵣ rhat_un1) ** (sp + signExtend12 3952 ↦ₘ dlo)) := by
  intro q_dlo rhat_hi rhat_un1 cr
  have I0 := ld_spec_gen .x1 .x12 sp v1_old dlo 3952 base (by nofun) hv
  have I1 := mul_spec_gen .x5 .x10 .x1 v5_old q dlo (base + 4) (by nofun)
  have I2 := slli_spec_gen .x1 .x7 dlo rhat 32 (base + 8) (by nofun)
  have I3 := or_spec_gen_rd_eq_rs1 .x1 .x11 (rhat <<< (32 : BitVec 6).toNat) un1 (base + 12) (by nofun)
  runBlock I0 I1 I2 I3

-- ============================================================================
-- div128 subroutine: Correction path (2 instrs: ADDI q-- + ADD rhat+=d_hi).
-- Used after product check BLTU taken, and also after q1/q0 clamp BEQ ntaken.
-- ============================================================================

/-- div128 correction: q-- and rhat += d_hi. Generic for q1 (x10) or q0 (x5). -/
theorem divK_div128_correct_q1_spec (q rhat d_hi : Word) (base : Word) :
    let q' := q + signExtend12 4095
    let rhat' := rhat + d_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 4) (.ADD .x7 .x7 .x6))
    cpsTriple base (base + 8) cr
      ((.x10 ↦ᵣ q) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi))
      ((.x10 ↦ᵣ q') ** (.x7 ↦ᵣ rhat') ** (.x6 ↦ᵣ d_hi)) := by
  intro q' rhat' cr
  have I0 := addi_spec_gen_same .x10 q 4095 base (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1 .x7 .x6 rhat d_hi (base + 4) (by nofun)
  runBlock I0 I1

/-- div128 correction for q0: q0-- and rhat2 += d_hi. -/
theorem divK_div128_correct_q0_spec (q0 rhat2 d_hi : Word) (base : Word) :
    let q0' := q0 + signExtend12 4095
    let rhat2' := rhat2 + d_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.ADDI .x5 .x5 4095))
       (CodeReq.singleton (base + 4) (.ADD .x11 .x11 .x6))
    cpsTriple base (base + 8) cr
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi))
      ((.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ rhat2') ** (.x6 ↦ᵣ d_hi)) := by
  intro q0' rhat2' cr
  have I0 := addi_spec_gen_same .x5 q0 4095 base (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1 .x11 .x6 rhat2 d_hi (base + 4) (by nofun)
  runBlock I0 I1

-- ============================================================================
-- div128 subroutine: q1 clamp body (SRLI test, before BEQ).
-- 1 instruction: SRLI x5 x10 32.
-- ============================================================================

/-- div128 q1 clamp test: x5 = q1 >>> 32 (nonzero iff q1 >= 2^32). -/
theorem divK_div128_clamp_test_q1_spec (q1 v5_old : Word) (base : Word) :
    let hi := q1 >>> (32 : BitVec 6).toNat
    let cr := CodeReq.singleton base (.SRLI .x5 .x10 32)
    cpsTriple base (base + 4) cr
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ v5_old))
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ hi)) := by
  intro hi cr
  have I0 := srli_spec_gen .x5 .x10 v5_old q1 32 base (by nofun)
  runBlock I0

/-- div128 q0 clamp test: x1 = q0 >>> 32. -/
theorem divK_div128_clamp_test_q0_spec (q0 v1_old : Word) (base : Word) :
    let hi := q0 >>> (32 : BitVec 6).toNat
    let cr := CodeReq.singleton base (.SRLI .x1 .x5 32)
    cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ q0) ** (.x1 ↦ᵣ v1_old))
      ((.x5 ↦ᵣ q0) ** (.x1 ↦ᵣ hi)) := by
  intro hi cr
  have I0 := srli_spec_gen .x1 .x5 v1_old q0 32 base (by nofun)
  runBlock I0

-- ============================================================================
-- div128 subroutine: Step 2 initial — DIVU q0, compute rhat2.
-- 3 instructions: DIVU + MUL + SUB.
-- ============================================================================

/-- div128 Step 2: q0 = DIVU(un21, d_hi), rhat2 = un21 - q0 * d_hi. -/
theorem divK_div128_step2_init_spec (un21 d_hi v1_old v5_old v11_old : Word) (base : Word) :
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
       (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1)))
    cpsTriple base (base + 12) cr
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) ** (.x11 ↦ᵣ v11_old))
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ q0) ** (.x1 ↦ᵣ q0 * d_hi) ** (.x11 ↦ᵣ rhat2)) := by
  intro q0 rhat2 cr
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
    (base : Word)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_un0 : isValidDwordAccess (sp + signExtend12 3944) = true) :
    let q0_dlo := q0 * dlo
    let rhat2_hi := rhat2 <<< (32 : BitVec 6).toNat
    let rhat2_un0 := rhat2_hi ||| un0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.LD .x11 .x12 3944))
       (CodeReq.singleton (base + 16) (.OR .x1 .x1 .x11)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) **
       (.x7 ↦ᵣ v7_old) ** (.x1 ↦ᵣ v1_old) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
       (.x7 ↦ᵣ q0_dlo) ** (.x1 ↦ᵣ rhat2_un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0_dlo rhat2_hi rhat2_un0 cr
  have I0 := ld_spec_gen .x1 .x12 sp v1_old dlo 3952 base (by nofun) hv_dlo
  have I1 := mul_spec_gen .x7 .x5 .x1 v7_old q0 dlo (base + 4) (by nofun)
  have I2 := slli_spec_gen .x1 .x11 dlo rhat2 32 (base + 8) (by nofun)
  have I3 := ld_spec_gen .x11 .x12 sp rhat2 un0 3944 (base + 12) (by nofun) hv_un0
  have I4 := or_spec_gen_rd_eq_rs1 .x1 .x11 rhat2_hi un0 (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- div128 subroutine: Single-instr ADDI correction (product check 2, q0--).
-- 1 instruction: ADDI x5 x5 4095.
-- ============================================================================

/-- div128 product check 2 correction: q0--. -/
theorem divK_div128_correct_q0_single_spec (q0 : Word) (base : Word) :
    let q0' := q0 + signExtend12 4095
    let cr := CodeReq.singleton base (.ADDI .x5 .x5 4095)
    cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ q0))
      ((.x5 ↦ᵣ q0')) := by
  intro q0' cr
  have I0 := addi_spec_gen_same .x5 q0 4095 base (by nofun)
  runBlock I0

-- ============================================================================
-- div128 subroutine: Combine q = q1<<32 | q0 (instrs 45-46).
-- 2 instructions: SLLI + OR.
-- ============================================================================

/-- div128 combine: x11 = q1<<32 | q0. -/
theorem divK_div128_combine_q_spec (q1 q0 v11_old : Word) (base : Word) :
    let q1_hi := q1 <<< (32 : BitVec 6).toNat
    let q := q1_hi ||| q0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x11 .x10 32))
       (CodeReq.singleton (base + 4) (.OR .x11 .x11 .x5))
    cpsTriple base (base + 8) cr
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ v11_old))
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ q)) := by
  intro q1_hi q cr
  have I0 := slli_spec_gen .x11 .x10 v11_old q1 32 base (by nofun)
  have I1 := or_spec_gen_rd_eq_rs1 .x11 .x5 q1_hi q0 (base + 4) (by nofun)
  runBlock I0 I1

-- ============================================================================
-- div128 subroutine: Restore return addr + JALR return (instrs 47-48).
-- 2 instructions: LD + JALR.
-- ============================================================================

/-- div128 restore and return: load return addr, JALR x0 x2 0. -/
theorem divK_div128_restore_return_spec (sp v2_old ret_addr : Word) (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 3968) = true)
    (halign : (ret_addr + signExtend12 0) &&& ~~~1 = ret_addr) :
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x2 .x12 3968))
       (CodeReq.singleton (base + 4) (.JALR .x0 .x2 0))
    cpsTriple base ret_addr cr
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2_old) ** (sp + signExtend12 3968 ↦ₘ ret_addr))
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (sp + signExtend12 3968 ↦ₘ ret_addr)) := by
  intro cr
  have I0 := ld_spec_gen .x2 .x12 sp v2_old ret_addr 3968 base (by nofun) hv
  have I1 := jalr_x0_spec_gen .x2 ret_addr 0 (base + 4)
  rw [halign] at I1
  runBlock I0 I1

-- ============================================================================
-- div128 subroutine: Clamp q1 section [13]-[16].
-- 4 instructions: SRLI + BEQ + ADDI + ADD.
-- BEQ skips correction if q1 < 2^32, else q1-- and rhat+=d_hi.
-- ============================================================================

set_option maxRecDepth 1024 in
/-- div128 clamp q1: test q1 >= 2^32, conditionally decrement and adjust rhat.
    Instrs [13]-[16]. Both BEQ paths merge at base+16. -/
theorem divK_div128_clamp_q1_merged_spec (q1 rhat d_hi v5_old : Word) (base : Word) :
    let hi := q1 >>> (32 : BitVec 6).toNat
    let q1' := if hi = 0 then q1 else q1 + signExtend12 4095
    let rhat' := if hi = 0 then rhat else rhat + d_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SRLI .x5 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.BEQ .x5 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 12) (.ADD .x7 .x7 .x6))))
    cpsTriple base (base + 16) cr
      ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ v5_old) ** (.x0 ↦ᵣ 0))
      ((.x10 ↦ᵣ q1') ** (.x7 ↦ᵣ rhat') ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
  intro hi q1' rhat' cr
  -- 1. SRLI body
  have I0 := srli_spec_gen .x5 .x10 v5_old q1 32 base (by nofun)
  have hbody : cpsTriple base (base + 4) cr
      ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ v5_old) ** (.x0 ↦ᵣ 0))
      ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi) **
       (.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
    runBlock I0
  -- 2. BEQ at base+4 (keep pure facts)
  have hbeq_raw := beq_spec_gen .x5 .x0 (12 : BitVec 13) hi (0 : Word) (base + 4)
  have hsig : signExtend13 (12 : BitVec 13) = (12 : Word) := by decide
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbeq_raw
  -- 3. Frame BEQ with x10, x7, x6
  have hbeq_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi))
    (by pcFree) hbeq_raw
  -- 4. Extend to full cr
  have hbeq_ext : cpsBranch (base + 4) cr
      (((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi)))
      (base + 16)
        (((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi = 0⌝) **
         ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi)))
      (base + 8)
        (((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi ≠ 0⌝) **
         ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi))) :=
    fun R hR s hcr hPR hpc =>
      hbeq_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show cr (base + 4) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  -- 5. Compose body → BEQ
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_ext
  -- 6. by_cases on hi = 0
  by_cases hcond : hi = 0
  · -- hi = 0 → BEQ taken (skip correction)
    have hq : q1' = q1 := if_pos hcond
    have hr : rhat' = rhat := if_pos hcond
    rw [hq, hr]
    -- Eliminate ntaken path (hi ≠ 0 contradicts hcond)
    have taken := cpsBranch_elim_taken _ _ _ _ _ _ _ composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    -- Strip pure fact from taken postcondition and permute
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp') taken
  · -- hi ≠ 0 → BEQ not-taken (execute correction)
    have hq : q1' = q1 + signExtend12 4095 := if_neg hcond
    have hr : rhat' = rhat + d_hi := if_neg hcond
    rw [hq, hr]
    -- Eliminate taken path (hi = 0 contradicts hcond)
    have ntaken := cpsBranch_elim_ntaken _ _ _ _ _ _ _ composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact hcond ((sepConj_pure_right _ _ _).1 h_x0p).2)
    -- Correction: ADDI + ADD from base+8 to base+16
    have I1 := addi_spec_gen_same .x10 q1 4095 (base + 8) (by nofun)
    have I2 := add_spec_gen_rd_eq_rs1 .x7 .x6 rhat d_hi (base + 12) (by nofun)
    have hcorr : cpsTriple (base + 8) (base + 16) cr
        ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi))
        ((.x10 ↦ᵣ (q1 + signExtend12 4095)) ** (.x7 ↦ᵣ (rhat + d_hi)) ** (.x6 ↦ᵣ d_hi)) := by
      runBlock I1 I2
    have hcorr_framed := cpsTriple_frame_left _ _ _ _ _
      ((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcFree) hcorr
    have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp') ntaken hcorr_framed
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp) full
-- ============================================================================
-- div128 subroutine: Product check 1 section [17]-[24].
-- 8 instructions: LD+MUL+SLLI+OR (body) + BLTU+JAL (branch) + ADDI+ADD (correction).
-- BLTU taken → correction, BLTU ntaken → JAL skip. Both merge at base+32.
-- ============================================================================

set_option maxRecDepth 8192 in
/-- div128 product check 1: compute q1*d_lo vs rhat*2^32+un1, conditionally correct.
    Instrs [17]-[24]. Both BLTU paths merge at base+32. -/
theorem divK_div128_prodcheck1_merged_spec
    (sp q1 rhat d_hi un1 v1_old v5_old dlo : Word) (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 3952) = true) :
    let q_dlo := q1 * dlo
    let rhat_un1 := (rhat <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1 + signExtend12 4095 else q1
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhat + d_hi else rhat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 20) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 28) (.ADD .x7 .x7 .x6))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) ** (.x6 ↦ᵣ d_hi) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1') ** (.x7 ↦ᵣ rhat') ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ q_dlo) ** (.x1 ↦ᵣ rhat_un1) ** (.x6 ↦ᵣ d_hi) **
       (sp + signExtend12 3952 ↦ₘ dlo)) := by
  intro q_dlo rhat_un1 q1' rhat' cr
  -- 1. Body: 4 instructions (LD+MUL+SLLI+OR)
  have hbody : cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) ** (.x6 ↦ᵣ d_hi) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ q_dlo) ** (.x1 ↦ᵣ rhat_un1) ** (.x6 ↦ᵣ d_hi) **
       (sp + signExtend12 3952 ↦ₘ dlo)) := by
    have I0 := ld_spec_gen .x1 .x12 sp v1_old dlo 3952 base (by nofun) hv
    have I1 := mul_spec_gen .x5 .x10 .x1 v5_old q1 dlo (base + 4) (by nofun)
    have I2 := slli_spec_gen .x1 .x7 dlo rhat 32 (base + 8) (by nofun)
    have I3 := or_spec_gen_rd_eq_rs1 .x1 .x11 (rhat <<< (32 : BitVec 6).toNat) un1 (base + 12) (by nofun)
    runBlock I0 I1 I2 I3
  -- 2. BLTU at base+16, strip pure
  have hbltu_raw := bltu_spec_gen .x1 .x5 (8 : BitVec 13) rhat_un1 q_dlo (base + 16)
  have hsig : signExtend13 (8 : BitVec 13) = (8 : Word) := by decide
  have ha_t : (base + 16) + signExtend13 (8 : BitVec 13) = base + 24 := by rw [hsig]; bv_addr
  have ha_f : (base + 16 : Word) + 4 = base + 20 := by bv_addr
  rw [ha_t, ha_f] at hbltu_raw
  -- 3. Frame BLTU with remaining atoms
  have hbltu_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
     (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo))
    (by pcFree) hbltu_raw
  -- 4. Extend to full cr
  have hbltu_ext : cpsBranch (base + 16) cr
      (((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo)) **
       ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
        (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo)))
      (base + 24)
        (((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo) ** ⌜BitVec.ult rhat_un1 q_dlo⌝) **
         ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
          (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo)))
      (base + 20)
        (((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo) ** ⌜¬BitVec.ult rhat_un1 q_dlo⌝) **
         ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
          (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo))) :=
    fun R hR s hcr hPR hpc =>
      hbltu_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show cr (base + 16) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 16 = base) := by bv_omega
        have h1 : ¬(base + 16 = base + 4) := by bv_omega
        have h2 : ¬(base + 16 = base + 8) := by bv_omega
        have h3 : ¬(base + 16 = base + 12) := by bv_omega
        simp only [beq_iff_eq, h0, h1, h2, h3, ↓reduceIte]))) hPR hpc
  -- 5. Compose body → BLTU
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbltu_ext
  -- 6. by_cases on BLTU condition
  by_cases hcond : BitVec.ult rhat_un1 q_dlo
  · -- BLTU taken: rhat_un1 < q_dlo → correction
    have hq : q1' = q1 + signExtend12 4095 := if_pos hcond
    have hr : rhat' = rhat + d_hi := if_pos hcond
    rw [hq, hr]
    -- Eliminate ntaken path
    have taken_br := cpsBranch_elim_taken _ _ _ _ _ _ _ composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    -- Correction: ADDI q1-- + ADD rhat+=d_hi
    have I4 := addi_spec_gen_same .x10 q1 4095 (base + 24) (by nofun)
    have I5 := add_spec_gen_rd_eq_rs1 .x7 .x6 rhat d_hi (base + 28) (by nofun)
    have hcorr : cpsTriple (base + 24) (base + 32) cr
        ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ d_hi))
        ((.x10 ↦ᵣ (q1 + signExtend12 4095)) ** (.x7 ↦ᵣ (rhat + d_hi)) ** (.x6 ↦ᵣ d_hi)) := by
      runBlock I4 I5
    have hcorr_framed := cpsTriple_frame_left _ _ _ _ _
      ((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ un1) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      (by pcFree) hcorr
    have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp')
      taken_br hcorr_framed
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp) full
  · -- BLTU not-taken: rhat_un1 >= q_dlo → JAL skip
    have hq : q1' = q1 := if_neg hcond
    have hr : rhat' = rhat := if_neg hcond
    rw [hq, hr]
    -- Eliminate taken path
    have ntaken_br := cpsBranch_elim_ntaken _ _ _ _ _ _ _ composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact absurd ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    -- JAL skip: base+20 → base+32
    have hj : signExtend21 (12 : BitVec 21) = (12 : Word) := by decide
    have I_jal := jal_x0_spec_gen 12 (base + 20)
    rw [hj] at I_jal
    have ha_jal : (base + 20 : Word) + 12 = base + 32 := by bv_addr
    rw [ha_jal] at I_jal
    -- Extend JAL CR from singleton to cr
    have hcr_jal : ∀ a i, CodeReq.singleton (base + 20) (.JAL .x0 12) a = some i →
        cr a = some i := by
      intro a i h
      simp only [CodeReq.singleton] at h
      split at h
      · next heq => rw [beq_iff_eq] at heq; subst heq; simp_all [cr, CodeReq.union, CodeReq.singleton]
      · simp at h
    have I_jal_cr := cpsTriple_extend_code hcr_jal I_jal
    have hjal_framed := cpsTriple_frame_left _ _ _ _ _
      ((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo) ** (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) **
       (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) ** (.x6 ↦ᵣ d_hi) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      (by pcFree) I_jal_cr
    simp only [sepConj_emp_left'] at hjal_framed
    -- Strip pure and compose with JAL
    have ntaken_clean : cpsTriple base (base + 20) cr
        ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
         (.x5 ↦ᵣ v5_old) ** (.x1 ↦ᵣ v1_old) ** (.x6 ↦ᵣ d_hi) **
         (sp + signExtend12 3952 ↦ₘ dlo))
        ((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo) **
         (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
         (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo)) :=
      cpsTriple_consequence _ _ _ _ _ _ _
        (fun h hp => hp)
        (fun h hp => by
          have hp' : (((.x1 ↦ᵣ rhat_un1) ** (.x5 ↦ᵣ q_dlo)) **
            ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
             (.x6 ↦ᵣ d_hi) ** (sp + signExtend12 3952 ↦ₘ dlo))) h :=
            sepConj_mono_left (sepConj_mono_right
              (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
          xperm_hyp hp')
        ntaken_br
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
        (fun _ hp => hp)
        ntaken_clean hjal_framed)
-- ============================================================================
-- div128 subroutine: Clamp q0 section [33]-[36].
-- 4 instructions: SRLI + BEQ + ADDI + ADD.
-- BEQ skips correction if q0 < 2^32, else q0-- and rhat2+=d_hi.
-- ============================================================================

set_option maxRecDepth 1024 in
/-- div128 clamp q0: test q0 >= 2^32, conditionally decrement and adjust rhat2.
    Instrs [33]-[36]. Both BEQ paths merge at base+16. -/
theorem divK_div128_clamp_q0_merged_spec (q0 rhat2 d_hi v1_old : Word) (base : Word) :
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0' := if hi = 0 then q0 else q0 + signExtend12 4095
    let rhat2' := if hi = 0 then rhat2 else rhat2 + d_hi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x5 .x5 4095))
       (CodeReq.singleton (base + 12) (.ADD .x11 .x11 .x6))))
    cpsTriple base (base + 16) cr
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi) **
       (.x1 ↦ᵣ v1_old) ** (.x0 ↦ᵣ 0))
      ((.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ rhat2') ** (.x6 ↦ᵣ d_hi) **
       (.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
  intro hi q0' rhat2' cr
  -- 1. SRLI body
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi) **
       (.x1 ↦ᵣ v1_old) ** (.x0 ↦ᵣ 0))
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi) **
       (.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
    have I0 := srli_spec_gen .x1 .x5 v1_old q0 32 base (by nofun)
    runBlock I0
  -- 2. BEQ at base+4 (keep pure facts)
  have hbeq_raw := beq_spec_gen .x1 .x0 (12 : BitVec 13) hi (0 : Word) (base + 4)
  have hsig : signExtend13 (12 : BitVec 13) = (12 : Word) := by decide
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [hsig]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbeq_raw
  -- 3. Frame BEQ with x5, x11, x6
  have hbeq_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi))
    (by pcFree) hbeq_raw
  -- 4. Extend to full cr
  have hbeq_ext : cpsBranch (base + 4) cr
      (((.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi)))
      (base + 16)
        (((.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi = 0⌝) **
         ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi)))
      (base + 8)
        (((.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi ≠ 0⌝) **
         ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi))) :=
    fun R hR s hcr hPR hpc =>
      hbeq_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show cr (base + 4) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  -- 5. Compose body → BEQ
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_ext
  -- 6. by_cases on hi = 0
  by_cases hcond : hi = 0
  · -- hi = 0 → BEQ taken (skip correction)
    have hq : q0' = q0 := if_pos hcond
    have hr : rhat2' = rhat2 := if_pos hcond
    rw [hq, hr]
    have taken := cpsBranch_elim_taken _ _ _ _ _ _ _ composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp') taken
  · -- hi ≠ 0 → BEQ not-taken (execute correction)
    have hq : q0' = q0 + signExtend12 4095 := if_neg hcond
    have hr : rhat2' = rhat2 + d_hi := if_neg hcond
    rw [hq, hr]
    have ntaken := cpsBranch_elim_ntaken _ _ _ _ _ _ _ composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact hcond ((sepConj_pure_right _ _ _).1 h_x0p).2)
    -- Correction: ADDI + ADD from base+8 to base+16
    have I1 := addi_spec_gen_same .x5 q0 4095 (base + 8) (by nofun)
    have I2 := add_spec_gen_rd_eq_rs1 .x11 .x6 rhat2 d_hi (base + 12) (by nofun)
    have hcorr : cpsTriple (base + 8) (base + 16) cr
        ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ d_hi))
        ((.x5 ↦ᵣ (q0 + signExtend12 4095)) ** (.x11 ↦ᵣ (rhat2 + d_hi)) ** (.x6 ↦ᵣ d_hi)) := by
      runBlock I1 I2
    have hcorr_framed := cpsTriple_frame_left _ _ _ _ _
      ((.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcFree) hcorr
    have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp') ntaken hcorr_framed
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp) full
-- ============================================================================
-- div128 subroutine: Product check 2 section [37]-[44].
-- 8 instructions: LD+MUL+SLLI+LD+OR (body) + BLTU+JAL (branch) + ADDI (correction).
-- BLTU taken → ADDI correction, BLTU ntaken → JAL skip. Both merge at base+32.
-- ============================================================================

set_option maxRecDepth 8192 in
/-- div128 product check 2: compute q0*d_lo vs rhat2*2^32+un0, conditionally correct q0.
    Instrs [37]-[44]. Both BLTU paths merge at base+32. -/
theorem divK_div128_prodcheck2_merged_spec
    (sp q0 rhat2 v1_old v7_old dlo un0 : Word) (base : Word)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_un0 : isValidDwordAccess (sp + signExtend12 3944) = true) :
    let q0_dlo := q0 * dlo
    let rhat2_un0 := (rhat2 <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0 + signExtend12 4095 else q0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 16) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 20) (.BLTU .x1 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 24) (.JAL .x0 8))
       (CodeReq.singleton (base + 28) (.ADDI .x5 .x5 4095))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) **
       (.x7 ↦ᵣ v7_old) ** (.x1 ↦ᵣ v1_old) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ un0) **
       (.x7 ↦ᵣ q0_dlo) ** (.x1 ↦ᵣ rhat2_un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0_dlo rhat2_un0 q0' cr
  -- 1. Body: 5 instructions (LD+MUL+SLLI+LD+OR)
  have hbody : cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) **
       (.x7 ↦ᵣ v7_old) ** (.x1 ↦ᵣ v1_old) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
       (.x7 ↦ᵣ q0_dlo) ** (.x1 ↦ᵣ rhat2_un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
    have I0 := ld_spec_gen .x1 .x12 sp v1_old dlo 3952 base (by nofun) hv_dlo
    have I1 := mul_spec_gen .x7 .x5 .x1 v7_old q0 dlo (base + 4) (by nofun)
    have I2 := slli_spec_gen .x1 .x11 dlo rhat2 32 (base + 8) (by nofun)
    have I3 := ld_spec_gen .x11 .x12 sp rhat2 un0 3944 (base + 12) (by nofun) hv_un0
    have I4 := or_spec_gen_rd_eq_rs1 .x1 .x11 (rhat2 <<< (32 : BitVec 6).toNat) un0 (base + 16) (by nofun)
    runBlock I0 I1 I2 I3 I4
  -- 2. BLTU at base+20
  have hbltu_raw := bltu_spec_gen .x1 .x7 (8 : BitVec 13) rhat2_un0 q0_dlo (base + 20)
  have hsig : signExtend13 (8 : BitVec 13) = (8 : Word) := by decide
  have ha_t : (base + 20) + signExtend13 (8 : BitVec 13) = base + 28 := by rw [hsig]; bv_addr
  have ha_f : (base + 20 : Word) + 4 = base + 24 := by bv_addr
  rw [ha_t, ha_f] at hbltu_raw
  -- 3. Frame BLTU
  have hbltu_framed := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hbltu_raw
  -- 4. Extend to full cr
  have hbltu_ext : cpsBranch (base + 20) cr
      (((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo)) **
       ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
        (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)))
      (base + 28)
        (((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo) ** ⌜BitVec.ult rhat2_un0 q0_dlo⌝) **
         ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
          (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)))
      (base + 24)
        (((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo) ** ⌜¬BitVec.ult rhat2_un0 q0_dlo⌝) **
         ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
          (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))) :=
    fun R hR s hcr hPR hpc =>
      hbltu_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show cr (base + 20) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 20 = base) := by bv_omega
        have h1 : ¬(base + 20 = base + 4) := by bv_omega
        have h2 : ¬(base + 20 = base + 8) := by bv_omega
        have h3 : ¬(base + 20 = base + 12) := by bv_omega
        have h4 : ¬(base + 20 = base + 16) := by bv_omega
        simp only [beq_iff_eq, h0, h1, h2, h3, h4, ↓reduceIte]))) hPR hpc
  -- 5. Compose body → BLTU
  have composed := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbltu_ext
  -- 6. by_cases on BLTU condition
  by_cases hcond : BitVec.ult rhat2_un0 q0_dlo
  · -- BLTU taken: correction (ADDI q0--)
    have hq : q0' = q0 + signExtend12 4095 := if_pos hcond
    rw [hq]
    have taken_br := cpsBranch_elim_taken _ _ _ _ _ _ _ composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    -- Correction: ADDI q0-- from base+28 to base+32
    have I5 := addi_spec_gen_same .x5 q0 4095 (base + 28) (by nofun)
    have hcorr : cpsTriple (base + 28) (base + 32) cr
        (.x5 ↦ᵣ q0)
        (.x5 ↦ᵣ (q0 + signExtend12 4095)) := by
      runBlock I5
    have hcorr_framed := cpsTriple_frame_left _ _ _ _ _
      ((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (by pcFree) hcorr
    have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp')
      taken_br hcorr_framed
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp) full
  · -- BLTU not-taken: JAL skip
    have hq : q0' = q0 := if_neg hcond
    rw [hq]
    have ntaken_br := cpsBranch_elim_ntaken _ _ _ _ _ _ _ composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact absurd ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    -- JAL skip: base+24 → base+32
    have hj : signExtend21 (8 : BitVec 21) = (8 : Word) := by decide
    have I_jal := jal_x0_spec_gen 8 (base + 24)
    rw [hj] at I_jal
    have ha_jal : (base + 24 : Word) + 8 = base + 32 := by bv_addr
    rw [ha_jal] at I_jal
    have hcr_jal : ∀ a i, CodeReq.singleton (base + 24) (.JAL .x0 8) a = some i →
        cr a = some i := by
      intro a i h
      simp only [CodeReq.singleton] at h
      split at h
      · next heq => rw [beq_iff_eq] at heq; subst heq; simp_all [cr, CodeReq.union, CodeReq.singleton]
      · simp at h
    have I_jal_cr := cpsTriple_extend_code hcr_jal I_jal
    have hjal_framed := cpsTriple_frame_left _ _ _ _ _
      ((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo) ** (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) **
       (.x11 ↦ᵣ un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (by pcFree) I_jal_cr
    simp only [sepConj_emp_left'] at hjal_framed
    have ntaken_clean : cpsTriple base (base + 24) cr
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) **
         (.x7 ↦ᵣ v7_old) ** (.x1 ↦ᵣ v1_old) **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
        ((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo) **
         (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) :=
      cpsTriple_consequence _ _ _ _ _ _ _
        (fun h hp => hp)
        (fun h hp => by
          have hp' : (((.x1 ↦ᵣ rhat2_un0) ** (.x7 ↦ᵣ q0_dlo)) **
            ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
             (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))) h :=
            sepConj_mono_left (sepConj_mono_right
              (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
          xperm_hyp hp')
        ntaken_br
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
        (fun _ hp => hp)
        ntaken_clean hjal_framed)
-- ============================================================================
-- div128 subroutine: Step 1 full [10]-[24].
-- 15 instructions: DIVU+MUL+SUB (init) + SRLI+BEQ+ADDI+ADD (clamp q1)
--   + LD+MUL+SLLI+OR+BLTU+JAL+ADDI+ADD (product check 1).
-- ============================================================================

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2048 in
/-- div128 step 1: trial division q1, clamp, product check. Instrs [10]-[24].
    Input: u_hi in x7, d_hi in x6, un1 in x11, dlo in memory.
    Output: refined q1 in x10, refined rhat in x7. -/
theorem divK_div128_step1_spec
    (sp u_hi d_hi un1 v1_old v5_old v10_old dlo : Word) (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 3952) = true) :
    let q1 := rv64_divu u_hi d_hi
    let rhat := u_hi - q1 * d_hi
    let hi := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi = 0 then rhat else rhat + d_hi
    let q_dlo := q1c * dlo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x10 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x5 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x5 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x10 .x10 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 40) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 44) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 48) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 52) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 56) (.ADD .x7 .x7 .x6)))))))))))))))
    cpsTriple base (base + 60) cr
      ((.x7 ↦ᵣ u_hi) ** (.x6 ↦ᵣ d_hi) ** (.x10 ↦ᵣ v10_old) **
       (.x5 ↦ᵣ v5_old) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ v1_old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** (sp + signExtend12 3952 ↦ₘ dlo))
      ((.x7 ↦ᵣ rhat') ** (.x6 ↦ᵣ d_hi) ** (.x10 ↦ᵣ q1') **
       (.x5 ↦ᵣ q_dlo) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ rhat_un1) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** (sp + signExtend12 3952 ↦ₘ dlo)) := by
  intro q1 rhat hi q1c rhatc q_dlo rhat_un1 q1' rhat' cr
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.DIVU .x10 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x5 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x5 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x10 .x10 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 40) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 44) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 48) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 52) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 56) (.ADD .x7 .x7 .x6))))))))))))))) := rfl
  -- Sub-spec 1: init [10]-[12]
  have h1_raw := divK_div128_step1_init_spec u_hi d_hi v5_old v10_old base
  have h1 : cpsTriple base (base + 12) cr _ _ :=
    cpsTriple_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]; exact CodeReq.union_mono_tail (CodeReq.union_mono_tail (CodeReq.union_mono_left _ _)))
  have h1f := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ v1_old) ** (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
     (sp + signExtend12 3952 ↦ₘ dlo))
    (by pcFree) h1
  -- Sub-spec 2: clamp q1 [13]-[16]
  have h2_raw := divK_div128_clamp_q1_merged_spec q1 rhat d_hi (q1 * d_hi) (base + 12)
  have : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  have : (base + 12 : Word) + 8 = base + 20 := by bv_addr
  have : (base + 12 : Word) + 12 = base + 24 := by bv_addr
  have : (base + 12 : Word) + 16 = base + 28 := by bv_addr
  simp only [*] at h2_raw
  have h2 : cpsTriple (base + 12) (base + 28) cr _ _ :=
    cpsTriple_extend_code (h := h2_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
        · split at h
          · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
          · split at h
            · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
            · simp at h)
  have h2f := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ v1_old) ** (.x12 ↦ᵣ sp) **
     (sp + signExtend12 3952 ↦ₘ dlo))
    (by pcFree) h2
  -- Compose blocks 1 → 2
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1f h2f
  -- Sub-spec 3: prodcheck1 [17]-[24]
  have h3_raw := divK_div128_prodcheck1_merged_spec sp q1c rhatc d_hi un1
    v1_old hi dlo (base + 28) hv
  have : (base + 28 : Word) + 4 = base + 32 := by bv_addr
  have : (base + 28 : Word) + 8 = base + 36 := by bv_addr
  have : (base + 28 : Word) + 12 = base + 40 := by bv_addr
  have : (base + 28 : Word) + 16 = base + 44 := by bv_addr
  have : (base + 28 : Word) + 20 = base + 48 := by bv_addr
  have : (base + 28 : Word) + 24 = base + 52 := by bv_addr
  have : (base + 28 : Word) + 28 = base + 56 := by bv_addr
  have : (base + 28 : Word) + 32 = base + 60 := by bv_addr
  simp only [*] at h3_raw
  have h3 : cpsTriple (base + 28) (base + 60) cr _ _ :=
    cpsTriple_extend_code (h := h3_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
        · split at h
          · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
          · split at h
            · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
            · split at h
              · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
              · split at h
                · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                · split at h
                  · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                  · split at h
                    · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                    · simp at h)
  have h3f := cpsTriple_frame_left _ _ _ _ _
    ((.x0 ↦ᵣ 0))
    (by pcFree) h3
  -- Compose blocks 1→2 → 3
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 h3f
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    h123
-- ============================================================================
-- div128 subroutine: Step 2 full [30]-[44].
-- 15 instructions: DIVU+MUL+SUB (init) + SRLI+BEQ+ADDI+ADD (clamp q0)
--   + LD+MUL+SLLI+LD+OR+BLTU+JAL+ADDI (product check 2).
-- ============================================================================

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2048 in
/-- div128 step 2: trial division q0, clamp, product check. Instrs [30]-[44].
    Input: un21 in x7, d_hi in x6, dlo/un0 in memory.
    Output: refined q0 in x5. -/
theorem divK_div128_step2_spec
    (sp un21 d_hi v1_old v5_old v11_old dlo un0 : Word) (base : Word)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_un0 : isValidDwordAccess (sp + signExtend12 3944) = true) :
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * dlo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 44) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 48) (.BLTU .x1 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 52) (.JAL .x0 8))
       (CodeReq.singleton (base + 56) (.ADDI .x5 .x5 4095)))))))))))))))
    cpsTriple base (base + 60) cr
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ d_hi) ** (.x5 ↦ᵣ v5_old) **
       (.x1 ↦ᵣ v1_old) ** (.x11 ↦ᵣ v11_old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x7 ↦ᵣ q0_dlo) ** (.x6 ↦ᵣ d_hi) ** (.x5 ↦ᵣ q0') **
       (.x1 ↦ᵣ rhat2_un0) ** (.x11 ↦ᵣ un0) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0 rhat2 hi q0c rhat2c q0_dlo rhat2_un0 q0' cr
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 44) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 48) (.BLTU .x1 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 52) (.JAL .x0 8))
       (CodeReq.singleton (base + 56) (.ADDI .x5 .x5 4095))))))))))))))) := rfl
  -- Sub-spec 1: init [30]-[32]
  have h1_raw := divK_div128_step2_init_spec un21 d_hi v1_old v5_old v11_old base
  have h1 : cpsTriple base (base + 12) cr _ _ :=
    cpsTriple_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]; exact CodeReq.union_mono_tail (CodeReq.union_mono_tail (CodeReq.union_mono_left _ _)))
  have h1f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) h1
  -- Sub-spec 2: clamp q0 [33]-[36]
  have h2_raw := divK_div128_clamp_q0_merged_spec q0 rhat2 d_hi (q0 * d_hi) (base + 12)
  have : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  have : (base + 12 : Word) + 8 = base + 20 := by bv_addr
  have : (base + 12 : Word) + 12 = base + 24 := by bv_addr
  have : (base + 12 : Word) + 16 = base + 28 := by bv_addr
  simp only [*] at h2_raw
  have h2 : cpsTriple (base + 12) (base + 28) cr _ _ :=
    cpsTriple_extend_code (h := h2_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
        · split at h
          · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
          · split at h
            · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
            · simp at h)
  have h2f := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ un21) ** (.x12 ↦ᵣ sp) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) h2
  -- Compose blocks 1 → 2
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1f h2f
  -- Sub-spec 3: prodcheck2 [37]-[44]
  have h3_raw := divK_div128_prodcheck2_merged_spec sp q0c rhat2c hi
    un21 dlo un0 (base + 28) hv_dlo hv_un0
  have : (base + 28 : Word) + 4 = base + 32 := by bv_addr
  have : (base + 28 : Word) + 8 = base + 36 := by bv_addr
  have : (base + 28 : Word) + 12 = base + 40 := by bv_addr
  have : (base + 28 : Word) + 16 = base + 44 := by bv_addr
  have : (base + 28 : Word) + 20 = base + 48 := by bv_addr
  have : (base + 28 : Word) + 24 = base + 52 := by bv_addr
  have : (base + 28 : Word) + 28 = base + 56 := by bv_addr
  have : (base + 28 : Word) + 32 = base + 60 := by bv_addr
  simp only [*] at h3_raw
  have h3 : cpsTriple (base + 28) (base + 60) cr _ _ :=
    cpsTriple_extend_code (h := h3_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
        · split at h
          · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
          · split at h
            · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
            · split at h
              · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
              · split at h
                · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                · split at h
                  · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                  · split at h
                    · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                    · simp at h)
  have h3f := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ d_hi) ** (.x0 ↦ᵣ 0))
    (by pcFree) h3
  -- Compose blocks 1→2 → 3
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 h3f
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    h123
-- ============================================================================
-- div128 subroutine: Phase 1 [0]-[9] — save ret/d, split d and u_lo.
-- 10 instructions: SD+SD+SRLI+SLLI+SRLI+SD + SRLI+SLLI+SRLI+SD.
-- ============================================================================

set_option maxRecDepth 2048 in
/-- div128 Phase 1: save return addr/d, split d and u_lo. Instrs [0]-[9].
    Input: x12=sp, x2=ret_addr, x10=d, x5=u_lo, x7=u_hi.
    Output: x6=d_hi, x11=un1, x5=un0 (saved), x7=u_hi (unchanged). -/
theorem divK_div128_phase1_spec
    (sp ret_addr d u_lo u_hi v1_old v6_old v11_old
     ret_mem d_mem dlo_mem un0_mem : Word) (base : Word)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_un0 : isValidDwordAccess (sp + signExtend12 3944) = true) :
    let d_hi := d >>> (32 : BitVec 6).toNat
    let d_lo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let un1 := u_lo >>> (32 : BitVec 6).toNat
    let un0 := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SD .x12 .x2 3968))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SD .x12 .x10 3960))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SRLI .x6 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLLI .x1 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SRLI .x1 .x1 32))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x1 3952))
      (CodeReq.union (CodeReq.singleton (base + 24) (.SRLI .x11 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SLLI .x5 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 32) (.SRLI .x5 .x5 32))
       (CodeReq.singleton (base + 36) (.SD .x12 .x5 3944))))))))))
    cpsTriple base (base + 40) cr
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x6 ↦ᵣ v6_old) ** (.x1 ↦ᵣ v1_old) ** (.x5 ↦ᵣ u_lo) **
       (.x11 ↦ᵣ v11_old) ** (.x7 ↦ᵣ u_hi) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ un0_mem))
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x6 ↦ᵣ d_hi) ** (.x1 ↦ᵣ d_lo) ** (.x5 ↦ᵣ un0) **
       (.x11 ↦ᵣ un1) ** (.x7 ↦ᵣ u_hi) **
       (sp + signExtend12 3968 ↦ₘ ret_addr) **
       (sp + signExtend12 3960 ↦ₘ d) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro d_hi d_lo un1 un0 cr
  -- Instructions from save_split_d (6 instrs at base)
  have I0 := sd_spec_gen .x12 .x2 sp ret_addr ret_mem 3968 base hv_ret
  have I1 := sd_spec_gen .x12 .x10 sp d d_mem 3960 (base + 4) hv_d
  have I2 := srli_spec_gen .x6 .x10 v6_old d 32 (base + 8) (by nofun)
  have I3 := slli_spec_gen .x1 .x10 v1_old d 32 (base + 12) (by nofun)
  have I4 := srli_spec_gen_same .x1 (d <<< (32 : BitVec 6).toNat) 32 (base + 16) (by nofun)
  have I5 := sd_spec_gen .x12 .x1 sp d_lo dlo_mem 3952 (base + 20) hv_dlo
  -- Instructions from split_ulo (4 instrs at base+24)
  have I6 := srli_spec_gen .x11 .x5 v11_old u_lo 32 (base + 24) (by nofun)
  have I7 := slli_spec_gen_same .x5 u_lo 32 (base + 28) (by nofun)
  have I8 := srli_spec_gen_same .x5 (u_lo <<< (32 : BitVec 6).toNat) 32 (base + 32) (by nofun)
  have I9 := sd_spec_gen .x12 .x5 sp un0 un0_mem 3944 (base + 36) hv_un0
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9
-- ============================================================================
-- div128 subroutine: End phase [45]-[48] — combine q + restore/return.
-- 4 instructions: SLLI + OR + LD + JALR.
-- ============================================================================

set_option maxRecDepth 2048 in
/-- div128 end phase: combine q1,q0 into q, restore return addr, return.
    Instrs [45]-[48]. Exit to ret_addr. -/
theorem divK_div128_end_spec
    (sp q1 q0 v2_old v11_old ret_addr : Word) (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 3968) = true)
    (halign : (ret_addr + signExtend12 0) &&& ~~~1 = ret_addr) :
    let q1_hi := q1 <<< (32 : BitVec 6).toNat
    let q := q1_hi ||| q0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x11 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.OR .x11 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x2 .x12 3968))
       (CodeReq.singleton (base + 12) (.JALR .x0 .x2 0))))
    cpsTriple base ret_addr cr
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ v11_old) **
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2_old) ** (sp + signExtend12 3968 ↦ₘ ret_addr))
      ((.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ q) **
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (sp + signExtend12 3968 ↦ₘ ret_addr)) := by
  intro q1_hi q cr
  -- Instructions from combine_q (2 instrs at base)
  have I0 := slli_spec_gen .x11 .x10 v11_old q1 32 base (by nofun)
  have I1 := or_spec_gen_rd_eq_rs1 .x11 .x5 q1_hi q0 (base + 4) (by nofun)
  -- Instructions from restore_return (2 instrs at base+8)
  have I2 := ld_spec_gen .x2 .x12 sp v2_old ret_addr 3968 (base + 8) (by nofun) hv
  have I3 := jalr_x0_spec_gen .x2 ret_addr 0 (base + 12)
  rw [halign] at I3
  runBlock I0 I1 I2 I3
-- ============================================================================
-- Composed per-limb specs: mulsub_limb, addback_limb.
-- These compose partA+partB into single per-limb operations.
-- ============================================================================

set_option maxRecDepth 2048 in
/-- Mul-sub full limb: partA (6 instrs) + partB (5 instrs) = 11 instructions.
    Input: q_hat (x11), carry_in (x10), v[i] and u[j+i] in memory.
    Output: carry_out (x10), u_new stored. -/
theorem divK_mulsub_limb_spec
    (sp u_base q_hat carry_in v5_old v7_old v2_old v_i u_i : Word)
    (v_off u_off : BitVec 12) (base : Word)
    (hv_v : isValidDwordAccess (sp + signExtend12 v_off) = true)
    (hv_u : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let prod_lo := q_hat * v_i
    let prod_hi := rv64_mulhu q_hat v_i
    let full_sub := prod_lo + carry_in
    let borrow_add := if BitVec.ult full_sub carry_in then (1 : Word) else 0
    let partial_carry := borrow_add + prod_hi
    let borrow_sub := if BitVec.ult u_i full_sub then (1 : Word) else 0
    let u_new := u_i - full_sub
    let carry_out := partial_carry + borrow_sub
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.MULHU .x5 .x11 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADD .x7 .x7 .x10))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x10 .x7 .x10))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADD .x10 .x10 .x5))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SLTU .x5 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 32) (.SUB .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 36) (.ADD .x10 .x10 .x5))
       (CodeReq.singleton (base + 40) (.SD .x6 .x2 u_off)))))))))))
    cpsTriple base (base + 44) cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ carry_in) **
       (.x6 ↦ᵣ u_base) ** (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ carry_out) **
       (.x6 ↦ᵣ u_base) ** (.x5 ↦ᵣ borrow_sub) ** (.x7 ↦ᵣ full_sub) **
       (.x2 ↦ᵣ u_new) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro prod_lo prod_hi full_sub borrow_add partial_carry borrow_sub u_new carry_out cr
  -- Instructions from partA (6 instrs at base)
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun) hv_v
  have I1 := mul_spec_gen .x7 .x11 .x5 v7_old q_hat v_i (base + 4) (by nofun)
  have I2 := mulhu_spec_gen_rd_eq_rs2 .x5 .x11 q_hat v_i (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs1 .x7 .x10 prod_lo carry_in (base + 12) (by nofun)
  have I4 := sltu_spec_gen_rd_eq_rs2 .x10 .x7 full_sub carry_in (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1 .x10 .x5 borrow_add prod_hi (base + 20) (by nofun)
  -- Instructions from partB (5 instrs at base+24)
  have I6 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off (base + 24) (by nofun) hv_u
  have I7 := sltu_spec_gen .x5 .x2 .x7 prod_hi u_i full_sub (base + 28) (by nofun)
  have I8 := sub_spec_gen_rd_eq_rs1 .x2 .x7 u_i full_sub (base + 32) (by nofun)
  have I9 := add_spec_gen_rd_eq_rs1 .x10 .x5 partial_carry borrow_sub (base + 36) (by nofun)
  have I10 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 40) hv_u
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10
set_option maxRecDepth 2048 in
/-- Add-back full limb: partA (5 instrs) + partB (3 instrs) = 8 instructions.
    Input: carry_in (x7), v[i] and u[j+i] in memory.
    Output: carry_out (x7), u_new stored. -/
theorem divK_addback_limb_spec
    (sp u_base carry_in v5_old v2_old v_i u_i : Word)
    (v_off u_off : BitVec 12) (base : Word)
    (hv_v : isValidDwordAccess (sp + signExtend12 v_off) = true)
    (hv_u : isValidDwordAccess (u_base + signExtend12 u_off) = true) :
    let u_plus_carry := u_i + carry_in
    let carry1 := if BitVec.ult u_plus_carry carry_in then (1 : Word) else 0
    let u_new := u_plus_carry + v_i
    let carry2 := if BitVec.ult u_new v_i then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 v_off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x2 .x6 u_off))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x2 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x7 .x2 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.ADD .x2 .x2 .x5))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SLTU .x5 .x2 .x5))
      (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x7 .x7 .x5))
       (CodeReq.singleton (base + 28) (.SD .x6 .x2 u_off))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_in) **
       (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_i))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ carry_out) **
       (.x5 ↦ᵣ carry2) ** (.x2 ↦ᵣ u_new) **
       ((sp + signExtend12 v_off) ↦ₘ v_i) **
       ((u_base + signExtend12 u_off) ↦ₘ u_new)) := by
  intro u_plus_carry carry1 u_new carry2 carry_out cr
  -- Instructions from partA (5 instrs at base)
  have I0 := ld_spec_gen .x5 .x12 sp v5_old v_i v_off base (by nofun) hv_v
  have I1 := ld_spec_gen .x2 .x6 u_base v2_old u_i u_off (base + 4) (by nofun) hv_u
  have I2 := add_spec_gen_rd_eq_rs1 .x2 .x7 u_i carry_in (base + 8) (by nofun)
  have I3 := sltu_spec_gen_rd_eq_rs2 .x7 .x2 u_plus_carry carry_in (base + 12) (by nofun)
  have I4 := add_spec_gen_rd_eq_rs1 .x2 .x5 u_plus_carry v_i (base + 16) (by nofun)
  -- Instructions from partB (3 instrs at base+20)
  have I5 := sltu_spec_gen_rd_eq_rs2 .x5 .x2 u_new v_i (base + 20) (by nofun)
  have I6 := or_spec_gen_rd_eq_rs1 .x7 .x5 carry1 carry2 (base + 24) (by nofun)
  have I7 := sd_spec_gen .x6 .x2 u_base u_new u_i u_off (base + 28) hv_u
  runBlock I0 I1 I2 I3 I4 I5 I6 I7
-- ============================================================================
-- Trial quotient load phase: load u[j+n], u[j+n-1], v_top = b[n-1].
-- trial_load_u [1]-[7] + trial_load_vtop [8]-[12] = 12 instructions.
-- ============================================================================

set_option maxRecDepth 2048 in
/-- Trial quotient load: fetch u_hi, u_lo, v_top from memory.
    Instrs [1]-[12] of loop body.
    Output: x7 = u_hi, x5 = u_lo, x10 = v_top, x6 = vtop_base. -/
theorem divK_trial_load_spec
    (sp j n v5_old v6_old v7_old v10_old u_hi u_lo v_top : Word)
    (base : Word)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true) :
    let u_addr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtop_base := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x7 .x1 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x7 .x7 3))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADDI .x5 .x12 4056))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x5 0))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x5 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x6 .x12 3984))
      (CodeReq.union (CodeReq.singleton (base + 32) (.ADDI .x6 .x6 4095))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x6 .x6 3))
      (CodeReq.union (CodeReq.singleton (base + 40) (.ADD .x6 .x12 .x6))
       (CodeReq.singleton (base + 44) (.LD .x10 .x6 32))))))))))))
    cpsTriple base (base + 48) cr
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u_lo) ** (.x6 ↦ᵣ vtop_base) **
       (.x7 ↦ᵣ u_hi) ** (.x10 ↦ᵣ v_top) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top)) := by
  intro u_addr vtop_base cr
  -- Instructions from trial_load_u (7 instrs at base)
  let jpn := j + n
  let jpn_x8 := jpn <<< (3 : BitVec 6).toNat
  let u0_base := sp + signExtend12 4056
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr0 : u_addr + signExtend12 (0 : BitVec 12) = u_addr := by rw [hse0]; bv_omega
  have hv_uhi' : isValidDwordAccess (u_addr + signExtend12 0) = true := by rw [haddr0]; exact hv_uhi
  have I0 := ld_spec_gen .x5 .x12 sp v5_old n 3984 base (by nofun) hv_n1
  have I1 := add_spec_gen .x7 .x1 .x5 j n v7_old (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x7 jpn 3 (base + 8) (by nofun)
  have I3 := addi_spec_gen .x5 .x12 n sp 4056 (base + 12) (by nofun)
  have I4 := sub_spec_gen_rd_eq_rs1 .x5 .x7 u0_base jpn_x8 (base + 16) (by nofun)
  have I5 := ld_spec_gen .x7 .x5 u_addr jpn_x8 u_hi 0 (base + 20) (by nofun) hv_uhi'
  rw [haddr0] at I5
  have I6 := ld_spec_gen_same .x5 u_addr u_lo 8 (base + 24) (by nofun) hv_ulo
  -- Instructions from trial_load_vtop (5 instrs at base+28)
  let nm1 := n + signExtend12 4095
  let nm1_x8 := nm1 <<< (3 : BitVec 6).toNat
  have I7 := ld_spec_gen .x6 .x12 sp v6_old n 3984 (base + 28) (by nofun) hv_n1
  have I8 := addi_spec_gen_same .x6 n 4095 (base + 32) (by nofun)
  have I9 := slli_spec_gen_same .x6 nm1 3 (base + 36) (by nofun)
  have I10 := add_spec_gen_rd_eq_rs2 .x6 .x12 sp nm1_x8 (base + 40) (by nofun)
  have I11 := ld_spec_gen .x10 .x6 vtop_base v10_old v_top 32 (base + 44) (by nofun) hv_vtop
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11
-- ============================================================================
-- Composed store q[j]: addr computation + SD = 4 instructions.
-- ============================================================================

set_option maxRecDepth 2048 in
/-- Store q[j]: compute address and store q_hat. 4 instructions.
    q_addr = sp + 4088 - j*8. -/
theorem divK_store_qj_spec (sp j q_hat v5_old v7_old q_old : Word)
    (base : Word)
    (hv : isValidDwordAccess (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat) = true) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - j_x8
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLLI .x5 .x1 3))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x7 .x12 4088))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5))
       (CodeReq.singleton (base + 12) (.SD .x7 .x11 0))))
    cpsTriple base (base + 16) cr
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) **
       (q_addr ↦ₘ q_old))
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr) **
       (q_addr ↦ₘ q_hat)) := by
  intro j_x8 q_addr cr
  -- Instructions from store_qj_addr (3 instrs at base)
  have I0 := slli_spec_gen .x5 .x1 v5_old j 3 base (by nofun)
  have I1 := addi_spec_gen .x7 .x12 v7_old sp 4088 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1 .x7 .x5 (sp + signExtend12 4088) j_x8 (base + 8) (by nofun)
  -- SD instruction with signExtend12 normalization
  have hse : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr : q_addr + signExtend12 (0 : BitVec 12) = q_addr := by rw [hse]; bv_omega
  have hv' : isValidDwordAccess (q_addr + signExtend12 0) = true := by rw [haddr]; exact hv
  have I3 := sd_spec_gen .x7 .x11 q_addr q_hat q_old 0 (base + 12) hv'
  rw [haddr] at I3
  runBlock I0 I1 I2 I3
end EvmAsm.Evm64
