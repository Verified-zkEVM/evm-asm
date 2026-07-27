/-
  EvmAsm.Evm64.AddMod.Compose.CarryBlockSpecs

  Per-block `cpsTripleWithin` leaf specs for the straight-line carry-path
  blocks of `evm_addmod_total` (issue #9704, Phase 3):

    * `evm_addmod_carry_save_operands`  — park N → S1, r → S2
    * `evm_addmod_carry_minus_one_args` — materialize 2^256−1 in F+0..24
    * `evm_addmod_carry_call_mod`       — JAL enter / ADDI −32 restore
    * `evm_addmod_carry_plus_one_args`  — (−1 mod N)+1 → F+0..24, reload N
    * `evm_addmod_carry_stage_low_args` — park m → S3, reload r and N
    * `evm_addmod_carry_mod_add_stage`  — m ← S3 into F+0..24

  Scratch-cell map (F = the post-prologue `x12`, i.e. `sp + 32`):

    S1 = F + signExtend12 3904..3928  (F − 192..−168)  saved `N`
    S2 = F + signExtend12 3872..3896  (F − 224..−200)  saved `r`
    S3 = F + signExtend12 3840..3864  (F − 256..−232)  parked `m`

  All specs follow the AddMod house style (`LimbSpec.lean`): stated over a
  union-of-singletons `_code` handle with a `_code_eq_ofProg` bridge, proven
  by per-instruction `*_spec_gen_within` leaves composed with `runBlock`.
  The branch-free conditional subtract (`evm_addmod_carry_cond_sub`) lives
  in `Compose/CondSubSpec.lean`.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Evm64.AddMod.Program

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64
open EvmAsm.Evm64

-- ============================================================================
-- evm_addmod_carry_save_operands (16 instructions)
-- ============================================================================

abbrev evm_addmod_carry_save_operands_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 (32 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SD .x12 .x5 (3904 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x5 .x12 (40 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x5 (3912 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x5 .x12 (48 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x5 (3920 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x5 .x12 (56 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SD .x12 .x5 (3928 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 32) (.LD .x5 .x12 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 36) (.SD .x12 .x5 (3872 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x5 .x12 (8 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 44) (.SD .x12 .x5 (3880 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 48) (.LD .x5 .x12 (16 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 52) (.SD .x12 .x5 (3888 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 56) (.LD .x5 .x12 (24 : BitVec 12)))
   (CodeReq.singleton (base + 60) (.SD .x12 .x5 (3896 : BitVec 12)))))))))))))))))

theorem evm_addmod_carry_save_operands_code_eq_ofProg (base : Word) :
    evm_addmod_carry_save_operands_code base =
      CodeReq.ofProg base evm_addmod_carry_save_operands := by
  unfold evm_addmod_carry_save_operands_code evm_addmod_carry_save_operands
    LD SD single seq
  change _ = CodeReq.ofProg base
    [.LD .x5 .x12 32, .SD .x12 .x5 3904, .LD .x5 .x12 40, .SD .x12 .x5 3912,
     .LD .x5 .x12 48, .SD .x12 .x5 3920, .LD .x5 .x12 56, .SD .x12 .x5 3928,
     .LD .x5 .x12 0, .SD .x12 .x5 3872, .LD .x5 .x12 8, .SD .x12 .x5 3880,
     .LD .x5 .x12 16, .SD .x12 .x5 3888, .LD .x5 .x12 24, .SD .x12 .x5 3896]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right, BitVec.add_assoc, BitVec.reduceAdd]
  rfl

/-- Carry path — park the live operands: `N` (at `F + 32..56`) → S1 and the
    truncated sum `r` (at `F + 0..24`) → S2. `x5` ends holding the last
    copied limb `r3`. -/
theorem evm_addmod_carry_save_operands_spec_within
    (sp base x5Old : Word) (n0 n1 n2 n3 r0 r1 r2 r3 : Word)
    (p0 p1 p2 p3 q0 q1 q2 q3 : Word) :
    cpsTripleWithin 16 base (base + 64)
      (evm_addmod_carry_save_operands_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (3904 : BitVec 12)) ↦ₘ p0) **
       ((sp + signExtend12 (3912 : BitVec 12)) ↦ₘ p1) **
       ((sp + signExtend12 (3920 : BitVec 12)) ↦ₘ p2) **
       ((sp + signExtend12 (3928 : BitVec 12)) ↦ₘ p3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ q0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ q1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ q2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ q3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3928 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ r3)) := by
  have L0 := ld_spec_gen_within .x5 .x12 sp x5Old n0 32 base (by nofun)
  have S0 := sd_spec_gen_within .x12 .x5 sp n0 p0 3904 (base + 4)
  have L1 := ld_spec_gen_within .x5 .x12 sp n0 n1 40 (base + 8) (by nofun)
  have S1 := sd_spec_gen_within .x12 .x5 sp n1 p1 3912 (base + 12)
  have L2 := ld_spec_gen_within .x5 .x12 sp n1 n2 48 (base + 16) (by nofun)
  have S2 := sd_spec_gen_within .x12 .x5 sp n2 p2 3920 (base + 20)
  have L3 := ld_spec_gen_within .x5 .x12 sp n2 n3 56 (base + 24) (by nofun)
  have S3 := sd_spec_gen_within .x12 .x5 sp n3 p3 3928 (base + 28)
  have L4 := ld_spec_gen_within .x5 .x12 sp n3 r0 0 (base + 32) (by nofun)
  have S4 := sd_spec_gen_within .x12 .x5 sp r0 q0 3872 (base + 36)
  have L5 := ld_spec_gen_within .x5 .x12 sp r0 r1 8 (base + 40) (by nofun)
  have S5 := sd_spec_gen_within .x12 .x5 sp r1 q1 3880 (base + 44)
  have L6 := ld_spec_gen_within .x5 .x12 sp r1 r2 16 (base + 48) (by nofun)
  have S6 := sd_spec_gen_within .x12 .x5 sp r2 q2 3888 (base + 52)
  have L7 := ld_spec_gen_within .x5 .x12 sp r2 r3 24 (base + 56) (by nofun)
  have S7 := sd_spec_gen_within .x12 .x5 sp r3 q3 3896 (base + 60)
  runBlock L0 S0 L1 S1 L2 S2 L3 S3 L4 S4 L5 S5 L6 S6 L7 S7

-- ============================================================================
-- evm_addmod_carry_minus_one_args (5 instructions)
-- ============================================================================

abbrev evm_addmod_carry_minus_one_args_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x5 .x0 (4095 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SD .x12 .x5 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SD .x12 .x5 (8 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x5 (16 : BitVec 12)))
   (CodeReq.singleton (base + 16) (.SD .x12 .x5 (24 : BitVec 12))))))

theorem evm_addmod_carry_minus_one_args_code_eq_ofProg (base : Word) :
    evm_addmod_carry_minus_one_args_code base =
      CodeReq.ofProg base evm_addmod_carry_minus_one_args := by
  unfold evm_addmod_carry_minus_one_args_code evm_addmod_carry_minus_one_args
    ADDI SD single seq
  change _ = CodeReq.ofProg base
    [.ADDI .x5 .x0 4095, .SD .x12 .x5 0, .SD .x12 .x5 8,
     .SD .x12 .x5 16, .SD .x12 .x5 24]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right, BitVec.add_assoc, BitVec.reduceAdd]
  rfl

/-- Carry path — materialize the all-ones dividend `2^256 − 1` in the MOD
    frame dividend slots `F + 0..24` (`signExtend12 4095 = −1`, the all-ones
    64-bit word). -/
theorem evm_addmod_carry_minus_one_args_spec_within
    (sp base x5Old : Word) (w0 w1 w2 w3 : Word) :
    cpsTripleWithin 5 base (base + 20)
      (evm_addmod_carry_minus_one_args_code base)
      ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ x5Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ w0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ w1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ w2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ w3))
      ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12))) := by
  have I := addi_x0_spec_gen_within .x5 x5Old 4095 base (by nofun)
  have S0 := sd_spec_gen_within .x12 .x5 sp
    (signExtend12 (4095 : BitVec 12)) w0 0 (base + 4)
  have S1 := sd_spec_gen_within .x12 .x5 sp
    (signExtend12 (4095 : BitVec 12)) w1 8 (base + 8)
  have S2 := sd_spec_gen_within .x12 .x5 sp
    (signExtend12 (4095 : BitVec 12)) w2 16 (base + 12)
  have S3 := sd_spec_gen_within .x12 .x5 sp
    (signExtend12 (4095 : BitVec 12)) w3 24 (base + 16)
  runBlock I S0 S1 S2 S3

-- ============================================================================
-- evm_addmod_carry_call_mod (2 instructions: JAL enter + ADDI restore)
-- ============================================================================
--
-- The two instructions cannot form one straight-line triple (control leaves
-- through the callable between them), so they get separate leaf specs; the
-- composition threads the callable spec in between (mirroring
-- `evm_addmod_pow256_call_mod_enter/restore`).

abbrev evm_addmod_carry_call_mod_code (base : Word) (modOff : BitVec 21) :
    CodeReq :=
  CodeReq.union (CodeReq.singleton base (.JAL .x1 modOff))
    (CodeReq.singleton (base + 4) (.ADDI .x12 .x12 (4064 : BitVec 12)))

theorem evm_addmod_carry_call_mod_code_eq_ofProg (base : Word)
    (modOff : BitVec 21) :
    evm_addmod_carry_call_mod_code base modOff =
      CodeReq.ofProg base (evm_addmod_carry_call_mod modOff) := by
  unfold evm_addmod_carry_call_mod_code evm_addmod_carry_call_mod
    JAL ADDI single seq
  change _ = CodeReq.ofProg base [.JAL .x1 modOff, .ADDI .x12 .x12 4064]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_singleton]

/-- Carry path — enter one helper MOD call: `JAL x1, modOff` into the
    appended `evm_mod_callable_v5`. -/
theorem evm_addmod_carry_call_mod_enter_spec_within
    (x1Old base : Word) (modOff : BitVec 21) :
    cpsTripleWithin 1 base (base + signExtend21 modOff)
      (CodeReq.singleton base (.JAL .x1 modOff))
      (.x1 ↦ᵣ x1Old)
      (.x1 ↦ᵣ (base + 4)) :=
  jal_spec_within .x1 x1Old modOff base (by nofun)

/-- Carry path — restore the shared MOD frame base after a callable return:
    `ADDI x12, x12, −32` (immediate 4064). -/
theorem evm_addmod_carry_call_mod_restore_spec_within
    (sp base : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.ADDI .x12 .x12 (4064 : BitVec 12)))
      (.x12 ↦ᵣ sp)
      (.x12 ↦ᵣ (sp + signExtend12 (4064 : BitVec 12))) :=
  addi_spec_gen_same_within .x12 sp 4064 base (by nofun)

-- ============================================================================
-- evm_addmod_carry_plus_one_args (24 instructions)
-- ============================================================================

abbrev evm_addmod_carry_plus_one_args_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 (32 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x6 .x5 (1 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SLTIU .x7 .x6 (1 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x6 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x5 .x12 (40 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 20) (.ADD .x6 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SLTU .x7 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SD .x12 .x6 (8 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 32) (.LD .x5 .x12 (48 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 36) (.ADD .x6 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SLTU .x7 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 44) (.SD .x12 .x6 (16 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 48) (.LD .x5 .x12 (56 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 52) (.ADD .x6 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 56) (.SLTU .x7 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 60) (.SD .x12 .x6 (24 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 64) (.LD .x5 .x12 (3904 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 68) (.SD .x12 .x5 (32 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 72) (.LD .x5 .x12 (3912 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 76) (.SD .x12 .x5 (40 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 80) (.LD .x5 .x12 (3920 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 84) (.SD .x12 .x5 (48 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 88) (.LD .x5 .x12 (3928 : BitVec 12)))
   (CodeReq.singleton (base + 92) (.SD .x12 .x5 (56 : BitVec 12)))))))))))))))))))))))))

theorem evm_addmod_carry_plus_one_args_code_eq_ofProg (base : Word) :
    evm_addmod_carry_plus_one_args_code base =
      CodeReq.ofProg base evm_addmod_carry_plus_one_args := by
  unfold evm_addmod_carry_plus_one_args_code evm_addmod_carry_plus_one_args
    LD SD ADDI ADD SLTU SLTIU single seq
  change _ = CodeReq.ofProg base
    [.LD .x5 .x12 32, .ADDI .x6 .x5 1, .SLTIU .x7 .x6 1, .SD .x12 .x6 0,
     .LD .x5 .x12 40, .ADD .x6 .x5 .x7, .SLTU .x7 .x6 .x7, .SD .x12 .x6 8,
     .LD .x5 .x12 48, .ADD .x6 .x5 .x7, .SLTU .x7 .x6 .x7, .SD .x12 .x6 16,
     .LD .x5 .x12 56, .ADD .x6 .x5 .x7, .SLTU .x7 .x6 .x7, .SD .x12 .x6 24,
     .LD .x5 .x12 3904, .SD .x12 .x5 32, .LD .x5 .x12 3912, .SD .x12 .x5 40,
     .LD .x5 .x12 3920, .SD .x12 .x5 48, .LD .x5 .x12 3928, .SD .x12 .x5 56]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right, BitVec.add_assoc, BitVec.reduceAdd]
  rfl

/-- Plus-one chunk (limb 0): load the low remainder limb from `F + 32`,
    add one, detect wrap via `SLTIU`, store to `F + 0`. Raw-expression
    post (no lets) so downstream `runBlock` joins match syntactically. -/
theorem evm_addmod_carry_plus_one_low_spec_within
    (sp base x5Old x6Old x7Old m0 w0 : Word) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 (32 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x6 .x5 (1 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTIU .x7 .x6 (1 : BitVec 12)))
       (CodeReq.singleton (base + 12) (.SD .x12 .x6 (0 : BitVec 12))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ w0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ m0) **
       (.x6 ↦ᵣ (m0 + signExtend12 (1 : BitVec 12))) **
       (.x7 ↦ᵣ (if BitVec.ult (m0 + signExtend12 (1 : BitVec 12))
          (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0)) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
          (m0 + signExtend12 (1 : BitVec 12)))) := by
  have L := ld_spec_gen_within .x5 .x12 sp x5Old m0 32 base (by nofun)
  have A := addi_spec_gen_within .x6 .x5 x6Old m0 1 (base + 4) (by nofun)
  have C := sltiu_spec_gen_within .x7 .x6 x7Old
    (m0 + signExtend12 (1 : BitVec 12)) 1 (base + 8) (by nofun)
  have S := sd_spec_gen_within .x12 .x6 sp
    (m0 + signExtend12 (1 : BitVec 12)) w0 0 (base + 12)
  runBlock L A C S

/-- Plus-one chunk (limbs 1–3, offset-generic): load the next remainder limb
    from `F + offM`, add the incoming carry, propagate via `SLTU`, store to
    `F + offW`. `carryIn` is a parameter, so instantiation keeps expression
    depth shallow at each composition site. -/
theorem evm_addmod_carry_plus_one_limb_spec_within (offM offW : BitVec 12)
    (sp base x5Old x6Old carryIn m w : Word) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 offM))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x6 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x7 .x6 .x7))
       (CodeReq.singleton (base + 12) (.SD .x12 .x6 offW)))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ carryIn) **
       ((sp + signExtend12 offM) ↦ₘ m) **
       ((sp + signExtend12 offW) ↦ₘ w))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ m) ** (.x6 ↦ᵣ (m + carryIn)) **
       (.x7 ↦ᵣ (if BitVec.ult (m + carryIn) carryIn then (1 : Word) else 0)) **
       ((sp + signExtend12 offM) ↦ₘ m) **
       ((sp + signExtend12 offW) ↦ₘ (m + carryIn))) := by
  have L := ld_spec_gen_within .x5 .x12 sp x5Old m offM base (by nofun)
  have A := add_spec_gen_within .x6 .x5 .x7 m carryIn x6Old (base + 4) (by nofun)
  have C := sltu_spec_gen_rd_eq_rs2_within .x7 .x6 (m + carryIn) carryIn
    (base + 8) (by nofun)
  have S := sd_spec_gen_within .x12 .x6 sp (m + carryIn) w offW (base + 12)
  runBlock L A C S

/-- Plus-one chunk (N reload): copy the parked `N` from S1 back into the
    divisor slots `F + 32..56` (8 LD/SD pairs). -/
theorem evm_addmod_carry_plus_one_reload_spec_within
    (sp base x5Old : Word) (n0 n1 n2 n3 u0 u1 u2 u3 : Word) :
    cpsTripleWithin 8 base (base + 32)
      (CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 (3904 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SD .x12 .x5 (32 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x5 .x12 (3912 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x5 (40 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x5 .x12 (3920 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x5 (48 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x5 .x12 (3928 : BitVec 12)))
       (CodeReq.singleton (base + 28) (.SD .x12 .x5 (56 : BitVec 12))))))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) **
       ((sp + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3928 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ u0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ u1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ u2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ u3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n3) **
       ((sp + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3928 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3)) := by
  have R0 := ld_spec_gen_within .x5 .x12 sp x5Old n0 3904 base (by nofun)
  have T0 := sd_spec_gen_within .x12 .x5 sp n0 u0 32 (base + 4)
  have R1 := ld_spec_gen_within .x5 .x12 sp n0 n1 3912 (base + 8) (by nofun)
  have T1 := sd_spec_gen_within .x12 .x5 sp n1 u1 40 (base + 12)
  have R2 := ld_spec_gen_within .x5 .x12 sp n1 n2 3920 (base + 16) (by nofun)
  have T2 := sd_spec_gen_within .x12 .x5 sp n2 u2 48 (base + 20)
  have R3 := ld_spec_gen_within .x5 .x12 sp n2 n3 3928 (base + 24) (by nofun)
  have T3 := sd_spec_gen_within .x12 .x5 sp n3 u3 56 (base + 28)
  runBlock R0 T0 R1 T1 R2 T2 R3 T3

/-- Carry path — prepare the second helper call: add one to the remainder
    `m1 = (2^256−1) mod N` (at `F + 32..56`), writing the incremented value
    into `F + 0..24` (total carry chain), then reload `N` from S1 into
    `F + 32..56`. The carry-chain limb values are exposed verbatim; the
    value-level `m1 + 1` bridge is the next milestone's job. -/
theorem evm_addmod_carry_plus_one_args_spec_within
    (sp base x5Old x6Old x7Old : Word)
    (m0 m1 m2 m3 w0 w1 w2 w3 n0 n1 n2 n3 : Word) :
    let q0 := m0 + signExtend12 (1 : BitVec 12)
    let k0 := if BitVec.ult q0 (signExtend12 (1 : BitVec 12))
      then (1 : Word) else 0
    let q1 := m1 + k0
    let k1 := if BitVec.ult q1 k0 then (1 : Word) else 0
    let q2 := m2 + k1
    let k2 := if BitVec.ult q2 k1 then (1 : Word) else 0
    let q3 := m3 + k2
    let k3 := if BitVec.ult q3 k2 then (1 : Word) else 0
    cpsTripleWithin 24 base (base + 96)
      (evm_addmod_carry_plus_one_args_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ m3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ w0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ w1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ w2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ w3) **
       ((sp + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3928 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n3) ** (.x6 ↦ᵣ q3) ** (.x7 ↦ᵣ k3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ q0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ q1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ q2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ q3) **
       ((sp + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3928 : BitVec 12)) ↦ₘ n3)) := by
  intro q0 k0 q1 k1 q2 k2 q3 k3
  simp only [q0, k0, q1, k1, q2, k2, q3, k3]
  have P0 := evm_addmod_carry_plus_one_low_spec_within sp base
    x5Old x6Old x7Old m0 w0
  have P1 := evm_addmod_carry_plus_one_limb_spec_within 40 8 sp (base + 16)
    m0 (m0 + signExtend12 (1 : BitVec 12))
    (if BitVec.ult (m0 + signExtend12 (1 : BitVec 12))
      (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0)
    m1 w1
  have P2 := evm_addmod_carry_plus_one_limb_spec_within 48 16 sp (base + 32)
    m1
    (m1 + (if BitVec.ult (m0 + signExtend12 (1 : BitVec 12))
      (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0))
    (if BitVec.ult
      (m1 + (if BitVec.ult (m0 + signExtend12 (1 : BitVec 12))
        (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0))
      (if BitVec.ult (m0 + signExtend12 (1 : BitVec 12))
        (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0)
      then (1 : Word) else 0)
    m2 w2
  have P3 := evm_addmod_carry_plus_one_limb_spec_within 56 24 sp (base + 48)
    m2
    (m2 + (if BitVec.ult
      (m1 + (if BitVec.ult (m0 + signExtend12 (1 : BitVec 12))
        (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0))
      (if BitVec.ult (m0 + signExtend12 (1 : BitVec 12))
        (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0)
      then (1 : Word) else 0))
    (if BitVec.ult
      (m2 + (if BitVec.ult
        (m1 + (if BitVec.ult (m0 + signExtend12 (1 : BitVec 12))
          (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0))
        (if BitVec.ult (m0 + signExtend12 (1 : BitVec 12))
          (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0)
        then (1 : Word) else 0))
      (if BitVec.ult
        (m1 + (if BitVec.ult (m0 + signExtend12 (1 : BitVec 12))
          (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0))
        (if BitVec.ult (m0 + signExtend12 (1 : BitVec 12))
          (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0)
        then (1 : Word) else 0)
      then (1 : Word) else 0)
    m3 w3
  have R := evm_addmod_carry_plus_one_reload_spec_within sp (base + 64)
    m3 n0 n1 n2 n3 m0 m1 m2 m3
  runBlock P0 P1 P2 P3 R

-- ============================================================================
-- evm_addmod_carry_stage_low_args (24 instructions)
-- ============================================================================

abbrev evm_addmod_carry_stage_low_args_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 (32 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SD .x12 .x5 (3840 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x5 .x12 (40 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x5 (3848 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x5 .x12 (48 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x5 (3856 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x5 .x12 (56 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SD .x12 .x5 (3864 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 32) (.LD .x5 .x12 (3872 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 36) (.SD .x12 .x5 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x5 .x12 (3880 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 44) (.SD .x12 .x5 (8 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 48) (.LD .x5 .x12 (3888 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 52) (.SD .x12 .x5 (16 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 56) (.LD .x5 .x12 (3896 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 60) (.SD .x12 .x5 (24 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 64) (.LD .x5 .x12 (3904 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 68) (.SD .x12 .x5 (32 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 72) (.LD .x5 .x12 (3912 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 76) (.SD .x12 .x5 (40 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 80) (.LD .x5 .x12 (3920 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 84) (.SD .x12 .x5 (48 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 88) (.LD .x5 .x12 (3928 : BitVec 12)))
   (CodeReq.singleton (base + 92) (.SD .x12 .x5 (56 : BitVec 12)))))))))))))))))))))))))

theorem evm_addmod_carry_stage_low_args_code_eq_ofProg (base : Word) :
    evm_addmod_carry_stage_low_args_code base =
      CodeReq.ofProg base evm_addmod_carry_stage_low_args := by
  unfold evm_addmod_carry_stage_low_args_code evm_addmod_carry_stage_low_args
    LD SD single seq
  change _ = CodeReq.ofProg base
    [.LD .x5 .x12 32, .SD .x12 .x5 3840, .LD .x5 .x12 40, .SD .x12 .x5 3848,
     .LD .x5 .x12 48, .SD .x12 .x5 3856, .LD .x5 .x12 56, .SD .x12 .x5 3864,
     .LD .x5 .x12 3872, .SD .x12 .x5 0, .LD .x5 .x12 3880, .SD .x12 .x5 8,
     .LD .x5 .x12 3888, .SD .x12 .x5 16, .LD .x5 .x12 3896, .SD .x12 .x5 24,
     .LD .x5 .x12 3904, .SD .x12 .x5 32, .LD .x5 .x12 3912, .SD .x12 .x5 40,
     .LD .x5 .x12 3920, .SD .x12 .x5 48, .LD .x5 .x12 3928, .SD .x12 .x5 56]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right, BitVec.add_assoc, BitVec.reduceAdd]
  rfl

/-- Carry path — stage the low-sum reduction: park `m = 2^256 mod N` (at
    `F + 32..56`) into S3, reload `r` from S2 into `F + 0..24`, and reload
    `N` from S1 into `F + 32..56`. -/
theorem evm_addmod_carry_stage_low_args_spec_within
    (sp base x5Old : Word)
    (m0 m1 m2 m3 u0 u1 u2 u3 r0 r1 r2 r3 w0 w1 w2 w3 n0 n1 n2 n3 : Word) :
    cpsTripleWithin 24 base (base + 96)
      (evm_addmod_carry_stage_low_args_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ m3) **
       ((sp + signExtend12 (3840 : BitVec 12)) ↦ₘ u0) **
       ((sp + signExtend12 (3848 : BitVec 12)) ↦ₘ u1) **
       ((sp + signExtend12 (3856 : BitVec 12)) ↦ₘ u2) **
       ((sp + signExtend12 (3864 : BitVec 12)) ↦ₘ u3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ w0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ w1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ w2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ w3) **
       ((sp + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3928 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (3840 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (3848 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (3856 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (3864 : BitVec 12)) ↦ₘ m3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3928 : BitVec 12)) ↦ₘ n3)) := by
  have P0 := ld_spec_gen_within .x5 .x12 sp x5Old m0 32 base (by nofun)
  have Q0 := sd_spec_gen_within .x12 .x5 sp m0 u0 3840 (base + 4)
  have P1 := ld_spec_gen_within .x5 .x12 sp m0 m1 40 (base + 8) (by nofun)
  have Q1 := sd_spec_gen_within .x12 .x5 sp m1 u1 3848 (base + 12)
  have P2 := ld_spec_gen_within .x5 .x12 sp m1 m2 48 (base + 16) (by nofun)
  have Q2 := sd_spec_gen_within .x12 .x5 sp m2 u2 3856 (base + 20)
  have P3 := ld_spec_gen_within .x5 .x12 sp m2 m3 56 (base + 24) (by nofun)
  have Q3 := sd_spec_gen_within .x12 .x5 sp m3 u3 3864 (base + 28)
  have R0 := ld_spec_gen_within .x5 .x12 sp m3 r0 3872 (base + 32) (by nofun)
  have T0 := sd_spec_gen_within .x12 .x5 sp r0 w0 0 (base + 36)
  have R1 := ld_spec_gen_within .x5 .x12 sp r0 r1 3880 (base + 40) (by nofun)
  have T1 := sd_spec_gen_within .x12 .x5 sp r1 w1 8 (base + 44)
  have R2 := ld_spec_gen_within .x5 .x12 sp r1 r2 3888 (base + 48) (by nofun)
  have T2 := sd_spec_gen_within .x12 .x5 sp r2 w2 16 (base + 52)
  have R3 := ld_spec_gen_within .x5 .x12 sp r2 r3 3896 (base + 56) (by nofun)
  have T3 := sd_spec_gen_within .x12 .x5 sp r3 w3 24 (base + 60)
  have N0 := ld_spec_gen_within .x5 .x12 sp r3 n0 3904 (base + 64) (by nofun)
  have U0 := sd_spec_gen_within .x12 .x5 sp n0 m0 32 (base + 68)
  have N1 := ld_spec_gen_within .x5 .x12 sp n0 n1 3912 (base + 72) (by nofun)
  have U1 := sd_spec_gen_within .x12 .x5 sp n1 m1 40 (base + 76)
  have N2 := ld_spec_gen_within .x5 .x12 sp n1 n2 3920 (base + 80) (by nofun)
  have U2 := sd_spec_gen_within .x12 .x5 sp n2 m2 48 (base + 84)
  have N3 := ld_spec_gen_within .x5 .x12 sp n2 n3 3928 (base + 88) (by nofun)
  have U3 := sd_spec_gen_within .x12 .x5 sp n3 m3 56 (base + 92)
  runBlock P0 Q0 P1 Q1 P2 Q2 P3 Q3 R0 T0 R1 T1 R2 T2 R3 T3
    N0 U0 N1 U1 N2 U2 N3 U3

-- ============================================================================
-- evm_addmod_carry_mod_add_stage (8 instructions)
-- ============================================================================

abbrev evm_addmod_carry_mod_add_stage_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 (3840 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SD .x12 .x5 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x5 .x12 (3848 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x5 (8 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x5 .x12 (3856 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x5 (16 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x5 .x12 (3864 : BitVec 12)))
   (CodeReq.singleton (base + 28) (.SD .x12 .x5 (24 : BitVec 12)))))))))

theorem evm_addmod_carry_mod_add_stage_code_eq_ofProg (base : Word) :
    evm_addmod_carry_mod_add_stage_code base =
      CodeReq.ofProg base evm_addmod_carry_mod_add_stage := by
  unfold evm_addmod_carry_mod_add_stage_code evm_addmod_carry_mod_add_stage
    LD SD single seq
  change _ = CodeReq.ofProg base
    [.LD .x5 .x12 3840, .SD .x12 .x5 0, .LD .x5 .x12 3848, .SD .x12 .x5 8,
     .LD .x5 .x12 3856, .SD .x12 .x5 16, .LD .x5 .x12 3864, .SD .x12 .x5 24]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right, BitVec.add_assoc, BitVec.reduceAdd]
  rfl

/-- Carry path — stage the final modular add: copy `m` from S3 into the
    `evm_add` first-operand slots `F + 0..24` (rMod is already at
    `F + 32..56` from the third MOD call). -/
theorem evm_addmod_carry_mod_add_stage_spec_within
    (sp base x5Old : Word) (m0 m1 m2 m3 w0 w1 w2 w3 : Word) :
    cpsTripleWithin 8 base (base + 32)
      (evm_addmod_carry_mod_add_stage_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) **
       ((sp + signExtend12 (3840 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (3848 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (3856 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (3864 : BitVec 12)) ↦ₘ m3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ w0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ w1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ w2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ w3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ m3) **
       ((sp + signExtend12 (3840 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (3848 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (3856 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (3864 : BitVec 12)) ↦ₘ m3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) := by
  have P0 := ld_spec_gen_within .x5 .x12 sp x5Old m0 3840 base (by nofun)
  have Q0 := sd_spec_gen_within .x12 .x5 sp m0 w0 0 (base + 4)
  have P1 := ld_spec_gen_within .x5 .x12 sp m0 m1 3848 (base + 8) (by nofun)
  have Q1 := sd_spec_gen_within .x12 .x5 sp m1 w1 8 (base + 12)
  have P2 := ld_spec_gen_within .x5 .x12 sp m1 m2 3856 (base + 16) (by nofun)
  have Q2 := sd_spec_gen_within .x12 .x5 sp m2 w2 16 (base + 20)
  have P3 := ld_spec_gen_within .x5 .x12 sp m2 m3 3864 (base + 24) (by nofun)
  have Q3 := sd_spec_gen_within .x12 .x5 sp m3 w3 24 (base + 28)
  runBlock P0 Q0 P1 Q1 P2 Q2 P3 Q3

end EvmAsm.Evm64.AddMod.Compose
