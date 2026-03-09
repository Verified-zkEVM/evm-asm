/-
  EvmAsm.Evm64.MultiplySpec

  CPS specifications for the 256-bit EVM MUL program (64-bit).
  Modular decomposition by column:
  - Column 0 (21 instrs): b[0] × {a[0], a[1], a[2], a[3]}
  - Column 1 (23 instrs): b[1] × {a[0], a[1], a[2]}
  - Column 2 (13 instrs): b[2] × {a[0], a[1]}
  - Column 3 (5 instrs): b[3] × {a[0]}
  - Epilogue (1 instr): ADDI sp, sp, 32
-/

import EvmAsm.Evm64.Multiply
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Column 3: b[3] × {a[0]} (5 instructions)
-- ============================================================================

/-- Column 3: multiply b[3] × a[0], add to r3 accumulator, store result.
    5 instructions: LD b3; LD a0; MUL a0*b3; ADD acc; SD result. -/
theorem mul_col3_spec (sp : Addr) (base : Addr)
    (a0 b3 r3_in v5 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code :=
      (base ↦ᵢ .LD .x5 .x12 56) ** ((base + 4) ↦ᵢ .LD .x6 .x12 0) **
      ((base + 8) ↦ᵢ .MUL .x6 .x6 .x5) ** ((base + 12) ↦ᵢ .ADD .x10 .x10 .x6) **
      ((base + 16) ↦ᵢ .SD .x12 .x10 56)
    cpsTriple base (base + 20)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ r3_in) **
       (sp ↦ₘ a0) ** ((sp + 56) ↦ₘ b3))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b3) ** (.x6 ↦ᵣ a0 * b3) ** (.x10 ↦ᵣ r3_in + a0 * b3) **
       (sp ↦ₘ a0) ** ((sp + 56) ↦ₘ r3_in + a0 * b3)) := by
  have L1 := ld_spec_gen .x5 .x12 sp v5 b3 56 base (by nofun) (by validMem)
  have L2 := ld_spec_gen .x6 .x12 sp v6 a0 0 (base + 4) (by nofun) (by validMem)
  have M := mul_spec_gen_rd_eq_rs1 .x6 .x5 a0 b3 (base + 8) (by nofun) (by nofun)
  have A := add_spec_gen_rd_eq_rs1 .x10 .x6 r3_in (a0 * b3) (base + 12) (by nofun) (by nofun)
  have S := sd_spec_gen .x12 .x10 sp (r3_in + a0 * b3) b3 56 (base + 16) (by validMem)
  runBlock L1 L2 M A S

-- ============================================================================
-- Column 2: b[2] × {a[0], a[1]} (13 instructions)
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- Column 2: multiply b[2] × {a[0],a[1]}, finalize r[2], update r[3] accumulator.
    13 instructions. Input: x11 = r2 acc, sp+16 = r3 partial.
    Output: x10 = r3 total, sp+48 = r2 stored. -/
theorem mul_col2_spec (sp : Addr) (base : Addr)
    (a0 a1 b2 r2_in r3p v5 v6 v7 v10 : Word)
    (hvalid : ValidMemRange sp 8) :
    let lo_a0b2 := a0 * b2
    let hi_a0b2 := rv64_mulhu a0 b2
    let r2_out := r2_in + lo_a0b2
    let carry02 := if BitVec.ult r2_out lo_a0b2 then (1 : Word) else 0
    let r3_contrib := hi_a0b2 + carry02 + a1 * b2
    let r3_out := r3p + r3_contrib
    let code :=
      (base ↦ᵢ .LD .x5 .x12 48) ** ((base + 4) ↦ᵢ .LD .x6 .x12 0) **
      ((base + 8) ↦ᵢ .MUL .x7 .x6 .x5) ** ((base + 12) ↦ᵢ .MULHU .x6 .x6 .x5) **
      ((base + 16) ↦ᵢ .ADD .x11 .x11 .x7) ** ((base + 20) ↦ᵢ .SLTU .x7 .x11 .x7) **
      ((base + 24) ↦ᵢ .ADD .x6 .x6 .x7) ** ((base + 28) ↦ᵢ .SD .x12 .x11 48) **
      ((base + 32) ↦ᵢ .LD .x7 .x12 8) ** ((base + 36) ↦ᵢ .MUL .x7 .x7 .x5) **
      ((base + 40) ↦ᵢ .ADD .x6 .x6 .x7) ** ((base + 44) ↦ᵢ .LD .x10 .x12 16) **
      ((base + 48) ↦ᵢ .ADD .x10 .x10 .x6)
    cpsTriple base (base + 52)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ r2_in) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ r3p) ** ((sp + 48) ↦ₘ b2))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b2) ** (.x6 ↦ᵣ r3_contrib) ** (.x7 ↦ᵣ a1 * b2) **
       (.x10 ↦ᵣ r3_out) ** (.x11 ↦ᵣ r2_out) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ r3p) ** ((sp + 48) ↦ₘ r2_out)) := by
  intro lo_a0b2; intro hi_a0b2; intro r2_out; intro carry02
  intro r3_contrib; intro r3_out
  have I0 := ld_spec_gen .x5 .x12 sp v5 b2 48 base (by nofun) (by validMem)
  have I1 := ld_spec_gen .x6 .x12 sp v6 a0 0 (base + 4) (by nofun) (by validMem)
  have I2 := mul_spec_gen .x7 .x6 .x5 v7 a0 b2 (base + 8) (by nofun)
  have I3 := mulhu_spec_gen_rd_eq_rs1 .x6 .x5 a0 b2 (base + 12) (by nofun) (by nofun)
  have I4 := add_spec_gen_rd_eq_rs1 .x11 .x7 r2_in lo_a0b2 (base + 16) (by nofun) (by nofun)
  have I5 := sltu_spec_gen_rd_eq_rs2 .x7 .x11 r2_out lo_a0b2 (base + 20) (by nofun) (by nofun)
  have I6 := add_spec_gen_rd_eq_rs1 .x6 .x7 hi_a0b2 carry02 (base + 24) (by nofun) (by nofun)
  have I7 := sd_spec_gen .x12 .x11 sp r2_out b2 48 (base + 28) (by validMem)
  have I8 := ld_spec_gen .x7 .x12 sp carry02 a1 8 (base + 32) (by nofun) (by validMem)
  have I9 := mul_spec_gen_rd_eq_rs1 .x7 .x5 a1 b2 (base + 36) (by nofun) (by nofun)
  have I10 := add_spec_gen_rd_eq_rs1 .x6 .x7 (hi_a0b2 + carry02) (a1 * b2) (base + 40) (by nofun) (by nofun)
  have I11 := ld_spec_gen .x10 .x12 sp v10 r3p 16 (base + 44) (by nofun) (by validMem)
  have I12 := add_spec_gen_rd_eq_rs1 .x10 .x6 r3p r3_contrib (base + 48) (by nofun) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12

-- ============================================================================
-- Column 1: b[1] × {a[0], a[1], a[2]} (23 instructions)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Column 1: multiply b[1] × {a[0],a[1],a[2]}, finalize r[1], update r[2]/r[3].
    23 instructions. Input: x10 = r1 acc, x11 = r2 acc, sp+24 = r3 partial from col0.
    Output: x11 = r2 acc, sp+16 = r3 partial, sp+40 = r1 stored. -/
theorem mul_col1_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 b1 r1_in r2_in r3p0 v5 v6 v7 : Word)
    (hvalid : ValidMemRange sp 8) :
    let lo_a0b1 := a0 * b1
    let hi_a0b1 := rv64_mulhu a0 b1
    let r1_out := r1_in + lo_a0b1
    let carry01 := if BitVec.ult r1_out lo_a0b1 then (1 : Word) else 0
    let r2_contrib1 := hi_a0b1 + carry01
    let r2_acc1 := r2_in + r2_contrib1
    let carry_r2_1 := if BitVec.ult r2_acc1 r2_contrib1 then (1 : Word) else 0
    let lo_a1b1 := a1 * b1
    let hi_a1b1 := rv64_mulhu a1 b1
    let r2_out := r2_acc1 + lo_a1b1
    let carry_r2_2 := if BitVec.ult r2_out lo_a1b1 then (1 : Word) else 0
    let r3_contrib1 := hi_a1b1 + carry_r2_2
    let r3_spill := carry_r2_1 + r3_contrib1 + a2 * b1 + r3p0
    let code :=
      (base ↦ᵢ .LD .x5 .x12 40) ** ((base + 4) ↦ᵢ .LD .x6 .x12 0) **
      ((base + 8) ↦ᵢ .MUL .x7 .x6 .x5) ** ((base + 12) ↦ᵢ .MULHU .x6 .x6 .x5) **
      ((base + 16) ↦ᵢ .ADD .x10 .x10 .x7) ** ((base + 20) ↦ᵢ .SLTU .x7 .x10 .x7) **
      ((base + 24) ↦ᵢ .ADD .x6 .x6 .x7) ** ((base + 28) ↦ᵢ .SD .x12 .x10 40) **
      ((base + 32) ↦ᵢ .ADD .x11 .x11 .x6) ** ((base + 36) ↦ᵢ .SLTU .x10 .x11 .x6) **
      ((base + 40) ↦ᵢ .LD .x6 .x12 8) ** ((base + 44) ↦ᵢ .MUL .x7 .x6 .x5) **
      ((base + 48) ↦ᵢ .MULHU .x6 .x6 .x5) ** ((base + 52) ↦ᵢ .ADD .x11 .x11 .x7) **
      ((base + 56) ↦ᵢ .SLTU .x7 .x11 .x7) ** ((base + 60) ↦ᵢ .ADD .x6 .x6 .x7) **
      ((base + 64) ↦ᵢ .ADD .x10 .x10 .x6) ** ((base + 68) ↦ᵢ .LD .x6 .x12 16) **
      ((base + 72) ↦ᵢ .MUL .x6 .x6 .x5) ** ((base + 76) ↦ᵢ .ADD .x10 .x10 .x6) **
      ((base + 80) ↦ᵢ .LD .x6 .x12 24) ** ((base + 84) ↦ᵢ .ADD .x10 .x10 .x6) **
      ((base + 88) ↦ᵢ .SD .x12 .x10 16)
    cpsTriple base (base + 92)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ r1_in) ** (.x11 ↦ᵣ r2_in) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) **
       ((sp + 24) ↦ₘ r3p0) ** ((sp + 40) ↦ₘ b1))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b1) ** (.x6 ↦ᵣ r3p0) ** (.x7 ↦ᵣ carry_r2_2) **
       (.x10 ↦ᵣ r3_spill) ** (.x11 ↦ᵣ r2_out) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ r3_spill) **
       ((sp + 24) ↦ₘ r3p0) ** ((sp + 40) ↦ₘ r1_out)) := by
  intro lo_a0b1; intro hi_a0b1; intro r1_out; intro carry01
  intro r2_contrib1; intro r2_acc1; intro carry_r2_1
  intro lo_a1b1; intro hi_a1b1; intro r2_out; intro carry_r2_2
  intro r3_contrib1; intro r3_spill
  have I0 := ld_spec_gen .x5 .x12 sp v5 b1 40 base (by nofun) (by validMem)
  have I1 := ld_spec_gen .x6 .x12 sp v6 a0 0 (base + 4) (by nofun) (by validMem)
  have I2 := mul_spec_gen .x7 .x6 .x5 v7 a0 b1 (base + 8) (by nofun)
  have I3 := mulhu_spec_gen_rd_eq_rs1 .x6 .x5 a0 b1 (base + 12) (by nofun) (by nofun)
  have I4 := add_spec_gen_rd_eq_rs1 .x10 .x7 r1_in lo_a0b1 (base + 16) (by nofun) (by nofun)
  have I5 := sltu_spec_gen_rd_eq_rs2 .x7 .x10 r1_out lo_a0b1 (base + 20) (by nofun) (by nofun)
  have I6 := add_spec_gen_rd_eq_rs1 .x6 .x7 hi_a0b1 carry01 (base + 24) (by nofun) (by nofun)
  have I7 := sd_spec_gen .x12 .x10 sp r1_out b1 40 (base + 28) (by validMem)
  have I8 := add_spec_gen_rd_eq_rs1 .x11 .x6 r2_in r2_contrib1 (base + 32) (by nofun) (by nofun)
  have I9 := sltu_spec_gen .x10 .x11 .x6 r1_out r2_acc1 r2_contrib1 (base + 36) (by nofun)
  have I10 := ld_spec_gen .x6 .x12 sp r2_contrib1 a1 8 (base + 40) (by nofun) (by validMem)
  have I11 := mul_spec_gen .x7 .x6 .x5 carry01 a1 b1 (base + 44) (by nofun)
  have I12 := mulhu_spec_gen_rd_eq_rs1 .x6 .x5 a1 b1 (base + 48) (by nofun) (by nofun)
  have I13 := add_spec_gen_rd_eq_rs1 .x11 .x7 r2_acc1 lo_a1b1 (base + 52) (by nofun) (by nofun)
  have I14 := sltu_spec_gen_rd_eq_rs2 .x7 .x11 r2_out lo_a1b1 (base + 56) (by nofun) (by nofun)
  have I15 := add_spec_gen_rd_eq_rs1 .x6 .x7 hi_a1b1 carry_r2_2 (base + 60) (by nofun) (by nofun)
  have I16 := add_spec_gen_rd_eq_rs1 .x10 .x6 carry_r2_1 r3_contrib1 (base + 64) (by nofun) (by nofun)
  have I17 := ld_spec_gen .x6 .x12 sp r3_contrib1 a2 16 (base + 68) (by nofun) (by validMem)
  have I18 := mul_spec_gen_rd_eq_rs1 .x6 .x5 a2 b1 (base + 72) (by nofun) (by nofun)
  have I19 := add_spec_gen_rd_eq_rs1 .x10 .x6 (carry_r2_1 + r3_contrib1) (a2 * b1) (base + 76) (by nofun) (by nofun)
  have I20 := ld_spec_gen .x6 .x12 sp (a2 * b1) r3p0 24 (base + 80) (by nofun) (by validMem)
  have I21 := add_spec_gen_rd_eq_rs1 .x10 .x6 (carry_r2_1 + r3_contrib1 + a2 * b1) r3p0 (base + 84) (by nofun) (by nofun)
  have I22 := sd_spec_gen .x12 .x10 sp r3_spill a2 16 (base + 88) (by validMem)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20 I21 I22

-- ============================================================================
-- Column 0: b[0] × {a[0], a[1], a[2], a[3]} (21 instructions)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Column 0: multiply b[0] × {a[0],a[1],a[2],a[3]}, store r[0], spill r[3] partial.
    21 instructions. Output: x10 = r1 acc, x11 = r2 acc, sp+24 = r3p, sp+32 = r0. -/
theorem mul_col0_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 b0 v5 v6 v7 v10 v11 : Word)
    (hvalid : ValidMemRange sp 8) :
    let r0 := a0 * b0
    let hi_a0b0 := rv64_mulhu a0 b0
    let lo_a1b0 := a1 * b0
    let hi_a1b0 := rv64_mulhu a1 b0
    let r1_acc := hi_a0b0 + lo_a1b0
    let carry_r1 := if BitVec.ult r1_acc lo_a1b0 then (1 : Word) else 0
    let lo_a2b0 := a2 * b0
    let hi_a2b0 := rv64_mulhu a2 b0
    let r2_acc := hi_a1b0 + carry_r1 + lo_a2b0
    let carry_r2 := if BitVec.ult r2_acc lo_a2b0 then (1 : Word) else 0
    let r3p := hi_a2b0 + carry_r2 + a3 * b0
    let code :=
      (base ↦ᵢ .LD .x5 .x12 32) ** ((base + 4) ↦ᵢ .LD .x6 .x12 0) **
      ((base + 8) ↦ᵢ .MUL .x7 .x6 .x5) ** ((base + 12) ↦ᵢ .MULHU .x10 .x6 .x5) **
      ((base + 16) ↦ᵢ .SD .x12 .x7 32) ** ((base + 20) ↦ᵢ .LD .x6 .x12 8) **
      ((base + 24) ↦ᵢ .MUL .x7 .x6 .x5) ** ((base + 28) ↦ᵢ .MULHU .x11 .x6 .x5) **
      ((base + 32) ↦ᵢ .ADD .x10 .x10 .x7) ** ((base + 36) ↦ᵢ .SLTU .x6 .x10 .x7) **
      ((base + 40) ↦ᵢ .ADD .x11 .x11 .x6) ** ((base + 44) ↦ᵢ .LD .x6 .x12 16) **
      ((base + 48) ↦ᵢ .MUL .x7 .x6 .x5) ** ((base + 52) ↦ᵢ .MULHU .x6 .x6 .x5) **
      ((base + 56) ↦ᵢ .ADD .x11 .x11 .x7) ** ((base + 60) ↦ᵢ .SLTU .x7 .x11 .x7) **
      ((base + 64) ↦ᵢ .ADD .x6 .x6 .x7) ** ((base + 68) ↦ᵢ .LD .x7 .x12 24) **
      ((base + 72) ↦ᵢ .MUL .x7 .x7 .x5) ** ((base + 76) ↦ᵢ .ADD .x6 .x6 .x7) **
      ((base + 80) ↦ᵢ .SD .x12 .x6 24)
    cpsTriple base (base + 84)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) **
       ((sp + 24) ↦ₘ a3) ** ((sp + 32) ↦ₘ b0))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) ** (.x6 ↦ᵣ r3p) ** (.x7 ↦ᵣ a3 * b0) **
       (.x10 ↦ᵣ r1_acc) ** (.x11 ↦ᵣ r2_acc) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) **
       ((sp + 24) ↦ₘ r3p) ** ((sp + 32) ↦ₘ r0)) := by
  intro r0; intro hi_a0b0; intro lo_a1b0; intro hi_a1b0
  intro r1_acc; intro carry_r1; intro lo_a2b0; intro hi_a2b0
  intro r2_acc; intro carry_r2; intro r3p
  have I0 := ld_spec_gen .x5 .x12 sp v5 b0 32 base (by nofun) (by validMem)
  have I1 := ld_spec_gen .x6 .x12 sp v6 a0 0 (base + 4) (by nofun) (by validMem)
  have I2 := mul_spec_gen .x7 .x6 .x5 v7 a0 b0 (base + 8) (by nofun)
  have I3 := mulhu_spec_gen .x10 .x6 .x5 v10 a0 b0 (base + 12) (by nofun)
  have I4 := sd_spec_gen .x12 .x7 sp r0 b0 32 (base + 16) (by validMem)
  have I5 := ld_spec_gen .x6 .x12 sp a0 a1 8 (base + 20) (by nofun) (by validMem)
  have I6 := mul_spec_gen .x7 .x6 .x5 r0 a1 b0 (base + 24) (by nofun)
  have I7 := mulhu_spec_gen .x11 .x6 .x5 v11 a1 b0 (base + 28) (by nofun)
  have I8 := add_spec_gen_rd_eq_rs1 .x10 .x7 hi_a0b0 lo_a1b0 (base + 32) (by nofun) (by nofun)
  have I9 := sltu_spec_gen .x6 .x10 .x7 a1 r1_acc lo_a1b0 (base + 36) (by nofun)
  have I10 := add_spec_gen_rd_eq_rs1 .x11 .x6 hi_a1b0 carry_r1 (base + 40) (by nofun) (by nofun)
  have I11 := ld_spec_gen .x6 .x12 sp carry_r1 a2 16 (base + 44) (by nofun) (by validMem)
  have I12 := mul_spec_gen .x7 .x6 .x5 lo_a1b0 a2 b0 (base + 48) (by nofun)
  have I13 := mulhu_spec_gen_rd_eq_rs1 .x6 .x5 a2 b0 (base + 52) (by nofun) (by nofun)
  have I14 := add_spec_gen_rd_eq_rs1 .x11 .x7 (hi_a1b0 + carry_r1) lo_a2b0 (base + 56) (by nofun) (by nofun)
  have I15 := sltu_spec_gen_rd_eq_rs2 .x7 .x11 r2_acc lo_a2b0 (base + 60) (by nofun) (by nofun)
  have I16 := add_spec_gen_rd_eq_rs1 .x6 .x7 hi_a2b0 carry_r2 (base + 64) (by nofun) (by nofun)
  have I17 := ld_spec_gen .x7 .x12 sp carry_r2 a3 24 (base + 68) (by nofun) (by validMem)
  have I18 := mul_spec_gen_rd_eq_rs1 .x7 .x5 a3 b0 (base + 72) (by nofun) (by nofun)
  have I19 := add_spec_gen_rd_eq_rs1 .x6 .x7 (hi_a2b0 + carry_r2) (a3 * b0) (base + 76) (by nofun) (by nofun)
  have I20 := sd_spec_gen .x12 .x6 sp r3p a3 24 (base + 80) (by validMem)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20

-- ============================================================================
-- Full 256-bit EVM MUL (63 instructions + 1 epilogue = 252 bytes)
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM MUL: composes 4 per-column specs + ADDI sp adjustment.
    63 instructions total. Pops 2 stack words (A at sp, B at sp+32),
    writes (A * B) mod 2^256 to sp+32..sp+56, advances sp by 32. -/
theorem evm_mul_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (v5 v6 v7 v10 v11 : Word)
    (hvalid : ValidMemRange sp 8) :
    -- Col0 intermediates
    let c0_r0 := a0 * b0
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c0_lo_a2b0 := a2 * b0
    let c0_hi_a2b0 := rv64_mulhu a2 b0
    let c0_r2 := c0_hi_a1b0 + c0_c1 + c0_lo_a2b0
    let c0_c2 := if BitVec.ult c0_r2 c0_lo_a2b0 then (1 : Word) else 0
    let c0_r3p := c0_hi_a2b0 + c0_c2 + a3 * b0
    -- Col1 intermediates
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_cr1 := if BitVec.ult c1_r2a c1_rc then (1 : Word) else 0
    let c1_lo2 := a1 * b1
    let c1_hi2 := rv64_mulhu a1 b1
    let c1_r2 := c1_r2a + c1_lo2
    let c1_cr2 := if BitVec.ult c1_r2 c1_lo2 then (1 : Word) else 0
    let c1_rc2 := c1_hi2 + c1_cr2
    let c1_r3p := c1_cr1 + c1_rc2 + a2 * b1 + c0_r3p
    -- Col2 intermediates
    let c2_lo := a0 * b2
    let c2_hi := rv64_mulhu a0 b2
    let c2_r2 := c1_r2 + c2_lo
    let c2_c := if BitVec.ult c2_r2 c2_lo then (1 : Word) else 0
    let c2_rc := c2_hi + c2_c + a1 * b2
    let c2_r3 := c1_r3p + c2_rc
    -- Col3
    let r3_final := c2_r3 + a0 * b3
    let code :=
      -- Col0 (21 instrs: base+0..base+80)
      (base ↦ᵢ .LD .x5 .x12 32) ** ((base + 4) ↦ᵢ .LD .x6 .x12 0) **
      ((base + 8) ↦ᵢ .MUL .x7 .x6 .x5) ** ((base + 12) ↦ᵢ .MULHU .x10 .x6 .x5) **
      ((base + 16) ↦ᵢ .SD .x12 .x7 32) ** ((base + 20) ↦ᵢ .LD .x6 .x12 8) **
      ((base + 24) ↦ᵢ .MUL .x7 .x6 .x5) ** ((base + 28) ↦ᵢ .MULHU .x11 .x6 .x5) **
      ((base + 32) ↦ᵢ .ADD .x10 .x10 .x7) ** ((base + 36) ↦ᵢ .SLTU .x6 .x10 .x7) **
      ((base + 40) ↦ᵢ .ADD .x11 .x11 .x6) ** ((base + 44) ↦ᵢ .LD .x6 .x12 16) **
      ((base + 48) ↦ᵢ .MUL .x7 .x6 .x5) ** ((base + 52) ↦ᵢ .MULHU .x6 .x6 .x5) **
      ((base + 56) ↦ᵢ .ADD .x11 .x11 .x7) ** ((base + 60) ↦ᵢ .SLTU .x7 .x11 .x7) **
      ((base + 64) ↦ᵢ .ADD .x6 .x6 .x7) ** ((base + 68) ↦ᵢ .LD .x7 .x12 24) **
      ((base + 72) ↦ᵢ .MUL .x7 .x7 .x5) ** ((base + 76) ↦ᵢ .ADD .x6 .x6 .x7) **
      ((base + 80) ↦ᵢ .SD .x12 .x6 24) **
      -- Col1 (23 instrs: base+84..base+172)
      ((base + 84) ↦ᵢ .LD .x5 .x12 40) ** ((base + 88) ↦ᵢ .LD .x6 .x12 0) **
      ((base + 92) ↦ᵢ .MUL .x7 .x6 .x5) ** ((base + 96) ↦ᵢ .MULHU .x6 .x6 .x5) **
      ((base + 100) ↦ᵢ .ADD .x10 .x10 .x7) ** ((base + 104) ↦ᵢ .SLTU .x7 .x10 .x7) **
      ((base + 108) ↦ᵢ .ADD .x6 .x6 .x7) ** ((base + 112) ↦ᵢ .SD .x12 .x10 40) **
      ((base + 116) ↦ᵢ .ADD .x11 .x11 .x6) ** ((base + 120) ↦ᵢ .SLTU .x10 .x11 .x6) **
      ((base + 124) ↦ᵢ .LD .x6 .x12 8) ** ((base + 128) ↦ᵢ .MUL .x7 .x6 .x5) **
      ((base + 132) ↦ᵢ .MULHU .x6 .x6 .x5) ** ((base + 136) ↦ᵢ .ADD .x11 .x11 .x7) **
      ((base + 140) ↦ᵢ .SLTU .x7 .x11 .x7) ** ((base + 144) ↦ᵢ .ADD .x6 .x6 .x7) **
      ((base + 148) ↦ᵢ .ADD .x10 .x10 .x6) ** ((base + 152) ↦ᵢ .LD .x6 .x12 16) **
      ((base + 156) ↦ᵢ .MUL .x6 .x6 .x5) ** ((base + 160) ↦ᵢ .ADD .x10 .x10 .x6) **
      ((base + 164) ↦ᵢ .LD .x6 .x12 24) ** ((base + 168) ↦ᵢ .ADD .x10 .x10 .x6) **
      ((base + 172) ↦ᵢ .SD .x12 .x10 16) **
      -- Col2 (13 instrs: base+176..base+224)
      ((base + 176) ↦ᵢ .LD .x5 .x12 48) ** ((base + 180) ↦ᵢ .LD .x6 .x12 0) **
      ((base + 184) ↦ᵢ .MUL .x7 .x6 .x5) ** ((base + 188) ↦ᵢ .MULHU .x6 .x6 .x5) **
      ((base + 192) ↦ᵢ .ADD .x11 .x11 .x7) ** ((base + 196) ↦ᵢ .SLTU .x7 .x11 .x7) **
      ((base + 200) ↦ᵢ .ADD .x6 .x6 .x7) ** ((base + 204) ↦ᵢ .SD .x12 .x11 48) **
      ((base + 208) ↦ᵢ .LD .x7 .x12 8) ** ((base + 212) ↦ᵢ .MUL .x7 .x7 .x5) **
      ((base + 216) ↦ᵢ .ADD .x6 .x6 .x7) ** ((base + 220) ↦ᵢ .LD .x10 .x12 16) **
      ((base + 224) ↦ᵢ .ADD .x10 .x10 .x6) **
      -- Col3 (5 instrs: base+228..base+244)
      ((base + 228) ↦ᵢ .LD .x5 .x12 56) ** ((base + 232) ↦ᵢ .LD .x6 .x12 0) **
      ((base + 236) ↦ᵢ .MUL .x6 .x6 .x5) ** ((base + 240) ↦ᵢ .ADD .x10 .x10 .x6) **
      ((base + 244) ↦ᵢ .SD .x12 .x10 56) **
      -- Epilogue (1 instr: base+248)
      ((base + 248) ↦ᵢ .ADDI .x12 .x12 32)
    cpsTriple base (base + 252)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (code **
       (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ b3) ** (.x6 ↦ᵣ a0 * b3) ** (.x7 ↦ᵣ a1 * b2) **
       (.x10 ↦ᵣ r3_final) ** (.x11 ↦ᵣ c2_r2) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ c1_r3p) ** ((sp + 24) ↦ₘ c0_r3p) **
       ((sp + 32) ↦ₘ c0_r0) ** ((sp + 40) ↦ₘ c1_r1) ** ((sp + 48) ↦ₘ c2_r2) ** ((sp + 56) ↦ₘ r3_final)) := by
  -- Introduce all let bindings
  intro c0_r0; intro c0_hi_a0b0; intro c0_lo_a1b0; intro c0_hi_a1b0
  intro c0_r1; intro c0_c1; intro c0_lo_a2b0; intro c0_hi_a2b0
  intro c0_r2; intro c0_c2; intro c0_r3p
  intro c1_lo; intro c1_hi; intro c1_r1; intro c1_c1
  intro c1_rc; intro c1_r2a; intro c1_cr1
  intro c1_lo2; intro c1_hi2; intro c1_r2; intro c1_cr2; intro c1_rc2; intro c1_r3p
  intro c2_lo; intro c2_hi; intro c2_r2; intro c2_c; intro c2_rc; intro c2_r3
  intro r3_final
  -- Instantiate column specs
  have C0 := mul_col0_spec sp base a0 a1 a2 a3 b0 v5 v6 v7 v10 v11 hvalid
  have C1 := mul_col1_spec sp (base + 84) a0 a1 a2 b1 c0_r1 c0_r2 c0_r3p b0 c0_r3p (a3 * b0) hvalid
  have C2 := mul_col2_spec sp (base + 176) a0 a1 b2 c1_r2 c1_r3p b1 c0_r3p c1_cr2 c1_r3p hvalid
  have C3 := mul_col3_spec sp (base + 228) a0 b3 c2_r3 b2 c2_rc hvalid
  have EP := addi_spec_gen_same .x12 sp 32 (base + 248) (by nofun)
  runBlock C0 C1 C2 C3 EP

end EvmAsm.Rv64
