/-
  EvmAsm.Evm32.ShiftComposition

  Full composition proof for the 256-bit EVM SHR program.
  Composes all sub-specs (phase_a, phase_b, phase_c, body_7..body_0, zero_path)
  into the final evm_shr_spec theorem.
-/

import EvmAsm.Evm32.ShiftSpec

namespace EvmAsm

-- ============================================================================
-- Section 1: progAt unfolding lemmas
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem progAt_shr_phase_a (base : Addr) :
    progAt base shr_phase_a =
    ((base ↦ᵢ .LW .x5 .x12 4) **
     ((base + 4) ↦ᵢ .LW .x10 .x12 8) **
     ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LW .x10 .x12 12) **
     ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LW .x10 .x12 16) **
     ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .LW .x10 .x12 20) **
     ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) **
     ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 44) ↦ᵢ .LW .x10 .x12 28) **
     ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
     ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
     ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108)) := by
  show progAt base ([.LW .x5 .x12 4, .LW .x10 .x12 8, .OR .x5 .x5 .x10, .LW .x10 .x12 12, .OR .x5 .x5 .x10, .LW .x10 .x12 16, .OR .x5 .x5 .x10, .LW .x10 .x12 20, .OR .x5 .x5 .x10, .LW .x10 .x12 24, .OR .x5 .x5 .x10, .LW .x10 .x12 28, .OR .x5 .x5 .x10, .BNE .x5 .x0 1120, .LW .x5 .x12 0, .SLTIU .x10 .x5 256, .BEQ .x10 .x0 1108] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 64 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 60 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 56 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 52 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 48 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 44 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 40 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 36 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 32 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 = base + 28 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem progAt_shr_phase_b (base : Addr) :
    progAt base shr_phase_b =
    ((base ↦ᵢ .ANDI .x6 .x5 31) **
     ((base + 4) ↦ᵢ .SRLI .x5 .x5 5) **
     ((base + 8) ↦ᵢ .SLTU .x11 .x0 .x6) **
     ((base + 12) ↦ᵢ .SUB .x11 .x0 .x11) **
     ((base + 16) ↦ᵢ .LI .x7 32) **
     ((base + 20) ↦ᵢ .SUB .x7 .x7 .x6) **
     ((base + 24) ↦ᵢ .ADDI .x12 .x12 32)) := by
  show progAt base ([.ANDI .x6 .x5 31, .SRLI .x5 .x5 5, .SLTU .x11 .x0 .x6, .SUB .x11 .x0 .x11, .LI .x7 32, .SUB .x7 .x7 .x6, .ADDI .x12 .x12 32] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem progAt_shr_phase_c (base : Addr) :
    progAt base shr_phase_c =
    ((base ↦ᵢ .BEQ .x5 .x0 864) **
     ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) **
     ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
     ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) **
     ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
     ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) **
     ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
     ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) **
     ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
     ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) **
     ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
     ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) **
     ((base + 48) ↦ᵢ .BEQ .x5 .x10 48)) := by
  show progAt base ([.BEQ .x5 .x0 864, .ADDI .x10 .x0 1, .BEQ .x5 .x10 668, .ADDI .x10 .x0 2, .BEQ .x5 .x10 496, .ADDI .x10 .x0 3, .BEQ .x5 .x10 348, .ADDI .x10 .x0 4, .BEQ .x5 .x10 224, .ADDI .x10 .x0 5, .BEQ .x5 .x10 124, .ADDI .x10 .x0 6, .BEQ .x5 .x10 48] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 48 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 44 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 40 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 36 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 32 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 = base + 28 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem progAt_shr_body_7 (base : Addr) :
    progAt base shr_body_7 =
    ((base ↦ᵢ .LW .x5 .x12 28) **
     ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 12) ↦ᵢ .SW .x12 .x0 4) **
     ((base + 16) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 24) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 32) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 36) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 40) ↦ᵢ .JAL .x0 1020)) := by
  show progAt base ([.LW .x5 .x12 28, .SRL .x5 .x5 .x6, .SW .x12 .x5 0, .SW .x12 .x0 4, .SW .x12 .x0 8, .SW .x12 .x0 12, .SW .x12 .x0 16, .SW .x12 .x0 20, .SW .x12 .x0 24, .SW .x12 .x0 28, .JAL .x0 1020] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 40 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 36 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 32 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 = base + 28 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem progAt_shr_body_6 (base : Addr) :
    progAt base shr_body_6 =
    ((base ↦ᵢ .LW .x5 .x12 24) **
     ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 28) **
     ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 28) **
     ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 40) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 44) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 48) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 52) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 56) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 60) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 64) ↦ᵢ .JAL .x0 952)) := by
  show progAt base ([.LW .x5 .x12 24, .SRL .x5 .x5 .x6, .LW .x10 .x12 28, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 0, .LW .x5 .x12 28, .SRL .x5 .x5 .x6, .SW .x12 .x5 4, .SW .x12 .x0 8, .SW .x12 .x0 12, .SW .x12 .x0 16, .SW .x12 .x0 20, .SW .x12 .x0 24, .SW .x12 .x0 28, .JAL .x0 952] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 64 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 60 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 56 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 52 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 48 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 44 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 40 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 36 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 32 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 = base + 28 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem progAt_shr_body_5 (base : Addr) :
    progAt base shr_body_5 =
    ((base ↦ᵢ .LW .x5 .x12 20) **
     ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 24) **
     ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 24) **
     ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 28) **
     ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 28) **
     ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .SW .x12 .x5 8) **
     ((base + 68) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 72) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 76) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 80) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 84) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 88) ↦ᵢ .JAL .x0 860)) := by
  show progAt base ([.LW .x5 .x12 20, .SRL .x5 .x5 .x6, .LW .x10 .x12 24, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 0, .LW .x5 .x12 24, .SRL .x5 .x5 .x6, .LW .x10 .x12 28, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 4, .LW .x5 .x12 28, .SRL .x5 .x5 .x6, .SW .x12 .x5 8, .SW .x12 .x0 12, .SW .x12 .x0 16, .SW .x12 .x0 20, .SW .x12 .x0 24, .SW .x12 .x0 28, .JAL .x0 860] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 88 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 84 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 80 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 76 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 72 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 68 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 64 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 60 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 56 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 52 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 48 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 44 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 40 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 36 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 32 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 = base + 28 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem progAt_shr_body_4 (base : Addr) :
    progAt base shr_body_4 =
    ((base ↦ᵢ .LW .x5 .x12 16) **
     ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 20) **
     ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 20) **
     ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) **
     ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 24) **
     ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 28) **
     ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     ((base + 84) ↦ᵢ .LW .x5 .x12 28) **
     ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .SW .x12 .x5 12) **
     ((base + 96) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 100) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 104) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 108) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 112) ↦ᵢ .JAL .x0 744)) := by
  show progAt base ([.LW .x5 .x12 16, .SRL .x5 .x5 .x6, .LW .x10 .x12 20, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 0, .LW .x5 .x12 20, .SRL .x5 .x5 .x6, .LW .x10 .x12 24, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 4, .LW .x5 .x12 24, .SRL .x5 .x5 .x6, .LW .x10 .x12 28, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 8, .LW .x5 .x12 28, .SRL .x5 .x5 .x6, .SW .x12 .x5 12, .SW .x12 .x0 16, .SW .x12 .x0 20, .SW .x12 .x0 24, .SW .x12 .x0 28, .JAL .x0 744] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 112 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 108 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 104 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 100 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 96 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 92 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 88 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 84 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 80 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 76 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 72 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 68 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 64 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 60 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 56 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 52 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 48 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 44 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 40 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 36 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 32 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 = base + 28 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem progAt_shr_body_3 (base : Addr) :
    progAt base shr_body_3 =
    ((base ↦ᵢ .LW .x5 .x12 12) **
     ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 16) **
     ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 16) **
     ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 20) **
     ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 20) **
     ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 24) **
     ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     ((base + 84) ↦ᵢ .LW .x5 .x12 24) **
     ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 28) **
     ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     ((base + 112) ↦ᵢ .LW .x5 .x12 28) **
     ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .SW .x12 .x5 16) **
     ((base + 124) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 128) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 132) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 136) ↦ᵢ .JAL .x0 604)) := by
  show progAt base ([.LW .x5 .x12 12, .SRL .x5 .x5 .x6, .LW .x10 .x12 16, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 0, .LW .x5 .x12 16, .SRL .x5 .x5 .x6, .LW .x10 .x12 20, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 4, .LW .x5 .x12 20, .SRL .x5 .x5 .x6, .LW .x10 .x12 24, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 8, .LW .x5 .x12 24, .SRL .x5 .x5 .x6, .LW .x10 .x12 28, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 12, .LW .x5 .x12 28, .SRL .x5 .x5 .x6, .SW .x12 .x5 16, .SW .x12 .x0 20, .SW .x12 .x0 24, .SW .x12 .x0 28, .JAL .x0 604] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 136 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 132 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 128 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 124 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 120 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 116 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 112 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 108 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 104 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 100 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 96 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 92 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 88 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 84 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 80 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 76 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 72 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 68 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 64 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 60 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 56 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 52 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 48 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 44 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 40 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 36 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 32 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 = base + 28 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem progAt_shr_body_2 (base : Addr) :
    progAt base shr_body_2 =
    ((base ↦ᵢ .LW .x5 .x12 8) **
     ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 12) **
     ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 12) **
     ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 16) **
     ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 16) **
     ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 20) **
     ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     ((base + 84) ↦ᵢ .LW .x5 .x12 20) **
     ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 24) **
     ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     ((base + 112) ↦ᵢ .LW .x5 .x12 24) **
     ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 28) **
     ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     ((base + 140) ↦ᵢ .LW .x5 .x12 28) **
     ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .SW .x12 .x5 20) **
     ((base + 152) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 156) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 160) ↦ᵢ .JAL .x0 440)) := by
  show progAt base ([.LW .x5 .x12 8, .SRL .x5 .x5 .x6, .LW .x10 .x12 12, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 0, .LW .x5 .x12 12, .SRL .x5 .x5 .x6, .LW .x10 .x12 16, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 4, .LW .x5 .x12 16, .SRL .x5 .x5 .x6, .LW .x10 .x12 20, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 8, .LW .x5 .x12 20, .SRL .x5 .x5 .x6, .LW .x10 .x12 24, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 12, .LW .x5 .x12 24, .SRL .x5 .x5 .x6, .LW .x10 .x12 28, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 16, .LW .x5 .x12 28, .SRL .x5 .x5 .x6, .SW .x12 .x5 20, .SW .x12 .x0 24, .SW .x12 .x0 28, .JAL .x0 440] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 160 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 156 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 152 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 148 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 144 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 140 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 136 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 132 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 128 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 124 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 120 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 116 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 112 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 108 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 104 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 100 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 96 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 92 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 88 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 84 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 80 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 76 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 72 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 68 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 64 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 60 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 56 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 52 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 48 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 44 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 40 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 36 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 32 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 = base + 28 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem progAt_shr_body_1 (base : Addr) :
    progAt base shr_body_1 =
    ((base ↦ᵢ .LW .x5 .x12 4) **
     ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 8) **
     ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 8) **
     ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 12) **
     ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 12) **
     ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 16) **
     ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     ((base + 84) ↦ᵢ .LW .x5 .x12 16) **
     ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 20) **
     ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     ((base + 112) ↦ᵢ .LW .x5 .x12 20) **
     ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 24) **
     ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     ((base + 140) ↦ᵢ .LW .x5 .x12 24) **
     ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 28) **
     ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     ((base + 168) ↦ᵢ .LW .x5 .x12 28) **
     ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .SW .x12 .x5 24) **
     ((base + 180) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 184) ↦ᵢ .JAL .x0 252)) := by
  show progAt base ([.LW .x5 .x12 4, .SRL .x5 .x5 .x6, .LW .x10 .x12 8, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 0, .LW .x5 .x12 8, .SRL .x5 .x5 .x6, .LW .x10 .x12 12, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 4, .LW .x5 .x12 12, .SRL .x5 .x5 .x6, .LW .x10 .x12 16, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 8, .LW .x5 .x12 16, .SRL .x5 .x5 .x6, .LW .x10 .x12 20, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 12, .LW .x5 .x12 20, .SRL .x5 .x5 .x6, .LW .x10 .x12 24, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 16, .LW .x5 .x12 24, .SRL .x5 .x5 .x6, .LW .x10 .x12 28, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 20, .LW .x5 .x12 28, .SRL .x5 .x5 .x6, .SW .x12 .x5 24, .SW .x12 .x0 28, .JAL .x0 252] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 184 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 180 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 176 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 172 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 168 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 164 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 160 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 156 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 152 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 148 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 144 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 140 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 136 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 132 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 128 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 124 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 120 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 116 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 112 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 108 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 104 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 100 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 96 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 92 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 88 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 84 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 80 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 76 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 72 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 68 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 64 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 60 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 56 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 52 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 48 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 44 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 40 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 36 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 32 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 = base + 28 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem progAt_shr_body_0 (base : Addr) :
    progAt base shr_body_0 =
    ((base ↦ᵢ .LW .x5 .x12 0) **
     ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 4) **
     ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 4) **
     ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 8) **
     ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 8) **
     ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 12) **
     ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     ((base + 84) ↦ᵢ .LW .x5 .x12 12) **
     ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 16) **
     ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     ((base + 112) ↦ᵢ .LW .x5 .x12 16) **
     ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 20) **
     ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     ((base + 140) ↦ᵢ .LW .x5 .x12 20) **
     ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 24) **
     ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     ((base + 168) ↦ᵢ .LW .x5 .x12 24) **
     ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .LW .x10 .x12 28) **
     ((base + 180) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 184) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 188) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 192) ↦ᵢ .SW .x12 .x5 24) **
     ((base + 196) ↦ᵢ .LW .x5 .x12 28) **
     ((base + 200) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 204) ↦ᵢ .SW .x12 .x5 28) **
     ((base + 208) ↦ᵢ .JAL .x0 40)) := by
  show progAt base ([.LW .x5 .x12 0, .SRL .x5 .x5 .x6, .LW .x10 .x12 4, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 0, .LW .x5 .x12 4, .SRL .x5 .x5 .x6, .LW .x10 .x12 8, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 4, .LW .x5 .x12 8, .SRL .x5 .x5 .x6, .LW .x10 .x12 12, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 8, .LW .x5 .x12 12, .SRL .x5 .x5 .x6, .LW .x10 .x12 16, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 12, .LW .x5 .x12 16, .SRL .x5 .x5 .x6, .LW .x10 .x12 20, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 16, .LW .x5 .x12 20, .SRL .x5 .x5 .x6, .LW .x10 .x12 24, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 20, .LW .x5 .x12 24, .SRL .x5 .x5 .x6, .LW .x10 .x12 28, .SLL .x10 .x10 .x7, .AND .x10 .x10 .x11, .OR .x5 .x5 .x10, .SW .x12 .x5 24, .LW .x5 .x12 28, .SRL .x5 .x5 .x6, .SW .x12 .x5 28, .JAL .x0 40] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 208 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 204 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 200 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 196 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 192 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 188 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 184 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 180 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 176 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 172 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 168 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 164 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 160 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 156 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 152 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 148 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 144 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 140 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 136 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 132 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 128 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 124 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 120 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 116 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 112 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 108 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 104 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 100 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 96 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 92 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 88 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 84 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 80 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 76 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 72 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 68 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 64 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 60 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 56 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 52 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 48 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 44 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 40 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 36 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 32 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 = base + 28 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem progAt_shr_zero_path (base : Addr) :
    progAt base shr_zero_path =
    ((base ↦ᵢ .ADDI .x12 .x12 32) **
     ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
     ((base + 8) ↦ᵢ .SW .x12 .x0 4) **
     ((base + 12) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 16) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 24) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 32) ↦ᵢ .SW .x12 .x0 28)) := by
  show progAt base ([.ADDI .x12 .x12 32, .SW .x12 .x0 0, .SW .x12 .x0 4, .SW .x12 .x0 8, .SW .x12 .x0 12, .SW .x12 .x0 16, .SW .x12 .x0 20, .SW .x12 .x0 24, .SW .x12 .x0 28] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 32 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 = base + 28 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

-- ============================================================================
-- Section 2: Abbreviations for code frame
-- ============================================================================

/-- The non-phase-a code frame: all progAt blocks except phase_a. -/
private abbrev otherCode (base : Addr) : Assertion :=
  progAt (base + 68) shr_phase_b **
  progAt (base + 96) shr_phase_c **
  progAt (base + 148) shr_body_7 **
  progAt (base + 192) shr_body_6 **
  progAt (base + 260) shr_body_5 **
  progAt (base + 352) shr_body_4 **
  progAt (base + 468) shr_body_3 **
  progAt (base + 608) shr_body_2 **
  progAt (base + 772) shr_body_1 **
  progAt (base + 960) shr_body_0 **
  progAt (base + 1172) shr_zero_path

private theorem pcFree_otherCode (base : Addr) : (otherCode base).pcFree := by
  unfold otherCode; pcFree

-- ============================================================================
-- Section 3: Not-taken path helper
-- ============================================================================

-- ============================================================================
-- Section 3: Not-taken path composition
-- ============================================================================

-- The not-taken path composes: phase_b (param extract) -> phase_c (8-way dispatch)
-- -> body_L (shift computation) for L=0..7.
-- Each body L handles limb_shift=L and exits to base+1208.

-- Abbreviation for the common postcondition (code + regOwn/memOwn):
private abbrev notTakenPost (sp base : Addr)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word) : Assertion :=
  progAt base shr_phase_a **
  progAt (base + 68) shr_phase_b **
  progAt (base + 96) shr_phase_c **
  progAt (base + 148) shr_body_7 **
  progAt (base + 192) shr_body_6 **
  progAt (base + 260) shr_body_5 **
  progAt (base + 352) shr_body_4 **
  progAt (base + 468) shr_body_3 **
  progAt (base + 608) shr_body_2 **
  progAt (base + 772) shr_body_1 **
  progAt (base + 960) shr_body_0 **
  progAt (base + 1172) shr_zero_path **
  (.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
  (regOwn .x10) ** (regOwn .x11) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
  ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
  (memOwn (sp + 32)) ** (memOwn (sp + 36)) ** (memOwn (sp + 40)) ** (memOwn (sp + 44)) **
  (memOwn (sp + 48)) ** (memOwn (sp + 52)) ** (memOwn (sp + 56)) ** (memOwn (sp + 60))

-- Helper: weaken body register+memory postcondition to regOwn/memOwn form.
-- This handles the non-code part of any body postcondition.
private theorem regIs_to_regOwn' (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  regIs_implies_regOwn r v

private theorem memIs_to_memOwn' (a : Addr) (v : Word) : ∀ h, (a ↦ₘ v) h → (memOwn a) h :=
  memIs_implies_memOwn a v

-- Helper: weaken concrete reg/mem postcondition (with all progAt) to notTakenPost.
-- Factored out because the same weakening applies to all 8 shift bodies.
private theorem weaken_to_notTakenPost (sp base : Addr)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    {r5 r6 r7 r10 r11 : Word} {m0 m1 m2 m3 m4 m5 m6 m7 : Word} : ∀ h,
    (progAt base shr_phase_a ** progAt (base + 68) shr_phase_b **
     progAt (base + 96) shr_phase_c ** progAt (base + 148) shr_body_7 **
     progAt (base + 192) shr_body_6 ** progAt (base + 260) shr_body_5 **
     progAt (base + 352) shr_body_4 ** progAt (base + 468) shr_body_3 **
     progAt (base + 608) shr_body_2 ** progAt (base + 772) shr_body_1 **
     progAt (base + 960) shr_body_0 ** progAt (base + 1172) shr_zero_path **
     (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) **
     (.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ r11) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 36) ↦ₘ m1) ** ((sp + 40) ↦ₘ m2) ** ((sp + 44) ↦ₘ m3) **
     ((sp + 48) ↦ₘ m4) ** ((sp + 52) ↦ₘ m5) ** ((sp + 56) ↦ₘ m6) ** ((sp + 60) ↦ₘ m7)) h →
    (notTakenPost sp base s0 s1 s2 s3 s4 s5 s6 s7) h := by
  intro h hp
  unfold notTakenPost
  have hp1 : (
    (progAt base shr_phase_a ** progAt (base + 68) shr_phase_b **
     progAt (base + 96) shr_phase_c ** progAt (base + 148) shr_body_7 **
     progAt (base + 192) shr_body_6 ** progAt (base + 260) shr_body_5 **
     progAt (base + 352) shr_body_4 ** progAt (base + 468) shr_body_3 **
     progAt (base + 608) shr_body_2 ** progAt (base + 772) shr_body_1 **
     progAt (base + 960) shr_body_0 ** progAt (base + 1172) shr_zero_path) **
    ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) **
     (.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ r11) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 36) ↦ₘ m1) ** ((sp + 40) ↦ₘ m2) ** ((sp + 44) ↦ₘ m3) **
     ((sp + 48) ↦ₘ m4) ** ((sp + 52) ↦ₘ m5) ** ((sp + 56) ↦ₘ m6) ** ((sp + 60) ↦ₘ m7))) h :=
    (congrFun (show _ = _ from by xperm) h).mp hp
  have hp2 := sepConj_mono_right
    (weaken_body_post sp s0 s1 s2 s3 s4 s5 s6 s7 r5 r6 r7 r10 r11 m0 m1 m2 m3 m4 m5 m6 m7) h hp1
  exact (congrFun (show _ = _ from by xperm) h).mp hp2

set_option maxHeartbeats 25600000 in
set_option maxRecDepth 4096 in
private theorem evm_shr_not_taken_aux
    (sp base : Addr) (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (v0 v1 v2 v3 v4 v5 v6 v7 : Word) (r6 r7 r10 r11 : Word)
    (_hvS : ValidMemRange sp 8) (hvV : ValidMemRange (sp + 32) 8) :
    cpsTriple (base + 68) (base + 1208)
      (progAt base shr_phase_a **
       progAt (base + 68) shr_phase_b **
       progAt (base + 96) shr_phase_c **
       progAt (base + 148) shr_body_7 **
       progAt (base + 192) shr_body_6 **
       progAt (base + 260) shr_body_5 **
       progAt (base + 352) shr_body_4 **
       progAt (base + 468) shr_body_3 **
       progAt (base + 608) shr_body_2 **
       progAt (base + 772) shr_body_1 **
       progAt (base + 960) shr_body_0 **
       progAt (base + 1172) shr_zero_path **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 36) ↦ₘ v1) ** ((sp + 40) ↦ₘ v2) ** ((sp + 44) ↦ₘ v3) **
       ((sp + 48) ↦ₘ v4) ** ((sp + 52) ↦ₘ v5) ** ((sp + 56) ↦ₘ v6) ** ((sp + 60) ↦ₘ v7))
      (notTakenPost sp base s0 s1 s2 s3 s4 s5 s6 s7) := by
  -- Step 1: Phase B spec (instrAt form, framed)
  have pb_raw := shr_phase_b_spec s0 sp r6 r7 r11 (base + 68)
  rw [show (base + 68 : Addr) + 28 = base + 96 from by bv_omega] at pb_raw
  have pb_framed := cpsTriple_frame_left _ _ _ _
    (progAt base shr_phase_a **
     progAt (base + 96) shr_phase_c **
     progAt (base + 148) shr_body_7 **
     progAt (base + 192) shr_body_6 **
     progAt (base + 260) shr_body_5 **
     progAt (base + 352) shr_body_4 **
     progAt (base + 468) shr_body_3 **
     progAt (base + 608) shr_body_2 **
     progAt (base + 772) shr_body_1 **
     progAt (base + 960) shr_body_0 **
     progAt (base + 1172) shr_zero_path **
     (.x10 ↦ᵣ r10) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 36) ↦ₘ v1) ** ((sp + 40) ↦ₘ v2) ** ((sp + 44) ↦ₘ v3) **
     ((sp + 48) ↦ₘ v4) ** ((sp + 52) ↦ₘ v5) ** ((sp + 56) ↦ₘ v6) ** ((sp + 60) ↦ₘ v7))
    (by pcFree) pb_raw
  clear pb_raw
  simp only [signExtend12_32] at pb_framed
  -- Step 2: Phase C spec (instrAt form)
  have pc_raw := shr_phase_c_spec
    (s0 >>> (5 : BitVec 5).toNat) r10 (base + 96)
    (base + 960) (base + 772) (base + 608) (base + 468)
    (base + 352) (base + 260) (base + 192) (base + 148)
    (by simp only [show signExtend13 864 = (864 : Word) from by native_decide]; bv_omega)
    (by simp only [show signExtend13 668 = (668 : Word) from by native_decide]; bv_omega)
    (by simp only [show signExtend13 496 = (496 : Word) from by native_decide]; bv_omega)
    (by simp only [show signExtend13 348 = (348 : Word) from by native_decide]; bv_omega)
    (by simp only [show signExtend13 224 = (224 : Word) from by native_decide]; bv_omega)
    (by simp only [show signExtend13 124 = (124 : Word) from by native_decide]; bv_omega)
    (by simp only [show signExtend13 48 = (48 : Word) from by native_decide]; bv_omega)
    (by bv_omega)
  -- Frame phase_c with remaining resources (phase_b output values)
  have pc_framed := cpsNBranch_frame_left (base + 96) _ _
    (progAt base shr_phase_a **
     progAt (base + 68) shr_phase_b **
     progAt (base + 148) shr_body_7 **
     progAt (base + 192) shr_body_6 **
     progAt (base + 260) shr_body_5 **
     progAt (base + 352) shr_body_4 **
     progAt (base + 468) shr_body_3 **
     progAt (base + 608) shr_body_2 **
     progAt (base + 772) shr_body_1 **
     progAt (base + 960) shr_body_0 **
     progAt (base + 1172) shr_zero_path **
     (.x6 ↦ᵣ (s0 &&& signExtend12 31)) **
     (.x7 ↦ᵣ ((32 : Word) - (s0 &&& signExtend12 31))) **
     (.x11 ↦ᵣ ((0 : Word) - (if BitVec.ult (0 : Word) (s0 &&& signExtend12 31) then (1 : Word) else 0))) **
     (.x12 ↦ᵣ (sp + 32)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 36) ↦ₘ v1) ** ((sp + 40) ↦ₘ v2) ** ((sp + 44) ↦ₘ v3) **
     ((sp + 48) ↦ₘ v4) ** ((sp + 52) ↦ₘ v5) ** ((sp + 56) ↦ₘ v6) ** ((sp + 60) ↦ₘ v7))
    (by pcFree)
    pc_raw
  clear pc_raw
  -- Step 3: Compose phase_b (cpsTriple) with phase_c (cpsNBranch)
  -- Phase B output has instrAt + frame, Phase C input has instrAt + regs
  -- Need permutation to match: pb output → pc input
  have bc := cpsTriple_seq_cpsNBranch_with_perm (base + 68) (base + 96) _ _ _ _
    (fun h hp => by
      rw [progAt_shr_phase_c (base + 96)] at hp
      rw [progAt_shr_phase_b (base + 68)]
      xperm_hyp hp) pb_framed pc_framed
  clear pb_framed pc_framed
  -- Step 4: Bridge precondition (progAt → instrAt) and merge all 8 exits
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by
      rw [progAt_shr_phase_b (base + 68)] at hp
      xperm_hyp hp)
    (fun h hq => hq)
    (cpsNBranch_merge _ _ _ _ _ bc (fun exit hmem => by
      simp only [List.map_cons, List.map_nil, List.mem_cons,
        List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- Address normalizations shared across all bodies
      all_goals (
        try have hn4  : (sp + 32 : Word) + 4  = sp + 36 := by bv_omega
        try have hn8  : (sp + 32 : Word) + 8  = sp + 40 := by bv_omega
        try have hn12 : (sp + 32 : Word) + 12 = sp + 44 := by bv_omega
        try have hn16 : (sp + 32 : Word) + 16 = sp + 48 := by bv_omega
        try have hn20 : (sp + 32 : Word) + 20 = sp + 52 := by bv_omega
        try have hn24 : (sp + 32 : Word) + 24 = sp + 56 := by bv_omega
        try have hn28 : (sp + 32 : Word) + 28 = sp + 60 := by bv_omega
        skip)
      · -- body_0 at base+960
        have bspec := shr_body_0_spec (sp + 32)
          (s0 >>> (5 : BitVec 5).toNat) r10
          (s0 &&& signExtend12 31) ((32 : Word) - (s0 &&& signExtend12 31))
          ((0 : Word) - (if BitVec.ult (0 : Word) (s0 &&& signExtend12 31) then (1 : Word) else 0))
          v0 v1 v2 v3 v4 v5 v6 v7
          (base + 960) (base + 1208) 40
          (by simp only [show signExtend21 (40 : BitVec 21) = (40 : Word) from by native_decide]
              bv_omega)
          hvV
        rw [hn4, hn8, hn12, hn16, hn20, hn24, hn28] at bspec
        have bframed := cpsTriple_frame_left _ _ _ _
          (progAt (base + 96) shr_phase_c **
           (.x0 ↦ᵣ (0 : Word)) **
           progAt base shr_phase_a **
           progAt (base + 68) shr_phase_b **
           progAt (base + 148) shr_body_7 **
           progAt (base + 192) shr_body_6 **
           progAt (base + 260) shr_body_5 **
           progAt (base + 352) shr_body_4 **
           progAt (base + 468) shr_body_3 **
           progAt (base + 608) shr_body_2 **
           progAt (base + 772) shr_body_1 **
           progAt (base + 1172) shr_zero_path **
           (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
           ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
          (by pcFree) bspec
        exact cpsTriple_consequence _ _ _ _ _ _
          (fun h hp => by
            rw [progAt_shr_body_0 (base + 960)] at hp
            rw [progAt_shr_phase_c (base + 96)]
            xperm_hyp hp)
          (fun h hq => by
            apply weaken_to_notTakenPost sp base s0 s1 s2 s3 s4 s5 s6 s7
            rw [progAt_shr_body_0 (base + 960)]
            xperm_hyp hq)
          bframed
      · -- body_1 at base+772
        have bspec := shr_body_1_spec (sp + 32)
          (s0 >>> (5 : BitVec 5).toNat) ((0 : Word) + signExtend12 1)
          (s0 &&& signExtend12 31) ((32 : Word) - (s0 &&& signExtend12 31))
          ((0 : Word) - (if BitVec.ult (0 : Word) (s0 &&& signExtend12 31) then (1 : Word) else 0))
          v0 v1 v2 v3 v4 v5 v6 v7
          (base + 772) (base + 1208) 252
          (by simp only [show signExtend21 (252 : BitVec 21) = (252 : Word) from by native_decide]
              bv_omega)
          hvV
        rw [hn4, hn8, hn12, hn16, hn20, hn24, hn28] at bspec
        have bframed := cpsTriple_frame_left _ _ _ _
          (progAt (base + 96) shr_phase_c **
           (.x0 ↦ᵣ (0 : Word)) **
           progAt base shr_phase_a **
           progAt (base + 68) shr_phase_b **
           progAt (base + 148) shr_body_7 **
           progAt (base + 192) shr_body_6 **
           progAt (base + 260) shr_body_5 **
           progAt (base + 352) shr_body_4 **
           progAt (base + 468) shr_body_3 **
           progAt (base + 608) shr_body_2 **
           progAt (base + 960) shr_body_0 **
           progAt (base + 1172) shr_zero_path **
           (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
           ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
          (by pcFree) bspec
        exact cpsTriple_consequence _ _ _ _ _ _
          (fun h hp => by
            rw [progAt_shr_body_1 (base + 772)] at hp
            rw [progAt_shr_phase_c (base + 96)]
            xperm_hyp hp)
          (fun h hq => by
            apply weaken_to_notTakenPost sp base s0 s1 s2 s3 s4 s5 s6 s7
            rw [progAt_shr_body_1 (base + 772)]
            xperm_hyp hq)
          bframed
      · -- body_2 at base+608
        have bspec := shr_body_2_spec (sp + 32)
          (s0 >>> (5 : BitVec 5).toNat) ((0 : Word) + signExtend12 2)
          (s0 &&& signExtend12 31) ((32 : Word) - (s0 &&& signExtend12 31))
          ((0 : Word) - (if BitVec.ult (0 : Word) (s0 &&& signExtend12 31) then (1 : Word) else 0))
          v0 v1 v2 v3 v4 v5 v6 v7
          (base + 608) (base + 1208) 440
          (by simp only [show signExtend21 (440 : BitVec 21) = (440 : Word) from by native_decide]
              bv_omega)
          hvV
        rw [hn4, hn8, hn12, hn16, hn20, hn24, hn28] at bspec
        have bframed := cpsTriple_frame_left _ _ _ _
          (progAt (base + 96) shr_phase_c **
           (.x0 ↦ᵣ (0 : Word)) **
           progAt base shr_phase_a **
           progAt (base + 68) shr_phase_b **
           progAt (base + 148) shr_body_7 **
           progAt (base + 192) shr_body_6 **
           progAt (base + 260) shr_body_5 **
           progAt (base + 352) shr_body_4 **
           progAt (base + 468) shr_body_3 **
           progAt (base + 772) shr_body_1 **
           progAt (base + 960) shr_body_0 **
           progAt (base + 1172) shr_zero_path **
           (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
           ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
          (by pcFree) bspec
        exact cpsTriple_consequence _ _ _ _ _ _
          (fun h hp => by
            rw [progAt_shr_body_2 (base + 608)] at hp
            rw [progAt_shr_phase_c (base + 96)]
            xperm_hyp hp)
          (fun h hq => by
            apply weaken_to_notTakenPost sp base s0 s1 s2 s3 s4 s5 s6 s7
            rw [progAt_shr_body_2 (base + 608)]
            xperm_hyp hq)
          bframed
      · -- body_3 at base+468
        have bspec := shr_body_3_spec (sp + 32)
          (s0 >>> (5 : BitVec 5).toNat) ((0 : Word) + signExtend12 3)
          (s0 &&& signExtend12 31) ((32 : Word) - (s0 &&& signExtend12 31))
          ((0 : Word) - (if BitVec.ult (0 : Word) (s0 &&& signExtend12 31) then (1 : Word) else 0))
          v0 v1 v2 v3 v4 v5 v6 v7
          (base + 468) (base + 1208) 604
          (by simp only [show signExtend21 (604 : BitVec 21) = (604 : Word) from by native_decide]
              bv_omega)
          hvV
        rw [hn4, hn8, hn12, hn16, hn20, hn24, hn28] at bspec
        have bframed := cpsTriple_frame_left _ _ _ _
          (progAt (base + 96) shr_phase_c **
           (.x0 ↦ᵣ (0 : Word)) **
           progAt base shr_phase_a **
           progAt (base + 68) shr_phase_b **
           progAt (base + 148) shr_body_7 **
           progAt (base + 192) shr_body_6 **
           progAt (base + 260) shr_body_5 **
           progAt (base + 352) shr_body_4 **
           progAt (base + 608) shr_body_2 **
           progAt (base + 772) shr_body_1 **
           progAt (base + 960) shr_body_0 **
           progAt (base + 1172) shr_zero_path **
           (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
           ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
          (by pcFree) bspec
        exact cpsTriple_consequence _ _ _ _ _ _
          (fun h hp => by
            rw [progAt_shr_body_3 (base + 468)] at hp
            rw [progAt_shr_phase_c (base + 96)]
            xperm_hyp hp)
          (fun h hq => by
            apply weaken_to_notTakenPost sp base s0 s1 s2 s3 s4 s5 s6 s7
            rw [progAt_shr_body_3 (base + 468)]
            xperm_hyp hq)
          bframed
      · -- body_4 at base+352
        have bspec := shr_body_4_spec (sp + 32)
          (s0 >>> (5 : BitVec 5).toNat) ((0 : Word) + signExtend12 4)
          (s0 &&& signExtend12 31) ((32 : Word) - (s0 &&& signExtend12 31))
          ((0 : Word) - (if BitVec.ult (0 : Word) (s0 &&& signExtend12 31) then (1 : Word) else 0))
          v0 v1 v2 v3 v4 v5 v6 v7
          (base + 352) (base + 1208) 744
          (by simp only [show signExtend21 (744 : BitVec 21) = (744 : Word) from by native_decide]
              bv_omega)
          hvV
        rw [hn4, hn8, hn12, hn16, hn20, hn24, hn28] at bspec
        have bframed := cpsTriple_frame_left _ _ _ _
          (progAt (base + 96) shr_phase_c **
           (.x0 ↦ᵣ (0 : Word)) **
           progAt base shr_phase_a **
           progAt (base + 68) shr_phase_b **
           progAt (base + 148) shr_body_7 **
           progAt (base + 192) shr_body_6 **
           progAt (base + 260) shr_body_5 **
           progAt (base + 468) shr_body_3 **
           progAt (base + 608) shr_body_2 **
           progAt (base + 772) shr_body_1 **
           progAt (base + 960) shr_body_0 **
           progAt (base + 1172) shr_zero_path **
           (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
           ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
          (by pcFree) bspec
        exact cpsTriple_consequence _ _ _ _ _ _
          (fun h hp => by
            rw [progAt_shr_body_4 (base + 352)] at hp
            rw [progAt_shr_phase_c (base + 96)]
            xperm_hyp hp)
          (fun h hq => by
            apply weaken_to_notTakenPost sp base s0 s1 s2 s3 s4 s5 s6 s7
            rw [progAt_shr_body_4 (base + 352)]
            xperm_hyp hq)
          bframed
      · -- body_5 at base+260
        have bspec := shr_body_5_spec (sp + 32)
          (s0 >>> (5 : BitVec 5).toNat) ((0 : Word) + signExtend12 5)
          (s0 &&& signExtend12 31) ((32 : Word) - (s0 &&& signExtend12 31))
          ((0 : Word) - (if BitVec.ult (0 : Word) (s0 &&& signExtend12 31) then (1 : Word) else 0))
          v0 v1 v2 v3 v4 v5 v6 v7
          (base + 260) (base + 1208) 860
          (by simp only [show signExtend21 (860 : BitVec 21) = (860 : Word) from by native_decide]
              bv_omega)
          hvV
        rw [hn4, hn8, hn12, hn16, hn20, hn24, hn28] at bspec
        have bframed := cpsTriple_frame_left _ _ _ _
          (progAt (base + 96) shr_phase_c **
           (.x0 ↦ᵣ (0 : Word)) **
           progAt base shr_phase_a **
           progAt (base + 68) shr_phase_b **
           progAt (base + 148) shr_body_7 **
           progAt (base + 192) shr_body_6 **
           progAt (base + 352) shr_body_4 **
           progAt (base + 468) shr_body_3 **
           progAt (base + 608) shr_body_2 **
           progAt (base + 772) shr_body_1 **
           progAt (base + 960) shr_body_0 **
           progAt (base + 1172) shr_zero_path **
           (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
           ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
          (by pcFree) bspec
        exact cpsTriple_consequence _ _ _ _ _ _
          (fun h hp => by
            rw [progAt_shr_body_5 (base + 260)] at hp
            rw [progAt_shr_phase_c (base + 96)]
            xperm_hyp hp)
          (fun h hq => by
            apply weaken_to_notTakenPost sp base s0 s1 s2 s3 s4 s5 s6 s7
            rw [progAt_shr_body_5 (base + 260)]
            xperm_hyp hq)
          bframed
      · -- body_6 at base+192
        have bspec := shr_body_6_spec (sp + 32)
          (s0 >>> (5 : BitVec 5).toNat) ((0 : Word) + signExtend12 6)
          (s0 &&& signExtend12 31) ((32 : Word) - (s0 &&& signExtend12 31))
          ((0 : Word) - (if BitVec.ult (0 : Word) (s0 &&& signExtend12 31) then (1 : Word) else 0))
          v0 v1 v2 v3 v4 v5 v6 v7
          (base + 192) (base + 1208) 952
          (by simp only [show signExtend21 (952 : BitVec 21) = (952 : Word) from by native_decide]
              bv_omega)
          hvV
        rw [hn4, hn8, hn12, hn16, hn20, hn24, hn28] at bspec
        have bframed := cpsTriple_frame_left _ _ _ _
          (progAt (base + 96) shr_phase_c **
           (.x0 ↦ᵣ (0 : Word)) **
           progAt base shr_phase_a **
           progAt (base + 68) shr_phase_b **
           progAt (base + 148) shr_body_7 **
           progAt (base + 260) shr_body_5 **
           progAt (base + 352) shr_body_4 **
           progAt (base + 468) shr_body_3 **
           progAt (base + 608) shr_body_2 **
           progAt (base + 772) shr_body_1 **
           progAt (base + 960) shr_body_0 **
           progAt (base + 1172) shr_zero_path **
           (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
           ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
          (by pcFree) bspec
        exact cpsTriple_consequence _ _ _ _ _ _
          (fun h hp => by
            rw [progAt_shr_body_6 (base + 192)] at hp
            rw [progAt_shr_phase_c (base + 96)]
            xperm_hyp hp)
          (fun h hq => by
            apply weaken_to_notTakenPost sp base s0 s1 s2 s3 s4 s5 s6 s7
            rw [progAt_shr_body_6 (base + 192)]
            xperm_hyp hq)
          bframed
      · -- body_7 at base+148
        have bspec := shr_body_7_spec (sp + 32)
          (s0 >>> (5 : BitVec 5).toNat) ((0 : Word) + signExtend12 6)
          (s0 &&& signExtend12 31) ((32 : Word) - (s0 &&& signExtend12 31))
          ((0 : Word) - (if BitVec.ult (0 : Word) (s0 &&& signExtend12 31) then (1 : Word) else 0))
          v0 v1 v2 v3 v4 v5 v6 v7
          (base + 148) (base + 1208) 1020
          (by simp only [show signExtend21 (1020 : BitVec 21) = (1020 : Word) from by native_decide]
              bv_omega)
          hvV
        rw [hn4, hn8, hn12, hn16, hn20, hn24, hn28] at bspec
        have bframed := cpsTriple_frame_left _ _ _ _
          (progAt (base + 96) shr_phase_c **
           (.x0 ↦ᵣ (0 : Word)) **
           progAt base shr_phase_a **
           progAt (base + 68) shr_phase_b **
           progAt (base + 192) shr_body_6 **
           progAt (base + 260) shr_body_5 **
           progAt (base + 352) shr_body_4 **
           progAt (base + 468) shr_body_3 **
           progAt (base + 608) shr_body_2 **
           progAt (base + 772) shr_body_1 **
           progAt (base + 960) shr_body_0 **
           progAt (base + 1172) shr_zero_path **
           (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
           ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
          (by pcFree) bspec
        exact cpsTriple_consequence _ _ _ _ _ _
          (fun h hp => by
            rw [progAt_shr_body_7 (base + 148)] at hp
            rw [progAt_shr_phase_c (base + 96)]
            xperm_hyp hp)
          (fun h hq => by
            apply weaken_to_notTakenPost sp base s0 s1 s2 s3 s4 s5 s6 s7
            rw [progAt_shr_body_7 (base + 148)]
            xperm_hyp hq)
          bframed))

-- ============================================================================
-- Section 4: Full composition theorem
-- ============================================================================

set_option maxHeartbeats 25600000 in
set_option maxRecDepth 4096 in
/-- Full spec for the 256-bit EVM SHR program.
    SHR(shift, value) = value >> shift. 302 instructions.
    Pops shift (sp) and value (sp+32), pushes result (sp+32), advances sp by 32.
    Shift limbs at sp..sp+28 are preserved.
    Result limbs at sp+32..sp+60 are overwritten.
    Code ownership via progAt (302 instrAt assertions) is preserved. -/
theorem evm_shr_spec (sp base : Addr)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (v0 v1 v2 v3 v4 v5 v6 v7 : Word)
    (r5 r6 r7 r10 r11 : Word)
    (hvS : ValidMemRange sp 8) (hvV : ValidMemRange (sp + 32) 8) :
    let exit := base + 1208
    cpsTriple base exit
      (progAt base evm_shr **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) **
       (.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ r11) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 36) ↦ₘ v1) ** ((sp + 40) ↦ₘ v2) ** ((sp + 44) ↦ₘ v3) **
       ((sp + 48) ↦ₘ v4) ** ((sp + 52) ↦ₘ v5) ** ((sp + 56) ↦ₘ v6) ** ((sp + 60) ↦ₘ v7))
      (progAt base evm_shr **
       (.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
       (regOwn .x10) ** (regOwn .x11) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
       (memOwn (sp + 32)) ** (memOwn (sp + 36)) ** (memOwn (sp + 40)) ** (memOwn (sp + 44)) **
       (memOwn (sp + 48)) ** (memOwn (sp + 52)) ** (memOwn (sp + 56)) ** (memOwn (sp + 60))) := by
  intro exit_def
  -- Step 0: Split progAt evm_shr into per-phase blocks (goal keeps progAt form)
  rw [progAt_evm_shr_split]
  -- Step 1: Get phase_a spec (uses instrAt form) and convert to progAt via consequence
  have pa_raw := shr_phase_a_spec sp r5 r10 s0 s1 s2 s3 s4 s5 s6 s7 base (base + 1172)
    (by have h : signExtend13 1120 = (1120 : Word) := by native_decide
        rw [h]; bv_omega)
    (by have h : signExtend13 1108 = (1108 : Word) := by native_decide
        rw [h]; bv_omega) hvS
  -- Wrap phase_a: strengthen pre (progAt → instrAt), weaken post (instrAt → progAt)
  -- For the postconditions, we use `show` + `rw` to fold instrAt back to progAt:
  --   show (progAt ... ** regs ** mem) h; rw [progAt_shr_phase_a]; exact (by xperm).mp hq
  have pa := cpsBranch_consequence _
    _ -- P (spec's pre, instrAt form, inferred)
    (progAt base shr_phase_a **
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    _ -- exit_t
    _ -- Q_t (spec's taken post, instrAt form, inferred)
    (progAt base shr_phase_a **
     (.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    _ -- exit_f
    _ -- Q_f (spec's not-taken post, instrAt form, inferred)
    (progAt base shr_phase_a **
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    (fun h hp => by rw [progAt_shr_phase_a base] at hp; xperm_hyp hp)
    (fun h hq => by
      -- hq : Q_t h (instrAt form from spec). Goal: Q_t' h (progAt form)
      -- Strategy: unfold progAt in the goal, then use xperm
      rw [progAt_shr_phase_a base]
      xperm_hyp hq)
    (fun h hq => by
      rw [progAt_shr_phase_a base]
      xperm_hyp hq)
    pa_raw
  clear pa_raw
  -- Step 2: Frame phase_a with remaining resources
  have pa_framed := cpsBranch_frame_left _ _ _ _ _ _
    (otherCode base **
     (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 36) ↦ₘ v1) ** ((sp + 40) ↦ₘ v2) ** ((sp + 44) ↦ₘ v3) **
     ((sp + 48) ↦ₘ v4) ** ((sp + 52) ↦ₘ v5) ** ((sp + 56) ↦ₘ v6) ** ((sp + 60) ↦ₘ v7))
    (pcFree_sepConj (pcFree_otherCode base) (by pcFree))
    pa
  clear pa
  -- Step 3: Merge taken/not-taken via cpsBranch_merge
  -- Goal has progAt form. pa_framed's Q_t and Q_f also have instrAt form from spec + frame.
  -- cpsBranch_consequence converts pa_framed's pre to match goal's pre (permutation).
  -- pa_framed's post (Q_t, Q_f) have instrAt for phase_a from spec output + frame.
  -- We pass identity on Q_t, Q_f; the branch subgoals will handle conversion.
  apply cpsBranch_merge base (base + 1172) (base + 68) (base + 1208) _ _ _ _
    (cpsBranch_consequence _ _ _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => hq)
      (fun h hq => hq)
      pa_framed)
  -- Step 3a: Taken path (zero_path): base+1172 -> base+1208
  · clear pa_framed
    -- Get zero_path spec (uses (base+1172)+N and (sp+32)+N address forms)
    have zp := shr_zero_path_spec sp v0 v1 v2 v3 v4 v5 v6 v7 (base + 1172) hvV
    have hzp_exit : (base + 1172 : Addr) + 36 = base + 1208 := by bv_omega
    rw [hzp_exit] at zp
    -- Frame with everything except zero_path's instrAt + .x12 + value_mem
    have zp_framed := cpsTriple_frame_left _ _ _ _
      (progAt base shr_phase_a **
       progAt (base + 68) shr_phase_b ** progAt (base + 96) shr_phase_c **
       progAt (base + 148) shr_body_7 ** progAt (base + 192) shr_body_6 **
       progAt (base + 260) shr_body_5 ** progAt (base + 352) shr_body_4 **
       progAt (base + 468) shr_body_3 ** progAt (base + 608) shr_body_2 **
       progAt (base + 772) shr_body_1 ** progAt (base + 960) shr_body_0 **
       (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
      (by pcFree) zp
    clear zp
    -- Unfold progAt_shr_zero_path in goal to get instrAt form (matching zp_framed)
    rw [progAt_shr_zero_path (base + 1172)]
    -- Address normalization: (sp + 32) + N → sp + (32+N) for memory addresses
    -- The goal and zp_framed both use (base+1172)+N and (sp+32)+N forms
    -- but pa_framed's Q_t uses sp+36 etc. We normalize hp in the pre-consequence.
    have hn4  : (sp + 32 : Word) + 4  = sp + 36 := by bv_omega
    have hn8  : (sp + 32 : Word) + 8  = sp + 40 := by bv_omega
    have hn12 : (sp + 32 : Word) + 12 = sp + 44 := by bv_omega
    have hn16 : (sp + 32 : Word) + 16 = sp + 48 := by bv_omega
    have hn20 : (sp + 32 : Word) + 20 = sp + 52 := by bv_omega
    have hn24 : (sp + 32 : Word) + 24 = sp + 56 := by bv_omega
    have hn28 : (sp + 32 : Word) + 28 = sp + 60 := by bv_omega
    -- Apply cpsTriple_consequence to bridge between goal and zp_framed
    exact cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by
        -- hp: pa_framed's taken post (progAt form, sp+36 mem addresses)
        -- Goal: zp_framed's pre (instrAt form with (base+1172)+N, (sp+32)+N addresses)
        -- Unfold progAt in hp, then un-normalize goal mem addresses to sp+36 form
        unfold otherCode at hp
        rw [progAt_shr_zero_path (base + 1172)] at hp
        -- Now hp has instrAt with (base+1172)+N and sp+36 (from pa_framed's Q_t)
        -- Goal has instrAt with (base+1172)+N and (sp+32)+N
        -- Normalize goal's mem addresses
        rw [hn4, hn8, hn12, hn16, hn20, hn24, hn28]
        xperm_hyp hp)
      (fun h hq => by
        -- hq: zp_framed's post (instrAt with (base+1172)+N, (sp+32)+N mem addresses)
        -- Goal: main theorem's R (instrAt with (base+1172)+N, but sp+36 mem addresses
        --        and regOwn/memOwn instead of concrete values)
        -- Step 1: Normalize mem addresses in hq to sp+36 form
        rw [hn4, hn8, hn12, hn16, hn20, hn24, hn28] at hq
        -- Step 2: Permute to CODE ** REGS_MEM form for weakening
        have hp1 : (
          (progAt base shr_phase_a **
           progAt (base + 68) shr_phase_b ** progAt (base + 96) shr_phase_c **
           progAt (base + 148) shr_body_7 ** progAt (base + 192) shr_body_6 **
           progAt (base + 260) shr_body_5 ** progAt (base + 352) shr_body_4 **
           progAt (base + 468) shr_body_3 ** progAt (base + 608) shr_body_2 **
           progAt (base + 772) shr_body_1 ** progAt (base + 960) shr_body_0 **
           ((base + 1172) ↦ᵢ .ADDI .x12 .x12 32) ** (((base + 1172) + 4) ↦ᵢ .SW .x12 .x0 0) **
           (((base + 1172) + 8) ↦ᵢ .SW .x12 .x0 4) ** (((base + 1172) + 12) ↦ᵢ .SW .x12 .x0 8) **
           (((base + 1172) + 16) ↦ᵢ .SW .x12 .x0 12) ** (((base + 1172) + 20) ↦ᵢ .SW .x12 .x0 16) **
           (((base + 1172) + 24) ↦ᵢ .SW .x12 .x0 20) ** (((base + 1172) + 28) ↦ᵢ .SW .x12 .x0 24) **
           (((base + 1172) + 32) ↦ᵢ .SW .x12 .x0 28)) **
          ((.x12 ↦ᵣ (sp + 32)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 36) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 44) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 52) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) ** ((sp + 60) ↦ₘ (0 : Word)) **
           (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
           (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
           (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
           ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))) h :=
          (congrFun (show _ = _ from by xperm) h).mp hq
        have hp2 := sepConj_mono_right (weaken_zp_post sp r6 r7 r11 s0 s1 s2 s3 s4 s5 s6 s7) h hp1
        exact (congrFun (show _ = _ from by xperm) h).mp hp2)
      zp_framed
  -- Step 3b: Not-taken path (phase_b + phase_c + bodies): base+68 -> base+1208
  · clear pa_framed
    -- The precondition has regOwn .x10. Extract r10 via intro/decompose.
    intro R hR s hPR hpc
    obtain ⟨hp, hcompat, hP, hRs, hdPR, huPR, hPP, hRR⟩ := hPR
    -- Move regOwn .x10 to tail via permutation
    have hPP' : ((progAt base shr_phase_a **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
       otherCode base **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 36) ↦ₘ v1) ** ((sp + 40) ↦ₘ v2) ** ((sp + 44) ↦ₘ v3) **
       ((sp + 48) ↦ₘ v4) ** ((sp + 52) ↦ₘ v5) ** ((sp + 56) ↦ₘ v6) ** ((sp + 60) ↦ₘ v7)) **
       regOwn .x10) hP := by
      xperm_hyp hPP
    obtain ⟨h1, h2, hd12, hu12, hh1, ⟨r10, hr10⟩⟩ := hPP'
    -- Reconstruct with .x10 ↦ᵣ r10 and permute to target order
    have hPP_new : (progAt base shr_phase_a **
       progAt (base + 68) shr_phase_b **
       progAt (base + 96) shr_phase_c **
       progAt (base + 148) shr_body_7 **
       progAt (base + 192) shr_body_6 **
       progAt (base + 260) shr_body_5 **
       progAt (base + 352) shr_body_4 **
       progAt (base + 468) shr_body_3 **
       progAt (base + 608) shr_body_2 **
       progAt (base + 772) shr_body_1 **
       progAt (base + 960) shr_body_0 **
       progAt (base + 1172) shr_zero_path **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 36) ↦ₘ v1) ** ((sp + 40) ↦ₘ v2) ** ((sp + 44) ↦ₘ v3) **
       ((sp + 48) ↦ₘ v4) ** ((sp + 52) ↦ₘ v5) ** ((sp + 56) ↦ₘ v6) ** ((sp + 60) ↦ₘ v7)) hP := by
      have h_inter : ((progAt base shr_phase_a **
         (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) **
         (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
         ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
         otherCode base **
         (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
         ((sp + 32) ↦ₘ v0) ** ((sp + 36) ↦ₘ v1) ** ((sp + 40) ↦ₘ v2) ** ((sp + 44) ↦ₘ v3) **
         ((sp + 48) ↦ₘ v4) ** ((sp + 52) ↦ₘ v5) ** ((sp + 56) ↦ₘ v6) ** ((sp + 60) ↦ₘ v7)) **
         (.x10 ↦ᵣ r10)) hP := ⟨h1, h2, hd12, hu12, hh1, hr10⟩
      unfold otherCode at h_inter
      exact (congrFun (by ac_rfl) hP).mp h_inter
    -- Now apply the core theorem
    have hPR_core : ((progAt base shr_phase_a **
       progAt (base + 68) shr_phase_b **
       progAt (base + 96) shr_phase_c **
       progAt (base + 148) shr_body_7 **
       progAt (base + 192) shr_body_6 **
       progAt (base + 260) shr_body_5 **
       progAt (base + 352) shr_body_4 **
       progAt (base + 468) shr_body_3 **
       progAt (base + 608) shr_body_2 **
       progAt (base + 772) shr_body_1 **
       progAt (base + 960) shr_body_0 **
       progAt (base + 1172) shr_zero_path **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 36) ↦ₘ v1) ** ((sp + 40) ↦ₘ v2) ** ((sp + 44) ↦ₘ v3) **
       ((sp + 48) ↦ₘ v4) ** ((sp + 52) ↦ₘ v5) ** ((sp + 56) ↦ₘ v6) ** ((sp + 60) ↦ₘ v7)) **
       R).holdsFor s :=
      ⟨hp, hcompat, hP, hRs, hdPR, huPR, hPP_new, hRR⟩
    have nt := evm_shr_not_taken_aux sp base s0 s1 s2 s3 s4 s5 s6 s7
      v0 v1 v2 v3 v4 v5 v6 v7 r6 r7 r10 r11 hvS hvV
    exact (cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => hp) (fun h hq => by unfold notTakenPost at hq; xperm_hyp hq)
      nt) R hR s hPR_core hpc

end EvmAsm
