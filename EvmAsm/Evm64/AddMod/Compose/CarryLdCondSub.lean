/-
  EvmAsm.Evm64.AddMod.Compose.CarryLdCondSub

  Phase-3 M3d for total ADDMOD (issue #9704): the sub-region code subsumptions
  that lift the two cond-subtract halves (`pass1take_clean` at byte 612, len 25;
  `pass2_owned` at byte 712, len 30) onto the total program code.

  The cond-subtract block `evm_addmod_carry_cond_sub` sits at total-program
  instruction index 153 (byte 612). Its first 25 instructions are the
  pass1take borrow chain + mask; the next 30 are the pass2 masked subtract.
  Rather than route through the whole-block `evm_addmod_carry_cond_sub_code`
  (which the M2 heartbeat trap made expensive to reconcile), we subsume each
  half directly into `evm_addmod_total_program_code` via `ofProg_mono_sub` at
  the appropriate instruction index (153 for pass1take, 178 for pass2) — the
  same technique `TotalBase` uses for the whole blocks. No disjointness needed.
-/

import EvmAsm.Evm64.AddMod.Compose.TotalBase
import EvmAsm.Evm64.AddMod.Compose.CondSubWrapper

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64

/-- Slice-equation tactic (mirror of `TotalBase.evm_addmod_total_slice_rfl`):
    unfolds the total program to its concrete instruction list so a
    `List.take .. (List.drop ..)` slice reduces by `rfl`. -/
local macro "addmod_total_slice_rfl" : tactic =>
  `(tactic| (
      unfold evm_addmod_total evm_addmod_prologue evm_add
        evm_addmod_phase1_carry evm_addmod_phase2_n_zero_test
        evm_addmod_carry_save_operands evm_addmod_carry_minus_one_args
        evm_addmod_carry_call_mod evm_addmod_carry_plus_one_args
        evm_addmod_carry_stage_low_args evm_addmod_carry_mod_add_stage
        evm_addmod_carry_cond_sub evm_addmod_phase2_mod_call
        evm_addmod_phase2_zero_path evm_addmod_epilogue
      simp only [seq, single]
      rfl))

/-- The pass1take borrow-chain + mask program (first 25 instrs of
    `evm_addmod_carry_cond_sub`). -/
def condSubPass1Prog : List Instr :=
  [.ADDI .x10 .x5 0, .LD .x6 .x12 0, .LD .x7 .x12 3872, .SLTU .x11 .x6 .x7,
   .LD .x6 .x12 8, .LD .x7 .x12 3880, .SLTU .x5 .x6 .x7, .SUB .x6 .x6 .x7,
   .SLTU .x7 .x6 .x11, .OR .x11 .x5 .x7, .LD .x6 .x12 16, .LD .x7 .x12 3888,
   .SLTU .x5 .x6 .x7, .SUB .x6 .x6 .x7, .SLTU .x7 .x6 .x11, .OR .x11 .x5 .x7,
   .LD .x6 .x12 24, .LD .x7 .x12 3896, .SLTU .x5 .x6 .x7, .SUB .x6 .x6 .x7,
   .SLTU .x7 .x6 .x11, .OR .x11 .x5 .x7, .XORI .x11 .x11 1, .OR .x11 .x10 .x11,
   .SUB .x11 .x0 .x11]

/-- The pass2 masked-subtract program (last 30 instrs of
    `evm_addmod_carry_cond_sub`). -/
def condSubPass2Prog : List Instr :=
  [.LD .x6 .x12 0, .LD .x7 .x12 3872, .AND .x7 .x7 .x11, .SLTU .x10 .x6 .x7,
   .SUB .x5 .x6 .x7, .SD .x12 .x5 0, .LD .x6 .x12 8, .LD .x7 .x12 3880,
   .AND .x7 .x7 .x11, .SLTU .x5 .x6 .x7, .SUB .x6 .x6 .x7, .SLTU .x7 .x6 .x10,
   .SUB .x6 .x6 .x10, .OR .x10 .x5 .x7, .SD .x12 .x6 8, .LD .x6 .x12 16,
   .LD .x7 .x12 3888, .AND .x7 .x7 .x11, .SLTU .x5 .x6 .x7, .SUB .x6 .x6 .x7,
   .SLTU .x7 .x6 .x10, .SUB .x6 .x6 .x10, .OR .x10 .x5 .x7, .SD .x12 .x6 16,
   .LD .x6 .x12 24, .LD .x7 .x12 3896, .AND .x7 .x7 .x11, .SUB .x6 .x6 .x7,
   .SUB .x6 .x6 .x10, .SD .x12 .x6 24]

/-- The 25-singleton union code of the `pass1take_clean` block. Matches the
    inline code term in `evm_addmod_cond_sub_pass1take_clean`. -/
abbrev condSubPass1Code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x10 .x5 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x7 .x12 (3872 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x11 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x6 .x12 (8 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x12 (3880 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SLTU .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 32) (.SLTU .x7 .x6 .x11))
  (CodeReq.union (CodeReq.singleton (base + 36) (.OR .x11 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x6 .x12 (16 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 44) (.LD .x7 .x12 (3888 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 48) (.SLTU .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 52) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 56) (.SLTU .x7 .x6 .x11))
  (CodeReq.union (CodeReq.singleton (base + 60) (.OR .x11 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 64) (.LD .x6 .x12 (24 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 68) (.LD .x7 .x12 (3896 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 72) (.SLTU .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 76) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 80) (.SLTU .x7 .x6 .x11))
  (CodeReq.union (CodeReq.singleton (base + 84) (.OR .x11 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 88) (.XORI .x11 .x11 (1 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 92) (.OR .x11 .x10 .x11))
   (CodeReq.singleton (base + 96) (.SUB .x11 .x0 .x11)))))))))))))))))))))))))

/-- The 30-singleton union code of the `pass2_owned` block. Matches the inline
    code term in `evm_addmod_cond_sub_pass2_owned` / `..._spec_within`. -/
abbrev condSubPass2Code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x7 .x12 (3872 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x11))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x10 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x5 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x6 .x12 (8 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x7 .x12 (3880 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 32) (.AND .x7 .x7 .x11))
  (CodeReq.union (CodeReq.singleton (base + 36) (.SLTU .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 44) (.SLTU .x7 .x6 .x10))
  (CodeReq.union (CodeReq.singleton (base + 48) (.SUB .x6 .x6 .x10))
  (CodeReq.union (CodeReq.singleton (base + 52) (.OR .x10 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 56) (.SD .x12 .x6 (8 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 60) (.LD .x6 .x12 (16 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 64) (.LD .x7 .x12 (3888 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 68) (.AND .x7 .x7 .x11))
  (CodeReq.union (CodeReq.singleton (base + 72) (.SLTU .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 76) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 80) (.SLTU .x7 .x6 .x10))
  (CodeReq.union (CodeReq.singleton (base + 84) (.SUB .x6 .x6 .x10))
  (CodeReq.union (CodeReq.singleton (base + 88) (.OR .x10 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 92) (.SD .x12 .x6 (16 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 96) (.LD .x6 .x12 (24 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 100) (.LD .x7 .x12 (3896 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 104) (.AND .x7 .x7 .x11))
  (CodeReq.union (CodeReq.singleton (base + 108) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 112) (.SUB .x6 .x6 .x10))
   (CodeReq.singleton (base + 116) (.SD .x12 .x6 (24 : BitVec 12)))))))))))))))))))))))))))))))

theorem condSubPass1Code_eq_ofProg (base : Word) :
    condSubPass1Code base = CodeReq.ofProg base condSubPass1Prog := by
  unfold condSubPass1Code condSubPass1Prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right, BitVec.add_assoc, BitVec.reduceAdd]
  rfl

theorem condSubPass2Code_eq_ofProg (base : Word) :
    condSubPass2Code base = CodeReq.ofProg base condSubPass2Prog := by
  unfold condSubPass2Code condSubPass2Prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right, BitVec.add_assoc, BitVec.reduceAdd]
  rfl

/-- The pass1take half (byte 612, instr 153, len 25) is subsumed by the total
    program code. -/
theorem evm_addmod_total_program_code_cond_sub_pass1_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, condSubPass1Code (base + 612) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  intro a i h
  rw [condSubPass1Code_eq_ofProg] at h
  revert a i h
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 612)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    condSubPass1Prog 153
    (by bv_omega) ?_ ?_ ?_
  · addmod_total_slice_rfl
  · rw [evm_addmod_total_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The pass2 half (byte 712, instr 178, len 30) is subsumed by the total
    program code. -/
theorem evm_addmod_total_program_code_cond_sub_pass2_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, condSubPass2Code (base + 712) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  intro a i h
  rw [condSubPass2Code_eq_ofProg] at h
  revert a i h
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 712)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    condSubPass2Prog 178
    (by bv_omega) ?_ ?_ ?_
  · addmod_total_slice_rfl
  · rw [evm_addmod_total_length]; decide
  · rw [evm_addmod_total_length]; decide

end EvmAsm.Evm64.AddMod.Compose
