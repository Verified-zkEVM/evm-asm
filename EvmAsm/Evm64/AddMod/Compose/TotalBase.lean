/-
  EvmAsm.Evm64.AddMod.Compose.TotalBase

  Composition infrastructure for the total three-way ADDMOD program
  (`evm_addmod_total`, issue #9704): the `CodeReq.ofProg` handle plus
  per-block subsumption lemmas tying each sub-block's `CodeReq.ofProg`
  handle back to `evm_addmod_total_program_code`.

  Mirrors `Compose/Base.lean` (the handle for the legacy no-carry-only
  `evm_addmod`), extended to the 19 sub-blocks of the total layout. Each
  helper is a thin wrapper around `CodeReq.ofProg_mono_sub` with the byte
  offset / instruction index / range bound discharged by `decide` /
  `bv_omega`. No proof engineering beyond structural slicing.

  Block layout (instruction index → byte offset; see the layout table on
  `evm_addmod_total` in `AddMod/Program.lean`):

    prologue             : idx   0  byte   0  (30 instr)
    phase1_carry         : idx  30  byte 120  (1)
    phase2_n_zero_test   : idx  31  byte 124  (8, BEQ @ 152 → +692)
    carry-test BEQ x7    : idx  39  byte 156  (1, +680)
    carry_save_operands  : idx  40  byte 160  (16)
    carry_minus_one_args : idx  56  byte 224  (5)
    carry_call_mod 1     : idx  61  byte 244  (2)
    carry_plus_one_args  : idx  63  byte 252  (24)
    carry_call_mod 2     : idx  87  byte 348  (2)
    carry_stage_low_args : idx  89  byte 356  (24)
    carry_call_mod 3     : idx 113  byte 452  (2)
    carry_mod_add_stage  : idx 115  byte 460  (8)
    embedded evm_add     : idx 123  byte 492  (30)
    carry_cond_sub       : idx 153  byte 612  (55)
    carry exit JAL       : idx 208  byte 832  (1, +32)
    phase2_mod_call NC   : idx 209  byte 836  (1)
    no-carry exit JAL    : idx 210  byte 840  (1, +24)
    phase2_zero_path     : idx 211  byte 844  (4)
    epilogue             : idx 215  byte 860  (1)
    end                  : idx 216  byte 864
-/

import EvmAsm.Evm64.AddMod.LimbSpec
import EvmAsm.Evm64.AddMod.AddrNorm

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64
open EvmAsm.Evm64

-- ============================================================================
-- Top-level program-code handle
-- ============================================================================

/-- `CodeReq.ofProg` handle for the assembled total ADDMOD Program
    (216 instructions, 864 bytes). The four signed 21-bit parameters are
    the byte offsets from each `JAL x1` MOD-call site to the entry of the
    appended `evm_mod_callable_v5`; they are pinned by the surrounding
    dispatcher frame (canonically 624 / 520 / 416 / 32). -/
abbrev evm_addmod_total_program_code (base : Word)
    (modOff1 modOff2 modOff3 modOffNC : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)

-- ============================================================================
-- Per-block CodeReq subsumption: sub-block code ⊆ evm_addmod_total_program_code
-- ============================================================================

/-- Common slice-equation tactic for the `mono_sub` calls below. All the
    sub-blocks of `evm_addmod_total` reduce to plain `List Instr` literals
    once `seq` and `single` are unfolded; `rfl` closes the resulting
    `List.take .. (List.drop ..) = ..` goal since the only remaining free
    variables (the four `modOff*`) appear identically on both sides as
    single concrete `JAL .x1 _` constructors. -/
local macro "evm_addmod_total_slice_rfl" : tactic =>
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

/-- The `evm_addmod_prologue` sub-block (30 instrs at byte 0) is subsumed
    by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_prologue_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg base evm_addmod_prologue) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base base
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    evm_addmod_prologue 0
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_prologue_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The `evm_addmod_phase1_carry` sub-block (1 instr at byte 120) is
    subsumed by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_phase1_carry_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 120) evm_addmod_phase1_carry) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 120)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    evm_addmod_phase1_carry 30
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_phase1_carry_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The `evm_addmod_phase2_n_zero_test 692` sub-block (8 instrs at byte 124)
    is subsumed by `evm_addmod_total_program_code`. The total layout pins the
    zero-path skip offset to 692 (byte 152 → byte 844). -/
theorem evm_addmod_total_program_code_n_zero_test_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 124)
        (evm_addmod_phase2_n_zero_test 692)) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 124)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    (evm_addmod_phase2_n_zero_test 692) 31
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_phase2_n_zero_test_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The carry-test `BEQ x7, x0, 680` (1 instr at byte 156) is subsumed by
    `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_carry_test_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 156) (BEQ .x7 .x0 680)) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 156)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    (BEQ .x7 .x0 680) 39
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The `evm_addmod_carry_save_operands` sub-block (16 instrs at byte 160)
    is subsumed by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_carry_save_operands_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 160) evm_addmod_carry_save_operands) a
        = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 160)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    evm_addmod_carry_save_operands 40
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_carry_save_operands_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The `evm_addmod_carry_minus_one_args` sub-block (5 instrs at byte 224)
    is subsumed by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_carry_minus_one_args_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 224) evm_addmod_carry_minus_one_args) a
        = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 224)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    evm_addmod_carry_minus_one_args 56
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_carry_minus_one_args_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The first `evm_addmod_carry_call_mod modOff1` sub-block (2 instrs at
    byte 244) is subsumed by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_carry_call1_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 244)
        (evm_addmod_carry_call_mod modOff1)) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 244)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    (evm_addmod_carry_call_mod modOff1) 61
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_carry_call_mod_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The `evm_addmod_carry_plus_one_args` sub-block (24 instrs at byte 252)
    is subsumed by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_carry_plus_one_args_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 252) evm_addmod_carry_plus_one_args) a
        = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 252)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    evm_addmod_carry_plus_one_args 63
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_carry_plus_one_args_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The second `evm_addmod_carry_call_mod modOff2` sub-block (2 instrs at
    byte 348) is subsumed by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_carry_call2_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 348)
        (evm_addmod_carry_call_mod modOff2)) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 348)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    (evm_addmod_carry_call_mod modOff2) 87
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_carry_call_mod_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The `evm_addmod_carry_stage_low_args` sub-block (24 instrs at byte 356)
    is subsumed by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_carry_stage_low_args_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 356) evm_addmod_carry_stage_low_args) a
        = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 356)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    evm_addmod_carry_stage_low_args 89
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_carry_stage_low_args_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The third `evm_addmod_carry_call_mod modOff3` sub-block (2 instrs at
    byte 452) is subsumed by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_carry_call3_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 452)
        (evm_addmod_carry_call_mod modOff3)) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 452)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    (evm_addmod_carry_call_mod modOff3) 113
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_carry_call_mod_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The `evm_addmod_carry_mod_add_stage` sub-block (8 instrs at byte 460)
    is subsumed by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_carry_mod_add_stage_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 460) evm_addmod_carry_mod_add_stage) a
        = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 460)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    evm_addmod_carry_mod_add_stage 115
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_carry_mod_add_stage_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The embedded `evm_add` (the carry-path modular-add sum; 30 instrs at
    byte 492) is subsumed by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_carry_evm_add_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 492) evm_add) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 492)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    evm_add 123
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The `evm_addmod_carry_cond_sub` sub-block (55 instrs at byte 612) is
    subsumed by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_carry_cond_sub_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 612) evm_addmod_carry_cond_sub) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 612)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    evm_addmod_carry_cond_sub 153
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_carry_cond_sub_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The carry-path exit `JAL x0, 32` (1 instr at byte 832) is subsumed by
    `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_carry_exit_jal_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 832) (JAL .x0 32)) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 832)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    (JAL .x0 32) 208
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The no-carry `evm_addmod_phase2_mod_call modOffNC` (1 instr at byte 836)
    is subsumed by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_nc_mod_call_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 836)
        (evm_addmod_phase2_mod_call modOffNC)) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 836)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    (evm_addmod_phase2_mod_call modOffNC) 209
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_phase2_mod_call_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The no-carry exit `JAL x0, 24` (1 instr at byte 840) is subsumed by
    `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_nc_exit_jal_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 840) (JAL .x0 24)) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 840)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    (JAL .x0 24) 210
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The `evm_addmod_phase2_zero_path` sub-block (4 instrs at byte 844) is
    subsumed by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_zero_path_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 844) evm_addmod_phase2_zero_path) a
        = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 844)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    evm_addmod_phase2_zero_path 211
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_phase2_zero_path_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The `evm_addmod_epilogue` sub-block (1 instr at byte 860) is subsumed
    by `evm_addmod_total_program_code`. -/
theorem evm_addmod_total_program_code_epilogue_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 860) evm_addmod_epilogue) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 860)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    evm_addmod_epilogue 215
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_total_slice_rfl
  · rw [evm_addmod_total_length, evm_addmod_epilogue_length]
  · rw [evm_addmod_total_length]; decide

end EvmAsm.Evm64.AddMod.Compose
