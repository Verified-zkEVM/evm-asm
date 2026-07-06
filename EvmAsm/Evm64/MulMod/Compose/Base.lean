/-
  EvmAsm.Evm64.MulMod.Compose.Base

  Shared composition infrastructure for MULMOD: `evm_mulmod_program_code`
  (the `CodeReq.ofProg` handle for the assembled top-level `evm_mulmod`) and
  sub-block subsumption/lift helpers used by the later stack-spec composition.
-/

import EvmAsm.Evm64.MulMod.LimbSpec
import EvmAsm.Evm64.MulMod.ProductLayoutSpec
import EvmAsm.Evm64.MulMod.AddrNorm

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- `CodeReq.ofProg` handle for the assembled top-level `evm_mulmod` program. -/
abbrev evm_mulmod_program_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_mulmod

local macro "evm_mulmod_slice_rfl" : tactic =>
  `(tactic|
    first
      | rfl
      | (unfold evm_mulmod evm_mulmod_nonzero_or_zero_prefix
            evm_mulmod_reduce_zero_path evm_mulmod_epilogue
            evm_mulmod_zero_path_skip_nonzero evm_mulmod_product_layout
            evm_mulmod_product_zero evm_mulmod_product_add_partial
            evm_mulmod_product_propagate_carry evm_mulmod_reduce512 evm_mulmod_reduce512_loop
            evm_mulmod_reduce512_write_result evm_mulmod_reduce512_init
            LD OR' BNE SD ADDI JAL MUL MULHU ADD SLTU single seq
         rfl))

private theorem append_assoc_seven {α : Type} (a b c d e f g r : List α) :
    (a ++ (b ++ (c ++ (d ++ (e ++ (f ++ g)))))) ++ r =
      a ++ (b ++ (c ++ (d ++ (e ++ (f ++ (g ++ r)))))) := by
  repeat rw [List.append_assoc]

private theorem append_assoc_eight {α : Type} (a b c d e f g h r : List α) :
    (a ++ (b ++ (c ++ (d ++ (e ++ (f ++ (g ++ h))))))) ++ r =
      a ++ (b ++ (c ++ (d ++ (e ++ (f ++ (g ++ (h ++ r))))))) := by
  repeat rw [List.append_assoc]

private theorem append_assoc_product_layout {α : Type} (a b c d e f : List α) :
    (a ++ (b ++ (c ++ d))) ++ (e ++ f) =
      a ++ (b ++ (c ++ (d ++ (e ++ f)))) := by
  repeat rw [List.append_assoc]

/-- The zero/nonzero modulus prefix block (8 instrs at offset 0) is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_nonzero_or_zero_prefix_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg base evm_mulmod_nonzero_or_zero_prefix) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base base evm_mulmod
    evm_mulmod_nonzero_or_zero_prefix 0 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length, evm_mulmod_nonzero_or_zero_prefix_length]; decide
  · rw [evm_mulmod_length]; decide

/-- The zero-result path block (4 instrs at offset 32) is subsumed by the
    top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_reduce_zero_path_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 32) evm_mulmod_reduce_zero_path) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 32) evm_mulmod
    evm_mulmod_reduce_zero_path 8 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length, evm_mulmod_reduce_zero_path_length]; decide
  · rw [evm_mulmod_length]; decide

/-- The zero-path epilogue block (1 instr at offset 48) is subsumed by the
    top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_epilogue_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 48) evm_mulmod_epilogue) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 48) evm_mulmod
    evm_mulmod_epilogue 12 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length, evm_mulmod_epilogue_length]; decide
  · rw [evm_mulmod_length]; decide

/-- The jump over the nonzero path (1 instr at offset 52) is subsumed by the
    top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_zero_path_skip_nonzero_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 52) evm_mulmod_zero_path_skip_nonzero) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 52) evm_mulmod
    evm_mulmod_zero_path_skip_nonzero 13 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length, evm_mulmod_zero_path_skip_nonzero_length]; decide
  · rw [evm_mulmod_length]; decide

/-- The first nonzero-path block, which zeroes the product window at offset 56,
    is subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_zero_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 56) evm_mulmod_product_zero) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 56) evm_mulmod
    evm_mulmod_product_zero 14 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length, evm_mulmod_product_zero_length]; decide
  · rw [evm_mulmod_length]; decide

/-- The full product-layout block (440 instrs at offset 56) is subsumed by the
    top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_layout_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_layout_code (base + 56)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  intro a i h
  dsimp [evm_mulmod_product_layout_code, evm_mulmod_program_code] at h ⊢
  let pre : Program :=
    evm_mulmod_nonzero_or_zero_prefix ;;
    evm_mulmod_reduce_zero_path ;;
    evm_mulmod_epilogue ;;
    evm_mulmod_zero_path_skip_nonzero
  let mid : Program := evm_mulmod_product_layout
  let suf : Program := evm_mulmod_reduce512
  have hpre_len : pre.length = 14 := by
    unfold pre
    simp only [seq, Program.length_append, evm_mulmod_nonzero_or_zero_prefix_length,
      evm_mulmod_reduce_zero_path_length, evm_mulmod_epilogue_length,
      evm_mulmod_zero_path_skip_nonzero_length]
  have haddr : base + 56#64 = base + BitVec.ofNat 64 (4 * pre.length) := by
    rw [hpre_len]
  have hfull : pre ++ mid ++ suf = evm_mulmod := by
    calc
      pre ++ mid ++ suf = pre ++ (mid ++ suf) := List.append_assoc pre mid suf
      _ = evm_mulmod := by
        unfold pre mid suf evm_mulmod
        simpa only [seq] using append_assoc_product_layout
          evm_mulmod_nonzero_or_zero_prefix evm_mulmod_reduce_zero_path
          evm_mulmod_epilogue evm_mulmod_zero_path_skip_nonzero
          evm_mulmod_product_layout evm_mulmod_reduce512
  rw [← hfull]
  rw [haddr] at h
  exact CodeReq.ofProg_mono_subrange base pre mid suf (by
    have hlen : List.length (pre ++ mid ++ suf) = List.length evm_mulmod := by
      rw [hfull]
    change 4 * List.length (pre ++ mid ++ suf) < 2 ^ 64
    rw [hlen, evm_mulmod_length]
    decide) a i h

/-- The finish suffix of the first product partial at offset 140 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_first_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 140)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3944 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 140) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3944 : BitVec 12)) 35 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the first product partial at offset 148 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_first_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 148)
        (evm_mulmod_product_propagate_carry [3952, 3960, 3968, 3976, 3984, 3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 148) evm_mulmod
    (evm_mulmod_product_propagate_carry [3952, 3960, 3968, 3976, 3984, 3992]) 37 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The finish suffix of the second product partial at offset 296 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_second_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 296)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3952 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 296) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3952 : BitVec 12)) 74 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the second product partial at offset 304 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_second_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 304)
        (evm_mulmod_product_propagate_carry [3960, 3968, 3976, 3984, 3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 304) evm_mulmod
    (evm_mulmod_product_propagate_carry [3960, 3968, 3976, 3984, 3992]) 76 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The finish suffix of the third product partial at offset 436 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_third_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 436)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3952 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 436) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3952 : BitVec 12)) 109 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the third product partial at offset 444 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_third_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 444)
        (evm_mulmod_product_propagate_carry [3960, 3968, 3976, 3984, 3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 444) evm_mulmod
    (evm_mulmod_product_propagate_carry [3960, 3968, 3976, 3984, 3992]) 111 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The finish suffix of the fourth product partial at offset 576 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_fourth_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 576)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3960 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 576) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3960 : BitVec 12)) 144 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the fourth product partial at offset 584 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_fourth_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 584)
        (evm_mulmod_product_propagate_carry [3968, 3976, 3984, 3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 584) evm_mulmod
    (evm_mulmod_product_propagate_carry [3968, 3976, 3984, 3992]) 146 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The finish suffix of the fifth product partial at offset 700 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_fifth_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 700)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3960 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 700) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3960 : BitVec 12)) 175 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the fifth product partial at offset 708 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_fifth_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 708)
        (evm_mulmod_product_propagate_carry [3968, 3976, 3984, 3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 708) evm_mulmod
    (evm_mulmod_product_propagate_carry [3968, 3976, 3984, 3992]) 177 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The finish suffix of the sixth product partial at offset 824 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_sixth_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 824)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3960 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 824) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3960 : BitVec 12)) 206 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the sixth product partial at offset 832 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_sixth_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 832)
        (evm_mulmod_product_propagate_carry [3968, 3976, 3984, 3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 832) evm_mulmod
    (evm_mulmod_product_propagate_carry [3968, 3976, 3984, 3992]) 208 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The finish suffix of the seventh product partial at offset 948 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_seventh_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 948)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3968 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 948) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3968 : BitVec 12)) 237 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the seventh product partial at offset 956 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_seventh_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 956)
        (evm_mulmod_product_propagate_carry [3976, 3984, 3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 956) evm_mulmod
    (evm_mulmod_product_propagate_carry [3976, 3984, 3992]) 239 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The finish suffix of the eighth product partial at offset 1056 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_eighth_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1056)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3968 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1056) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3968 : BitVec 12)) 264 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the eighth product partial at offset 1064 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_eighth_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1064)
        (evm_mulmod_product_propagate_carry [3976, 3984, 3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1064) evm_mulmod
    (evm_mulmod_product_propagate_carry [3976, 3984, 3992]) 266 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The finish suffix of the ninth product partial at offset 1164 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_ninth_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1164)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3968 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1164) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3968 : BitVec 12)) 291 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the ninth product partial at offset 1172 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_ninth_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1172)
        (evm_mulmod_product_propagate_carry [3976, 3984, 3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1172) evm_mulmod
    (evm_mulmod_product_propagate_carry [3976, 3984, 3992]) 293 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The reducer initialization block at offset 1816 is subsumed by the top-level
    `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_reduce512_init_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1816) evm_mulmod_reduce512_init) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1816) evm_mulmod
    evm_mulmod_reduce512_init 454 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length, evm_mulmod_reduce512_init_length]; decide
  · rw [evm_mulmod_length]; decide

/-- The reducer result-copy block at offset 2124 is subsumed by the top-level
    `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_reduce512_write_result_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 2124) evm_mulmod_reduce512_write_result) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  intro a i h
  unfold evm_mulmod_program_code
  let pre : Program :=
    evm_mulmod_nonzero_or_zero_prefix ;;
    evm_mulmod_reduce_zero_path ;;
    evm_mulmod_epilogue ;;
    evm_mulmod_zero_path_skip_nonzero ;;
    evm_mulmod_product_layout ;;
    evm_mulmod_reduce512_init ;;
    evm_mulmod_reduce512_loop
  let mid : Program := evm_mulmod_reduce512_write_result
  let suf : Program := evm_mulmod_epilogue
  have hpre_len : pre.length = 531 := by
    unfold pre
    simp only [seq, Program.length_append, evm_mulmod_nonzero_or_zero_prefix_length,
      evm_mulmod_reduce_zero_path_length, evm_mulmod_epilogue_length,
      evm_mulmod_zero_path_skip_nonzero_length, evm_mulmod_product_layout_length,
      evm_mulmod_reduce512_init_length, evm_mulmod_reduce512_loop_length]
  have haddr : base + BitVec.ofNat 64 (4 * pre.length) = base + 2124 := by
    rw [hpre_len]
    bv_omega
  have hfull : pre ++ mid ++ suf = evm_mulmod := by
    calc
      pre ++ mid ++ suf = pre ++ (mid ++ suf) := List.append_assoc pre mid suf
      _ = evm_mulmod := by
        unfold pre mid suf evm_mulmod evm_mulmod_reduce512
        simpa only [seq] using
          append_assoc_seven evm_mulmod_nonzero_or_zero_prefix
            evm_mulmod_reduce_zero_path evm_mulmod_epilogue
            evm_mulmod_zero_path_skip_nonzero evm_mulmod_product_layout
            evm_mulmod_reduce512_init evm_mulmod_reduce512_loop
            (evm_mulmod_reduce512_write_result ++ evm_mulmod_epilogue)
  rw [← hfull]
  rw [← haddr] at h
  exact CodeReq.ofProg_mono_subrange base pre mid suf (by
    have hlen : List.length (pre ++ mid ++ suf) = List.length evm_mulmod := by
      rw [hfull]
    change 4 * List.length (pre ++ mid ++ suf) < 2 ^ 64
    rw [hlen, evm_mulmod_length]
    decide) a i h

/-- The final reducer epilogue at offset 2156 is subsumed by the top-level
    `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_reduce512_epilogue_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 2156) evm_mulmod_epilogue) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  intro a i h
  unfold evm_mulmod_program_code
  let pre : Program :=
    evm_mulmod_nonzero_or_zero_prefix ;;
    evm_mulmod_reduce_zero_path ;;
    evm_mulmod_epilogue ;;
    evm_mulmod_zero_path_skip_nonzero ;;
    evm_mulmod_product_layout ;;
    evm_mulmod_reduce512_init ;;
    evm_mulmod_reduce512_loop ;;
    evm_mulmod_reduce512_write_result
  let mid : Program := evm_mulmod_epilogue
  let suf : Program := []
  have hpre_len : pre.length = 539 := by
    unfold pre
    simp only [seq, Program.length_append,
      evm_mulmod_nonzero_or_zero_prefix_length, evm_mulmod_reduce_zero_path_length,
      evm_mulmod_epilogue_length, evm_mulmod_zero_path_skip_nonzero_length,
      evm_mulmod_product_layout_length, evm_mulmod_reduce512_init_length,
      evm_mulmod_reduce512_loop_length, evm_mulmod_reduce512_write_result_length]
  have haddr : base + BitVec.ofNat 64 (4 * pre.length) = base + 2156 := by
    rw [hpre_len]
    bv_omega
  have hfull : pre ++ mid ++ suf = evm_mulmod := by
    calc
      pre ++ mid ++ suf = pre ++ (mid ++ suf) := List.append_assoc pre mid suf
      _ = evm_mulmod := by
        unfold pre mid suf evm_mulmod evm_mulmod_reduce512
        simpa only [seq, List.append_nil] using
          append_assoc_eight evm_mulmod_nonzero_or_zero_prefix
            evm_mulmod_reduce_zero_path evm_mulmod_epilogue
            evm_mulmod_zero_path_skip_nonzero evm_mulmod_product_layout
            evm_mulmod_reduce512_init evm_mulmod_reduce512_loop
            evm_mulmod_reduce512_write_result evm_mulmod_epilogue
  rw [← hfull]
  rw [← haddr] at h
  exact CodeReq.ofProg_mono_subrange base pre mid suf (by
    have hlen : List.length (pre ++ mid ++ suf) = List.length evm_mulmod := by
      rw [hfull]
    change 4 * List.length (pre ++ mid ++ suf) < 2 ^ 64
    rw [hlen, evm_mulmod_length]
    decide) a i h

/-- Prefix branch spec lifted from its sub-block `CodeReq.ofProg` handle onto
    `evm_mulmod_program_code`. -/
theorem evm_mulmod_nonzero_or_zero_prefix_evm_mulmod_spec_within
    (sp v5Old v6Old n0 n1 n2 n3 : Word) (base : Word) :
    let orAll := n0 ||| n1 ||| n2 ||| n3
    cpsBranchWithin 8 base (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n3))
      ((base + 28) + signExtend13 (28 : BitVec 13))
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n3) **
         ⌜orAll ≠ 0⌝)
      (base + 32)
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n3) **
         ⌜orAll = 0⌝) := by
  intro orAll
  exact cpsBranchWithin_extend_code
    (h := evm_mulmod_nonzero_or_zero_prefix_spec_within sp v5Old v6Old n0 n1 n2 n3 base)
    (hmono := evm_mulmod_program_code_nonzero_or_zero_prefix_sub base)

/-- Zero-result path spec lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_reduce_zero_path_evm_mulmod_spec_within
    (sp m0 m1 m2 m3 : Word) (base : Word) :
    cpsTripleWithin 4 (base + 32) ((base + 32) + 16) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ m3))
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ (0 : Word))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_reduce_zero_path_ofProg_spec_within sp m0 m1 m2 m3 (base + 32))
    (hmono := evm_mulmod_program_code_reduce_zero_path_sub base)

/-- Zero-path epilogue spec lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_epilogue_evm_mulmod_spec_within
    (sp : Word) (base : Word) :
    cpsTripleWithin 1 (base + 48) ((base + 48) + 4) (evm_mulmod_program_code base)
      (.x12 ↦ᵣ sp)
      (.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_epilogue_spec_within sp (base + 48))
    (hmono := evm_mulmod_program_code_epilogue_sub base)

/-- Zero-path skip spec lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_zero_path_skip_nonzero_evm_mulmod_spec_within
    (base : Word) :
    cpsTripleWithin 1 (base + 52) ((base + 52) + signExtend21 (2108 : BitVec 21))
      (evm_mulmod_program_code base)
      empAssertion
      empAssertion :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_zero_path_skip_nonzero_spec_within (base + 52))
    (hmono := evm_mulmod_program_code_zero_path_skip_nonzero_sub base)


/-- Product-window zeroing spec lifted onto `evm_mulmod_program_code` at the
    start of the nonzero path. -/
theorem evm_mulmod_product_zero_evm_mulmod_spec_within (sp : Word) (base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 8 (base + 56) ((base + 56) + 32) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) **
       ((sp + 56) ↦ₘ b3) **
       ((sp + 64) ↦ₘ n0) ** ((sp + 72) ↦ₘ n1) ** ((sp + 80) ↦ₘ n2) **
       ((sp + 88) ↦ₘ n3) **
       ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ p0) **
       ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ p1) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ p2) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      (evmMulModProductZeroPost sp a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_zero_spec_within sp (base + 56)
      a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 p0 p1 p2 p3 p4 p5 p6 p7)
    (hmono := evm_mulmod_program_code_product_zero_sub base)


/-- Full product-layout spec lifted onto `evm_mulmod_program_code` at the start
    of the nonzero path. -/
theorem evm_mulmod_product_layout_evm_mulmod_spec_within
    (sp base : Word) (a b n : EvmWord)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 440 (base + 56) ((base + 56) + 1760) (evm_mulmod_program_code base)
      (evmMulModProductLayoutPre sp a b n p0 p1 p2 p3 p4 p5 p6 p7 **
       ((.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) **
        (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
        (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old)))
      (evmMulModProductLayoutPost sp a b n ** evmMulModProductLayoutScratchPost) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_layout_spec_within sp (base + 56) a b n
      p0 p1 p2 p3 p4 p5 p6 p7
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_layout_sub base)


/-- Reducer-initialization spec lifted onto `evm_mulmod_program_code` at the
    start of the 512-bit reduction path. -/
theorem evm_mulmod_reduce512_init_evm_mulmod_spec_within (sp : Word) (base : Word)
    (v16Old v18Old r0 r1 r2 r3 : Word) :
    cpsTripleWithin 6 (base + 1816) ((base + 1816) + 24) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3))
      ((.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ (sp + signExtend12 (3992 : BitVec 12))) **
       (.x18 ↦ᵣ (signExtend12 (8 : BitVec 12))) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ (0 : Word))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_reduce512_init_spec_within sp (base + 1816)
      v16Old v18Old r0 r1 r2 r3)
    (hmono := evm_mulmod_program_code_reduce512_init_sub base)


/-- Reducer result-copy spec lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_reduce512_write_result_evm_mulmod_spec_within (sp : Word) (base : Word)
    (v5Old r0 r1 r2 r3 m0 m1 m2 m3 : Word) :
    cpsTripleWithin 8 (base + 2124) ((base + 2124) + 32) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5Old) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ m3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ r3)) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_reduce512_write_result_spec_within sp (base + 2124)
      v5Old r0 r1 r2 r3 m0 m1 m2 m3)
    (hmono := evm_mulmod_program_code_reduce512_write_result_sub base)


/-- Final reducer epilogue spec lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_reduce512_epilogue_evm_mulmod_spec_within
    (sp : Word) (base : Word) :
    cpsTripleWithin 1 (base + 2156) ((base + 2156) + 4) (evm_mulmod_program_code base)
      (.x12 ↦ᵣ sp)
      (.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_epilogue_spec_within sp (base + 2156))
    (hmono := evm_mulmod_program_code_reduce512_epilogue_sub base)


/-- First product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_first_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p2 p3 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 24 (base + 148) ((base + 148) + 96) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ p2) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5
              (mulModCarryStepCarry p4
                (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 carry)))))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5
              (mulModCarryStepCarry p4
                (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 carry)))))) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ mulModCarryStepValue p2 carry) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p3 (mulModCarryStepCarry p2 carry)) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 carry))) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p5
           (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 carry)))) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p6
           (mulModCarryStepCarry p5
             (mulModCarryStepCarry p4 (mulModCarryStepCarry p3
               (mulModCarryStepCarry p2 carry))))) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p7
           (mulModCarryStepCarry p6
             (mulModCarryStepCarry p5
               (mulModCarryStepCarry p4
                 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 carry))))))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_112_120_128_136_144_152_spec_within
      sp (base + 148) carry v9 p2 p3 p4 p5 p6 p7)
    (hmono := evm_mulmod_program_code_product_first_carry_sub base)

/-- Second product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_second_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 296) ((base + 296) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 296)
      (3952 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_second_finish_sub base)

/-- Second product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_second_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p3 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 20 (base + 304) ((base + 304) + 80) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5
              (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 carry))))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5
              (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 carry))))) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ mulModCarryStepValue p3 carry) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p4 (mulModCarryStepCarry p3 carry)) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 carry))) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p6
           (mulModCarryStepCarry p5 (mulModCarryStepCarry p4
             (mulModCarryStepCarry p3 carry)))) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p7
           (mulModCarryStepCarry p6
             (mulModCarryStepCarry p5
               (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 carry)))))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_120_128_136_144_152_spec_within
      sp (base + 304) carry v9 p3 p4 p5 p6 p7)
    (hmono := evm_mulmod_program_code_product_second_carry_sub base)

/-- Third product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_third_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 436) ((base + 436) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 436)
      (3952 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_third_finish_sub base)

/-- Third product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_third_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p3 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 20 (base + 444) ((base + 444) + 80) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5
              (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 carry))))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5
              (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 carry))))) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ mulModCarryStepValue p3 carry) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p4 (mulModCarryStepCarry p3 carry)) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 carry))) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p6
           (mulModCarryStepCarry p5 (mulModCarryStepCarry p4
             (mulModCarryStepCarry p3 carry)))) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p7
           (mulModCarryStepCarry p6
             (mulModCarryStepCarry p5
               (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 carry)))))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_120_128_136_144_152_spec_within
      sp (base + 444) carry v9 p3 p4 p5 p6 p7)
    (hmono := evm_mulmod_program_code_product_third_carry_sub base)

/-- Fourth product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_fourth_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 576) ((base + 576) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 576)
      (3960 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_fourth_finish_sub base)

/-- Fourth product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_fourth_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 16 (base + 584) ((base + 584) + 64) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5
            (mulModCarryStepCarry p4 carry)))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5
            (mulModCarryStepCarry p4 carry)))) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ mulModCarryStepValue p4 carry) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p5 (mulModCarryStepCarry p4 carry)) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 carry))) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p7
           (mulModCarryStepCarry p6 (mulModCarryStepCarry p5
             (mulModCarryStepCarry p4 carry))))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_128_136_144_152_spec_within
      sp (base + 584) carry v9 p4 p5 p6 p7)
    (hmono := evm_mulmod_program_code_product_fourth_carry_sub base)

/-- Fifth product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_fifth_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 700) ((base + 700) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 700)
      (3960 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_fifth_finish_sub base)

/-- Fifth product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_fifth_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 16 (base + 708) ((base + 708) + 64) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5
            (mulModCarryStepCarry p4 carry)))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5
            (mulModCarryStepCarry p4 carry)))) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ mulModCarryStepValue p4 carry) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p5 (mulModCarryStepCarry p4 carry)) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 carry))) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p7
           (mulModCarryStepCarry p6 (mulModCarryStepCarry p5
             (mulModCarryStepCarry p4 carry))))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_128_136_144_152_spec_within
      sp (base + 708) carry v9 p4 p5 p6 p7)
    (hmono := evm_mulmod_program_code_product_fifth_carry_sub base)

/-- Sixth product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_sixth_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 824) ((base + 824) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 824)
      (3960 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_sixth_finish_sub base)

/-- Sixth product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_sixth_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 16 (base + 832) ((base + 832) + 64) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5
            (mulModCarryStepCarry p4 carry)))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5
            (mulModCarryStepCarry p4 carry)))) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ mulModCarryStepValue p4 carry) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p5 (mulModCarryStepCarry p4 carry)) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 carry))) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p7
           (mulModCarryStepCarry p6 (mulModCarryStepCarry p5
             (mulModCarryStepCarry p4 carry))))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_128_136_144_152_spec_within
      sp (base + 832) carry v9 p4 p5 p6 p7)
    (hmono := evm_mulmod_program_code_product_sixth_carry_sub base)

/-- Seventh product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_seventh_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 948) ((base + 948) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 948)
      (3968 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_seventh_finish_sub base)

/-- Seventh product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_seventh_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p5 p6 p7 : Word) :
    cpsTripleWithin 12 (base + 956) ((base + 956) + 48) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 carry))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 carry))) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ mulModCarryStepValue p5 carry) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p6 (mulModCarryStepCarry p5 carry)) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p7
           (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 carry)))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_136_144_152_spec_within
      sp (base + 956) carry v9 p5 p6 p7)
    (hmono := evm_mulmod_program_code_product_seventh_carry_sub base)

/-- Eighth product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_eighth_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 1056) ((base + 1056) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 1056)
      (3968 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_eighth_finish_sub base)

/-- Eighth product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_eighth_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p5 p6 p7 : Word) :
    cpsTripleWithin 12 (base + 1064) ((base + 1064) + 48) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 carry))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 carry))) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ mulModCarryStepValue p5 carry) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p6 (mulModCarryStepCarry p5 carry)) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p7
           (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 carry)))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_136_144_152_spec_within
      sp (base + 1064) carry v9 p5 p6 p7)
    (hmono := evm_mulmod_program_code_product_eighth_carry_sub base)

/-- Ninth product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_ninth_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 1164) ((base + 1164) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 1164)
      (3968 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_ninth_finish_sub base)

/-- Ninth product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_ninth_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p5 p6 p7 : Word) :
    cpsTripleWithin 12 (base + 1172) ((base + 1172) + 48) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 carry))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 carry))) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ mulModCarryStepValue p5 carry) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p6 (mulModCarryStepCarry p5 carry)) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p7
           (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 carry)))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_136_144_152_spec_within
      sp (base + 1172) carry v9 p5 p6 p7)
    (hmono := evm_mulmod_program_code_product_ninth_carry_sub base)

/-- First product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_first_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 140) ((base + 140) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 140)
      (3944 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_first_finish_sub base)

end EvmAsm.Evm64.MulMod.Compose
