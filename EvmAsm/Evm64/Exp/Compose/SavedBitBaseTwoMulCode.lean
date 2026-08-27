/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulCode

  Whole-code two-MUL and canonical saved-bit EXP CodeReq decomposition.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulIter

public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Top-level CodeReq decomposition for the corrected saved-bit EXP opcode
    with independent MUL-call offsets at the two JAL sites. -/
abbrev evmExpMsbSavedBitTwoMulCode (base : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_prologue,
    CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_loop_pointer_advance,
    expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff skipOff backOff,
    CodeReq.ofProg (base + 264) EvmAsm.Evm64.exp_loop_pointer_restore,
    CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue
  ]

theorem evmExpMsbSavedBitTwoMulCode_eq_ofProg (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff =
      CodeReq.ofProg base
        (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
          squaringMulOff condMulOff skipOff backOff) := by
  unfold evmExpMsbSavedBitTwoMulCode
  unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
  simp only [EvmAsm.Rv64.seq]
  unfold Program
  rw [CodeReq.ofProg_append]
  have h24 :
      base + BitVec.ofNat 64 (4 * (EvmAsm.Evm64.exp_prologue).length) =
        base + 24 := by
    rw [EvmAsm.Evm64.exp_prologue_length]
    rfl
  rw [h24]
  rw [CodeReq.ofProg_append]
  have h28 :
      (base + 24 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_loop_pointer_advance).length) = base + 28 := by
    rw [EvmAsm.Evm64.exp_loop_pointer_advance_length]
    bv_addr
  rw [h28]
  rw [CodeReq.ofProg_append]
  have h264 :
      (base + 28 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
          squaringMulOff condMulOff skipOff backOff).length) = base + 264 := by
    rw [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_length]
    bv_addr
  rw [h264]
  rw [CodeReq.ofProg_append]
  have h268 :
      (base + 264 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_loop_pointer_restore).length) = base + 268 := by
    rw [EvmAsm.Evm64.exp_loop_pointer_restore_length]
    bv_addr
  rw [h268]
  rw [← expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg
    (base + 28) squaringMulOff condMulOff skipOff backOff]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

/-- CodeReq decomposition for the canonical two-MUL saved-bit EXP program.
    The branch offsets are fixed by `evm_exp_msb_saved_bit_two_mul_canonical`;
    the two external MUL call offsets remain caller supplied. -/
abbrev evmExpMsbSavedBitTwoMulCanonicalCode (base : Word)
    (squaringMulOff condMulOff : BitVec 21) : CodeReq :=
  evmExpMsbSavedBitTwoMulCode base squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff

theorem evmExpMsbSavedBitTwoMulCanonicalCode_eq_ofProg (base : Word)
    (squaringMulOff condMulOff : BitVec 21) :
    evmExpMsbSavedBitTwoMulCanonicalCode base squaringMulOff condMulOff =
      CodeReq.ofProg base
        (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_canonical
          squaringMulOff condMulOff) := by
  rw [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_canonical_eq]
  exact evmExpMsbSavedBitTwoMulCode_eq_ofProg base squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff

theorem evmExpMsbSavedBitTwoMulCode_iter_body_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitTwoMulCode_eq_ofProg,
    expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 28)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff) 7
    (EvmAsm.Evm64.Exp.AddrNorm.expTopIterBodyProgramAddr base)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len,
        exp_iter_body_full_msb_saved_bit_two_mul_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len]
      norm_num)

theorem evmExpMsbSavedBitTwoMulCode_prologue_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulCode
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitTwoMulCode_pointer_advance_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 24)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_loop_pointer_advance 6
    (EvmAsm.Evm64.Exp.AddrNorm.expTopPointerAdvanceProgramAddr base)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len, exp_loop_pointer_advance_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len]
      norm_num)

theorem evmExpMsbSavedBitTwoMulCode_pointer_restore_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 264)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_loop_pointer_restore 66
    (EvmAsm.Evm64.Exp.AddrNorm.expTopEpilogueProgramAddr base)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len, exp_loop_pointer_restore_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len]
      norm_num)

theorem evmExpMsbSavedBitTwoMulCode_epilogue_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 268)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_epilogue 67
    (EvmAsm.Evm64.Exp.AddrNorm.expSavedBitEpilogueProgramAddr base)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len, exp_epilogue_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len]
      norm_num)

theorem evmExpMsbSavedBitTwoMulCode_block_subs {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) := by
  exact ⟨evmExpMsbSavedBitTwoMulCode_prologue_sub,
    evmExpMsbSavedBitTwoMulCode_pointer_advance_sub,
    evmExpMsbSavedBitTwoMulCode_iter_body_sub,
    evmExpMsbSavedBitTwoMulCode_pointer_restore_sub,
    evmExpMsbSavedBitTwoMulCode_epilogue_sub⟩

theorem evmExpMsbSavedBitTwoMulCanonicalCode_iter_body_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} :
    ∀ a i, (expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i :=
  evmExpMsbSavedBitTwoMulCode_iter_body_sub

theorem evmExpMsbSavedBitTwoMulCanonicalCode_prologue_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i :=
  evmExpMsbSavedBitTwoMulCode_prologue_sub

theorem evmExpMsbSavedBitTwoMulCanonicalCode_pointer_advance_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i :=
  evmExpMsbSavedBitTwoMulCode_pointer_advance_sub

theorem evmExpMsbSavedBitTwoMulCanonicalCode_pointer_restore_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i :=
  evmExpMsbSavedBitTwoMulCode_pointer_restore_sub

theorem evmExpMsbSavedBitTwoMulCanonicalCode_epilogue_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i :=
  evmExpMsbSavedBitTwoMulCode_epilogue_sub

theorem evmExpMsbSavedBitTwoMulCanonicalCode_block_subs {base : Word}
    {squaringMulOff condMulOff : BitVec 21} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i) := by
  exact ⟨evmExpMsbSavedBitTwoMulCanonicalCode_prologue_sub,
    evmExpMsbSavedBitTwoMulCanonicalCode_pointer_advance_sub,
    evmExpMsbSavedBitTwoMulCanonicalCode_iter_body_sub,
    evmExpMsbSavedBitTwoMulCanonicalCode_pointer_restore_sub,
    evmExpMsbSavedBitTwoMulCanonicalCode_epilogue_sub⟩

end EvmAsm.Evm64.Exp.Compose
