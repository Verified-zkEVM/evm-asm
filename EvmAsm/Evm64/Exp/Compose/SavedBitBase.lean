/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBase

  Single-offset whole-code CodeReq composition infrastructure for the corrected
  saved-bit EXP layouts.  Iteration-level and two-MUL/canonical decompositions
  live in sibling modules.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulCode

public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64 (CodeReq Program seq)

/-- Top-level CodeReq decomposition for the corrected MSB-first saved-bit EXP
    opcode program. -/
abbrev evmExpMsbSavedBitCode (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_prologue,
    CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_loop_pointer_advance,
    expIterBodyFullMsbSavedBitCode (base + 28) mulOff skipOff backOff,
    CodeReq.ofProg (base + 264) EvmAsm.Evm64.exp_loop_pointer_restore,
    CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue
  ]

theorem evmExpMsbSavedBitCode_eq_ofProg (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    evmExpMsbSavedBitCode base mulOff skipOff backOff =
      CodeReq.ofProg base
        (EvmAsm.Evm64.evm_exp_msb_saved_bit mulOff skipOff backOff) := by
  unfold evmExpMsbSavedBitCode
  unfold EvmAsm.Evm64.evm_exp_msb_saved_bit
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
        (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
          mulOff skipOff backOff).length) = base + 264 := by
    rw [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_length]
    bv_addr
  rw [h264]
  rw [CodeReq.ofProg_append]
  have h268 :
      (base + 264 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_loop_pointer_restore).length) = base + 268 := by
    rw [EvmAsm.Evm64.exp_loop_pointer_restore_length]
    bv_addr
  rw [h268]
  rw [← expIterBodyFullMsbSavedBitCode_eq_ofProg
    (base + 28) mulOff skipOff backOff]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

theorem evmExpMsbSavedBitCode_prologue_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitCode
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitCode_pointer_advance_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 24)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit mulOff skipOff backOff)
    EvmAsm.Evm64.exp_loop_pointer_advance 6
    (EvmAsm.Evm64.Exp.AddrNorm.expTopPointerAdvanceProgramAddr base)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_len, exp_loop_pointer_advance_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_len]
      norm_num)

theorem evmExpMsbSavedBitCode_iter_body_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (expIterBodyFullMsbSavedBitCode (base + 28)
      mulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitCode_eq_ofProg,
    expIterBodyFullMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 28)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit mulOff skipOff backOff) 7
    (EvmAsm.Evm64.Exp.AddrNorm.expTopIterBodyProgramAddr base)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_len,
        exp_iter_body_full_msb_saved_bit_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_len]
      norm_num)

theorem evmExpMsbSavedBitCode_pointer_restore_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 264)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit mulOff skipOff backOff)
    EvmAsm.Evm64.exp_loop_pointer_restore 66
    (EvmAsm.Evm64.Exp.AddrNorm.expTopEpilogueProgramAddr base)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_len, exp_loop_pointer_restore_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_len]
      norm_num)

theorem evmExpMsbSavedBitCode_epilogue_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 268)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit mulOff skipOff backOff)
    EvmAsm.Evm64.exp_epilogue 67
    (EvmAsm.Evm64.Exp.AddrNorm.expSavedBitEpilogueProgramAddr base)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_len, exp_epilogue_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_len]
      norm_num)

theorem evmExpMsbSavedBitCode_block_subs {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (expIterBodyFullMsbSavedBitCode (base + 28)
      mulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i) := by
  exact ⟨evmExpMsbSavedBitCode_prologue_sub,
    evmExpMsbSavedBitCode_pointer_advance_sub,
    evmExpMsbSavedBitCode_iter_body_sub,
    evmExpMsbSavedBitCode_pointer_restore_sub,
    evmExpMsbSavedBitCode_epilogue_sub⟩

end EvmAsm.Evm64.Exp.Compose
