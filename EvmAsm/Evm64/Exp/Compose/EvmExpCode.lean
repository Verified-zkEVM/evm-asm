/-
  EvmAsm.Evm64.Exp.Compose.EvmExpCode

  Top-level `CodeReq` decomposition for the EXP opcode program:
  `evmExpCode` (`unionAll` of prologue, pointer-advance, iter-body-full,
  pointer-restore, epilogue) plus its `_eq_ofProg` equality with
  `CodeReq.ofProg ... (evm_exp ...)` and the four `evmExpCode_*_sub`
  block-subsumption lemmas used by downstream top-code specs.

  Split out from `Compose/Base.lean` to respect the 1200-line cap on
  Compose files (#92 chore evm-asm-0z4dv).
-/

module

public import EvmAsm.Evm64.Exp.Compose.Base

@[expose] public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64 (CodeReq Program seq)

/-- Top-level CodeReq decomposition for the EXP opcode program. -/
abbrev evmExpCode (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_prologue,
    CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_loop_pointer_advance,
    expIterBodyFullCode (base + 28) mulOff skipOff backOff,
    CodeReq.ofProg (base + 260) EvmAsm.Evm64.exp_loop_pointer_restore,
    CodeReq.ofProg (base + 264) EvmAsm.Evm64.exp_epilogue
  ]

theorem evmExpCode_eq_ofProg (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    evmExpCode base mulOff skipOff backOff =
      CodeReq.ofProg base (EvmAsm.Evm64.evm_exp mulOff skipOff backOff) := by
  unfold evmExpCode
  unfold EvmAsm.Evm64.evm_exp
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
  have h260 :
      (base + 28 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_iter_body_full mulOff skipOff backOff).length) =
        base + 260 := by
    rw [EvmAsm.Evm64.exp_iter_body_full_length]
    bv_addr
  rw [h260]
  rw [CodeReq.ofProg_append]
  have h264 :
      (base + 260 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_loop_pointer_restore).length) = base + 264 := by
    rw [EvmAsm.Evm64.exp_loop_pointer_restore_length]
    bv_addr
  rw [h264]
  rw [← expIterBodyFullCode_eq_ofProg (base + 28) mulOff skipOff backOff]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

theorem evmExpCode_prologue_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  unfold evmExpCode
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem evmExpCode_pointer_advance_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  rw [evmExpCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 24)
    (EvmAsm.Evm64.evm_exp mulOff skipOff backOff)
    EvmAsm.Evm64.exp_loop_pointer_advance 6
    (EvmAsm.Evm64.Exp.AddrNorm.expTopPointerAdvanceProgramAddr base)
    (by
      unfold EvmAsm.Evm64.evm_exp
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_len, exp_loop_pointer_advance_len]
      omega)
    (by
      simp only [evm_exp_len]
      norm_num)

theorem evmExpCode_iter_body_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (expIterBodyFullCode (base + 28) mulOff skipOff backOff) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  rw [evmExpCode_eq_ofProg, expIterBodyFullCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 28)
    (EvmAsm.Evm64.evm_exp mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_iter_body_full mulOff skipOff backOff) 7
    (EvmAsm.Evm64.Exp.AddrNorm.expTopIterBodyProgramAddr base)
    (by
      unfold EvmAsm.Evm64.evm_exp
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_len, exp_iter_body_full_len]
      omega)
    (by
      simp only [evm_exp_len]
      norm_num)

theorem evmExpCode_pointer_restore_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 260)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  rw [evmExpCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 260)
    (EvmAsm.Evm64.evm_exp mulOff skipOff backOff)
    EvmAsm.Evm64.exp_loop_pointer_restore 65
    (EvmAsm.Evm64.Exp.AddrNorm.expTopPointerRestoreProgramAddr base)
    (by
      unfold EvmAsm.Evm64.evm_exp
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_len, exp_loop_pointer_restore_len]
      omega)
    (by
      simp only [evm_exp_len]
      norm_num)

end EvmAsm.Evm64.Exp.Compose
