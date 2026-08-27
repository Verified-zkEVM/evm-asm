/-
  EvmAsm.Evm64.Exp.Compose.TopCodeSubs

  Top-level EXP code-bundle subsumption lemmas split out of `Compose/Base.lean`
  to keep the base module under the Compose file-size guardrail.
-/

module

public import EvmAsm.Evm64.Exp.Compose.Base
public import EvmAsm.Evm64.Exp.Compose.EvmExpCode

public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64 (CodeReq Program)

theorem evmExpCode_epilogue_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 264) EvmAsm.Evm64.exp_epilogue) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  rw [evmExpCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 264)
    (EvmAsm.Evm64.evm_exp mulOff skipOff backOff)
    EvmAsm.Evm64.exp_epilogue 66
    (EvmAsm.Evm64.Exp.AddrNorm.expTopEpilogueProgramAddr base)
    (by
      unfold EvmAsm.Evm64.evm_exp
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_len, exp_epilogue_len]
      omega)
    (by
      simp only [evm_exp_len]
      norm_num)

theorem evmExpCode_block_subs {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (expIterBodyFullCode (base + 28) mulOff skipOff backOff) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 260)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264) EvmAsm.Evm64.exp_epilogue) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i) := by
  exact ⟨evmExpCode_prologue_sub, evmExpCode_pointer_advance_sub,
    evmExpCode_iter_body_sub, evmExpCode_pointer_restore_sub,
    evmExpCode_epilogue_sub⟩

end EvmAsm.Evm64.Exp.Compose
