/-
  EvmAsm.Evm64.DivMod.Compose.V6FastResultBridge

  Reconcile the v6 fast-path body's stored quotient limbs (`v6chainQ_j` at the
  result slots `sp+32 / +40 / +48 / +56`) with the `evmWordIs (sp+32)
  (EvmWord.div a b)` component of `divStackDispatchPost`.  This is the result
  half of the `dr466.3` postcondition weakening: it lets both fast-body lanes'
  postconditions be folded into the same dispatch post the reused v5 arm
  produces, so all arms converge under `cpsBranchWithin_merge_same_cr`.

  Proved per-cell via `congrArg` over the `getLimbN` bridges (the
  `EvmWord.div … (fromLimbs …)` term carries a `match`-motive that blocks a
  direct `rw`/`simp` rewrite, so each limb cell is rewritten individually).
  Bead `evm-asm-dr466.3`.
-/

import EvmAsm.Evm64.DivMod.Compose.V6BodyModelBridge
import EvmAsm.Evm64.DivMod.Compose.V6Shift0ChainBridge
import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

variable (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word)

/-- **shiftNz lane result reconciliation.** The four quotient limbs the fast
    body stores at `sp+32 / +40 / +48 / +56` form `evmWordIs (sp+32)
    (EvmWord.div a b)`. -/
theorem fast_div_result_word_shiftNz
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    evmWordIs (sp + 32)
        (EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3))
    = (((sp + 32) ↦ₘ v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0)) **
       ((sp + 40) ↦ₘ v6chainQ1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0)) **
       ((sp + 48) ↦ₘ v6chainQ2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0)) **
       ((sp + 56) ↦ₘ v6chainQ3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0))) := by
  rw [evmWordIs_sp32_unfold]
  congr 1
  · exact congrArg (fun w => (sp + 32) ↦ₘ w)
      (v6n_div_getLimbN_0 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  congr 1
  · exact congrArg (fun w => (sp + 40) ↦ₘ w)
      (v6n_div_getLimbN_1 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  congr 1
  · exact congrArg (fun w => (sp + 48) ↦ₘ w)
      (v6n_div_getLimbN_2 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  · exact congrArg (fun w => (sp + 56) ↦ₘ w)
      (v6n_div_getLimbN_3 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)

/-- **shift=0 lane result reconciliation.** As above, for the already-normalized
    lane whose window is `(0, a3, a2, a1, a0)` with `d = v6nD b0`. -/
theorem fast_div_result_word_shift0
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    evmWordIs (sp + 32)
        (EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3))
    = (((sp + 32) ↦ₘ v6chainQ0 0 a3 a2 a1 a0 (v6nD b0)) **
       ((sp + 40) ↦ₘ v6chainQ1 0 a3 a2 a1 (v6nD b0)) **
       ((sp + 48) ↦ₘ v6chainQ2 0 a3 a2 (v6nD b0)) **
       ((sp + 56) ↦ₘ v6chainQ3 0 a3 (v6nD b0))) := by
  rw [evmWordIs_sp32_unfold]
  congr 1
  · exact congrArg (fun w => (sp + 32) ↦ₘ w)
      (v6n_div_getLimbN_shift0_0 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz)
  congr 1
  · exact congrArg (fun w => (sp + 40) ↦ₘ w)
      (v6n_div_getLimbN_shift0_1 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz)
  congr 1
  · exact congrArg (fun w => (sp + 48) ↦ₘ w)
      (v6n_div_getLimbN_shift0_2 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz)
  · exact congrArg (fun w => (sp + 56) ↦ₘ w)
      (v6n_div_getLimbN_shift0_3 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz)

end EvmAsm.Evm64
