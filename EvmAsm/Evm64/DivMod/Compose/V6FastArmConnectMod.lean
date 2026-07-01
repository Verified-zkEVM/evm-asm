/-
  EvmAsm.Evm64.DivMod.Compose.V6FastArmConnectMod

  Connecting weakening for the v6 MOD fast arm.  From the canonical raw fast-body
  postcondition (clobbered registers as exact values, the four result cells
  `sp+32..56` holding the denormalized single-limb remainder `v6chainR0 >>> s` and
  three zeros, the dividend cells `sp+0..24`, the scratch value cells, the call
  cells as `memOwn`, `x1`, and `memOwn (sp+3936)`), derive `modStackDispatchPostV5
  sp a b`.

  Mirror of `Compose/V6FastArmConnect.lean` (DIV), folding the remainder cells into
  `evmWordIs (sp+32) (EvmWord.mod a b)` via `fast_mod_result_word_{shiftNz,shift0}`
  where DIV folds the quotient; the dividend fold (`fast_div_dividend_word`) and the
  structural register/scratch weakening (`fast_post_weaken_core`) are op-agnostic
  and reused verbatim.  Brick 5 of the MOD v6 fast arm.
-/

import EvmAsm.Evm64.DivMod.Compose.V6FastResultBridgeMod
import EvmAsm.Evm64.DivMod.Compose.V6FastResultBridge
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

variable (sp a0 a1 a2 a3 b0 b1 b2 b3 base : Word)
variable (x2v x11v qv0 qv1 qv2 qv3
          c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 x1v : Word)

/-- **shift≠0 MOD lane connecting weakening.** -/
theorem fast_canonical_to_modDispatchPostV5_shiftNz
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    ∀ h, ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x9 ** (.x2 ↦ᵣ x2v) **
          (.x5 ↦ᵣ qv0) ** (.x6 ↦ᵣ qv1) ** (.x7 ↦ᵣ qv2) ** (.x10 ↦ᵣ qv3) ** (.x11 ↦ᵣ x11v) **
          (.x0 ↦ᵣ (0 : Word)) **
          ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3)) **
          (((sp + 32) ↦ₘ (v6chainR0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0)
                                    (v6nU0 a0 b0) (v6nD b0)) >>> ((clzResult b0).1.toNat % 64)) **
           ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) **
          ((((sp + signExtend12 4088) ↦ₘ c0) ** ((sp + signExtend12 4080) ↦ₘ c1) **
            ((sp + signExtend12 4072) ↦ₘ c2) ** ((sp + signExtend12 4064) ↦ₘ c3) **
            ((sp + signExtend12 4056) ↦ₘ c4) ** ((sp + signExtend12 4048) ↦ₘ c5) **
            ((sp + signExtend12 4040) ↦ₘ c6) ** ((sp + signExtend12 4032) ↦ₘ c7) **
            ((sp + signExtend12 4024) ↦ₘ c8) ** ((sp + signExtend12 4016) ↦ₘ c9) **
            ((sp + signExtend12 4008) ↦ₘ c10) ** ((sp + signExtend12 4000) ↦ₘ c11) **
            ((sp + signExtend12 3992) ↦ₘ c12) ** ((sp + signExtend12 3984) ↦ₘ c13) **
            ((sp + signExtend12 3976) ↦ₘ c14)) **
            (memOwn (sp + signExtend12 3968)) ** (memOwn (sp + signExtend12 3960)) **
            (memOwn (sp + signExtend12 3952)) ** (memOwn (sp + signExtend12 3944)) **
            ((.x1 : Reg) ↦ᵣ x1v)) **
          memOwn (sp + signExtend12 3936)) h →
        modStackDispatchPostV5 sp
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) h := by
  intro h hp
  rw [← fast_div_dividend_word sp a0 a1 a2 a3,
      ← fast_mod_result_word_shiftNz sp a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz] at hp
  have hout := fast_post_weaken_core sp
    (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
    (EvmWord.mod
      (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
      (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3))
    x2v x11v qv0 qv1 qv2 qv3 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 x1v h hp
  rw [modStackDispatchPostV5, modStackDispatchPost_unfold]
  xperm_hyp hout

/-- **shift=0 MOD lane connecting weakening.** -/
theorem fast_canonical_to_modDispatchPostV5_shift0
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    ∀ h, ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x9 ** (.x2 ↦ᵣ x2v) **
          (.x5 ↦ᵣ qv0) ** (.x6 ↦ᵣ qv1) ** (.x7 ↦ᵣ qv2) ** (.x10 ↦ᵣ qv3) ** (.x11 ↦ᵣ x11v) **
          (.x0 ↦ᵣ (0 : Word)) **
          ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3)) **
          (((sp + 32) ↦ₘ (v6chainR0 (0 : Word) a3 a2 a1 a0 (v6nD b0)) >>> ((clzResult b0).1.toNat % 64)) **
           ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) **
          ((((sp + signExtend12 4088) ↦ₘ c0) ** ((sp + signExtend12 4080) ↦ₘ c1) **
            ((sp + signExtend12 4072) ↦ₘ c2) ** ((sp + signExtend12 4064) ↦ₘ c3) **
            ((sp + signExtend12 4056) ↦ₘ c4) ** ((sp + signExtend12 4048) ↦ₘ c5) **
            ((sp + signExtend12 4040) ↦ₘ c6) ** ((sp + signExtend12 4032) ↦ₘ c7) **
            ((sp + signExtend12 4024) ↦ₘ c8) ** ((sp + signExtend12 4016) ↦ₘ c9) **
            ((sp + signExtend12 4008) ↦ₘ c10) ** ((sp + signExtend12 4000) ↦ₘ c11) **
            ((sp + signExtend12 3992) ↦ₘ c12) ** ((sp + signExtend12 3984) ↦ₘ c13) **
            ((sp + signExtend12 3976) ↦ₘ c14)) **
            (memOwn (sp + signExtend12 3968)) ** (memOwn (sp + signExtend12 3960)) **
            (memOwn (sp + signExtend12 3952)) ** (memOwn (sp + signExtend12 3944)) **
            ((.x1 : Reg) ↦ᵣ x1v)) **
          memOwn (sp + signExtend12 3936)) h →
        modStackDispatchPostV5 sp
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) h := by
  intro h hp
  rw [← fast_div_dividend_word sp a0 a1 a2 a3,
      ← fast_mod_result_word_shift0 sp a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz] at hp
  have hout := fast_post_weaken_core sp
    (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
    (EvmWord.mod
      (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
      (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3))
    x2v x11v qv0 qv1 qv2 qv3 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 x1v h hp
  rw [modStackDispatchPostV5, modStackDispatchPost_unfold]
  xperm_hyp hout

end EvmAsm.Evm64
