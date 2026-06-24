/-
  EvmAsm.Evm64.DivMod.Compose.V6FastArmConnect

  The connecting weakening for the v6 DIV fast arm (bead `evm-asm-vg1dc`).
  Both fast-body lanes (`divK_fastBody_{shiftNz,shift0}_spec_within_v6`) end in a
  postcondition that, once permuted into the *canonical raw* shape (clobbered
  registers as exact values, the four quotient result cells `sp+32..56` and the
  four dividend cells `sp+0..24` grouped, every scratch cell as a value, the call
  cells as `memOwn`, plus `x1`), weakens to `divStackDispatchPostV5 sp a b`.

  The proof folds the result cells into `evmWordIs (sp+32) (EvmWord.div a b)` via
  `fast_div_result_word_{shiftNz,shift0}` and the dividend cells into
  `evmWordIs sp a` via `fast_div_dividend_word`, then discharges the purely
  structural register/scratch weakening with `fast_post_weaken_core`.

  Stated over the *canonical raw* shape (not the literal body post): the
  body-post → canonical permutation is an AC `xperm` performed at the fast-arm
  triple use site (`evm-asm-35xs4`), where the body-post type is inferred.
-/

import EvmAsm.Evm64.DivMod.Compose.V6FastResultBridge
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div

namespace EvmAsm.Evm64

open EvmAsm.Rv64

variable (sp a0 a1 a2 a3 b0 b1 b2 b3 base : Word)
variable (x2v x11v qv0 qv1 qv2 qv3
          c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 x1v : Word)

/-- **shiftNz lane connecting weakening.** From the canonical raw fast-body
    postcondition shape — registers as exact values, the four result cells
    `sp+32..56` holding `v6chainQ{0,1,2,3}` of the shiftNz window, the four
    dividend cells `sp+0..24` holding `a[0..3]`, the 15 scratch value cells, the
    four call cells as `memOwn`, `x1`, and `memOwn (sp+3936)` — derive
    `divStackDispatchPostV5 sp a b` with `b = ⟨b0,b1,b2,b3⟩`, `a = ⟨a0,a1,a2,a3⟩`. -/
theorem fast_canonical_to_dispatchPostV5_shiftNz
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    ∀ h, ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x9 ** (.x2 ↦ᵣ x2v) **
          (.x5 ↦ᵣ qv0) ** (.x6 ↦ᵣ qv1) ** (.x7 ↦ᵣ qv2) ** (.x10 ↦ᵣ qv3) ** (.x11 ↦ᵣ x11v) **
          (.x0 ↦ᵣ (0 : Word)) **
          ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3)) **
          (((sp + 32) ↦ₘ v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0)) **
           ((sp + 40) ↦ₘ v6chainQ1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0)) **
           ((sp + 48) ↦ₘ v6chainQ2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0)) **
           ((sp + 56) ↦ₘ v6chainQ3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0))) **
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
        divStackDispatchPostV5 sp
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) h := by
  intro h hp
  rw [← fast_div_dividend_word sp a0 a1 a2 a3,
      ← fast_div_result_word_shiftNz sp a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz] at hp
  have hout := fast_post_weaken_core sp
    (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
    (EvmWord.div
      (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
      (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3))
    x2v x11v qv0 qv1 qv2 qv3 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 x1v h hp
  rw [divStackDispatchPostV5, divStackDispatchPost_unfold]
  xperm_hyp hout

/-- **shift=0 lane connecting weakening.** As `fast_canonical_to_dispatchPostV5_shiftNz`,
    for the already-normalized lane whose result cells hold `v6chainQ{0,1,2,3}` of
    the `(0, a3, a2, a1, a0)` window. -/
theorem fast_canonical_to_dispatchPostV5_shift0
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    ∀ h, ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x9 ** (.x2 ↦ᵣ x2v) **
          (.x5 ↦ᵣ qv0) ** (.x6 ↦ᵣ qv1) ** (.x7 ↦ᵣ qv2) ** (.x10 ↦ᵣ qv3) ** (.x11 ↦ᵣ x11v) **
          (.x0 ↦ᵣ (0 : Word)) **
          ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3)) **
          (((sp + 32) ↦ₘ v6chainQ0 (0 : Word) a3 a2 a1 a0 (v6nD b0)) **
           ((sp + 40) ↦ₘ v6chainQ1 (0 : Word) a3 a2 a1 (v6nD b0)) **
           ((sp + 48) ↦ₘ v6chainQ2 (0 : Word) a3 a2 (v6nD b0)) **
           ((sp + 56) ↦ₘ v6chainQ3 (0 : Word) a3 (v6nD b0))) **
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
        divStackDispatchPostV5 sp
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) h := by
  intro h hp
  rw [← fast_div_dividend_word sp a0 a1 a2 a3,
      ← fast_div_result_word_shift0 sp a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz] at hp
  have hout := fast_post_weaken_core sp
    (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
    (EvmWord.div
      (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
      (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3))
    x2v x11v qv0 qv1 qv2 qv3 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 x1v h hp
  rw [divStackDispatchPostV5, divStackDispatchPost_unfold]
  xperm_hyp hout

end EvmAsm.Evm64
