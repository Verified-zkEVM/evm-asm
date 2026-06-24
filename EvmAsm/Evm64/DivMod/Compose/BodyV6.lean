/-
  EvmAsm.Evm64.DivMod.Compose.BodyV6

  Body-prefix compositions for the v6 fast-path: CLZ ;; fastSetup, for both the
  shift≠0 lane (→ normA) and the shift=0 lane (→ copyAU). These are the first
  two of the five bricks of the full DIV fast-path body (bead `evm-asm-7wbf8.4`).

  CLZ computes the normalization shift `s = (clzResult b0).1` of the divisor
  limb `b0` (held in `x5` from the dispatch); fastSetup then stores `s`, computes
  `antiShift = -s`, and the normalized divisor `b0' = b0 <<< s`.

  Bead `evm-asm-7wbf8.4.1`.
-/

import EvmAsm.Evm64.DivMod.Compose.DigitChainV6
import EvmAsm.Evm64.DivMod.Compose.FastSetupV6

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CLZ ;; fastSetup, shift≠0 lane: `v6ClzOff` → `v6NormAOff` (31 steps). The
    divisor `b0` is in `x5` (CLZ input) and at `sp+32` (fastSetup input). -/
theorem divK_clzSetup_shiftNz_spec_within_v6
    (sp b0 v6Old v7Old v2Old m3992 m3984 : Word) (base : Word)
    (hs_ne_0 : (clzResult b0).1 ≠ (0 : Word)) :
    cpsTripleWithin 31 (base + v6ClzOff) (base + v6NormAOff) (divCodeV6 base)
      (((.x5 ↦ᵣ b0) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
        ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984)))
      ((divKFastSetupPost sp ((clzResult b0).1) b0 ((0 : Word) - (clzResult b0).1)
          (b0 <<< (((clzResult b0).1).toNat % 64))) **
       (.x7 ↦ᵣ ((clzResult b0).2 >>> (63 : Nat)))) := by
  have hclz := divK_clz_spec_within_v6 b0 v6Old v7Old base
  have hclzf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
     ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984))
    (by pcFree) hclz
  have hsetup := divK_fastSetup_shiftNz_spec_within_v6 sp ((clzResult b0).2)
    ((clzResult b0).1) b0 v2Old m3992 m3984 base hs_ne_0
  have hsetupf := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ ((clzResult b0).2 >>> (63 : Nat)))) (by pcFree) hsetup
  exact cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hclzf hsetupf

/-- CLZ ;; fastSetup, shift=0 lane: `v6ClzOff` → `v6CopyAUOff` (31 steps). -/
theorem divK_clzSetup_shift0_spec_within_v6
    (sp b0 v6Old v7Old v2Old m3992 m3984 : Word) (base : Word)
    (hs_eq_0 : (clzResult b0).1 = (0 : Word)) :
    cpsTripleWithin 31 (base + v6ClzOff) (base + v6CopyAUOff) (divCodeV6 base)
      (((.x5 ↦ᵣ b0) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
        ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984)))
      ((divKFastSetupPost sp ((clzResult b0).1) b0 ((0 : Word) - (clzResult b0).1)
          (b0 <<< (((clzResult b0).1).toNat % 64))) **
       (.x7 ↦ᵣ ((clzResult b0).2 >>> (63 : Nat)))) := by
  have hclz := divK_clz_spec_within_v6 b0 v6Old v7Old base
  have hclzf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
     ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984))
    (by pcFree) hclz
  have hsetup := divK_fastSetup_shift0_spec_within_v6 sp ((clzResult b0).2)
    ((clzResult b0).1) b0 v2Old m3992 m3984 base hs_eq_0
  have hsetupf := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ ((clzResult b0).2 >>> (63 : Nat)))) (by pcFree) hsetup
  exact cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hclzf hsetupf

end EvmAsm.Evm64
