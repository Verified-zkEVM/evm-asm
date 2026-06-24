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
import EvmAsm.Evm64.DivMod.Compose.NormAV6

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

/-- CLZ ;; fastSetup ;; normA, shift≠0 lane: `v6ClzOff` → `v6Digit3Off` (52
    steps). Normalizes the divisor (`b0' = b0 << s`) and the 4-limb dividend
    `a[0..3]` (at `sp+0..24`) into the digit window `u[0..4]` (at `4024..4056`),
    ready for the digit chain. The divisor `b0` (CLZ input + `sp+32`), the
    dividend `a[0..3]`, and the (garbage) `u`-window are all in the precondition;
    `x10`/`x0`/scratch thread through. -/
theorem divK_clzSetupNormA_shiftNz_spec_within_v6
    (sp b0 a0 a1 a2 a3 v6Old v7Old v2Old v10 m3992 m3984 : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word)
    (hs_ne_0 : (clzResult b0).1 ≠ (0 : Word)) :
    cpsTripleWithin 52 (base + v6ClzOff) (base + v6Digit3Off) (divCodeV6 base)
      ((((.x5 ↦ᵣ b0) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
         ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984))) **
       ((.x10 ↦ᵣ v10) ** ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4024) ↦ₘ u4Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
        ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
        ((sp + signExtend12 4056) ↦ₘ u0Old)))
      ((normAFullPost sp a0 a1 a2 a3 ((clzResult b0).1) ((0 : Word) - (clzResult b0).1)) **
       ((.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 32) ↦ₘ b0) **
        ((sp + signExtend12 3992) ↦ₘ ((clzResult b0).1)) **
        ((sp + signExtend12 3984) ↦ₘ (b0 <<< (((clzResult b0).1).toNat % 64))))) := by
  have hcs := divK_clzSetup_shiftNz_spec_within_v6 sp b0 v6Old v7Old v2Old m3992 m3984 base hs_ne_0
  have hcsf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ v10) ** ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4056) ↦ₘ u0Old))
    (by pcFree) hcs
  have hnorma := divK_normA_full_spec_within_v6 sp a0 a1 a2 a3
    (b0 <<< (((clzResult b0).1).toNat % 64)) ((clzResult b0).2 >>> (63 : Nat)) v10
    ((clzResult b0).1) ((0 : Word) - (clzResult b0).1)
    u0Old u1Old u2Old u3Old u4Old base
  have hnormaf := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 32) ↦ₘ b0) **
     ((sp + signExtend12 3992) ↦ₘ ((clzResult b0).1)) **
     ((sp + signExtend12 3984) ↦ₘ (b0 <<< (((clzResult b0).1).toNat % 64))))
    (by pcFree) hnorma
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [divKFastSetupPost_unfold] at hp; xperm_hyp hp) hcsf hnormaf

/-- CLZ ;; fastSetup ;; copyAU, shift=0 lane: `v6ClzOff` → `v6Digit3Off` (40
    steps). When the divisor is already normalized (`s = 0`), the dividend needs
    no shifting: copyAU places `a[0..3]` directly into `u[0..3]` (at
    `4056/4048/4040/4032`) and zeroes `u[4]` (at `4024`). -/
theorem divK_clzSetupCopyAU_shift0_spec_within_v6
    (sp b0 a0 a1 a2 a3 v6Old v7Old v2Old m3992 m3984 : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word)
    (hs_eq_0 : (clzResult b0).1 = (0 : Word)) :
    cpsTripleWithin 40 (base + v6ClzOff) (base + v6Digit3Off) (divCodeV6 base)
      ((((.x5 ↦ᵣ b0) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
         ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984))) **
       (((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
        ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
        ((sp + signExtend12 4024) ↦ₘ u4Old)))
      ((((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ a3) **
         ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
         ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
         ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
         ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
         ((sp + signExtend12 4024) ↦ₘ (0 : Word)))) **
       ((.x6 ↦ᵣ ((clzResult b0).1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ ((0 : Word) - (clzResult b0).1)) ** ((sp + signExtend12 32) ↦ₘ b0) **
        ((sp + signExtend12 3992) ↦ₘ ((clzResult b0).1)) **
        ((sp + signExtend12 3984) ↦ₘ (b0 <<< (((clzResult b0).1).toNat % 64))) **
        (.x7 ↦ᵣ ((clzResult b0).2 >>> (63 : Nat))))) := by
  have hcs := divK_clzSetup_shift0_spec_within_v6 sp b0 v6Old v7Old v2Old m3992 m3984 base hs_eq_0
  have hcsf := cpsTripleWithin_frameR
    (((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4024) ↦ₘ u4Old))
    (by pcFree) hcs
  have hcopy := divK_copyAU_full_spec_within_v6 sp a0 a1 a2 a3
    u0Old u1Old u2Old u3Old u4Old (b0 <<< (((clzResult b0).1).toNat % 64)) base
  have hcopyf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ ((clzResult b0).1)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x2 ↦ᵣ ((0 : Word) - (clzResult b0).1)) ** ((sp + signExtend12 32) ↦ₘ b0) **
     ((sp + signExtend12 3992) ↦ₘ ((clzResult b0).1)) **
     ((sp + signExtend12 3984) ↦ₘ (b0 <<< (((clzResult b0).1).toNat % 64))) **
     (.x7 ↦ᵣ ((clzResult b0).2 >>> (63 : Nat))))
    (by pcFree) hcopy
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [divKFastSetupPost_unfold] at hp; xperm_hyp hp) hcsf hcopyf

-- ============================================================================
-- Normalized dividend limbs (the `normAFullPost` let-values for shift `s`,
-- antiShift `-s`, where `s = (clzResult b0).1`). Kept as abbreviations so the
-- digit-chain splice stays readable; unfolded at the seq boundary.
-- ============================================================================

abbrev v6nU4 (a3 b0 : Word) : Word := a3 >>> (((0 : Word) - (clzResult b0).1).toNat % 64)
abbrev v6nU3 (a3 a2 b0 : Word) : Word :=
  (a3 <<< (((clzResult b0).1).toNat % 64)) ||| (a2 >>> (((0 : Word) - (clzResult b0).1).toNat % 64))
abbrev v6nU2 (a2 a1 b0 : Word) : Word :=
  (a2 <<< (((clzResult b0).1).toNat % 64)) ||| (a1 >>> (((0 : Word) - (clzResult b0).1).toNat % 64))
abbrev v6nU1 (a1 a0 b0 : Word) : Word :=
  (a1 <<< (((clzResult b0).1).toNat % 64)) ||| (a0 >>> (((0 : Word) - (clzResult b0).1).toNat % 64))
abbrev v6nU0 (a0 b0 : Word) : Word := a0 <<< (((clzResult b0).1).toNat % 64)
abbrev v6nD (b0 : Word) : Word := b0 <<< (((clzResult b0).1).toNat % 64)
abbrev v6nX10 (a0 b0 : Word) : Word := a0 >>> (((0 : Word) - (clzResult b0).1).toNat % 64)

/-- CLZ ;; fastSetup ;; normA ;; digitChain, shift≠0 lane: `v6ClzOff` →
    `v6EpilogueOff` (424 steps). Normalizes the divisor + dividend, then runs the
    four single-limb division digits, leaving the quotient digits `q[3..0]` at
    `4064/4072/4080/4088` and the final remainder at `4056`. -/
theorem divK_clzSetupNormADigits_shiftNz_spec_within_v6
    (sp b0 a0 a1 a2 a3 v6Old v7Old v2Old v10 v9d v11d : Word)
    (qm3 qm2 qm1 qm0 m3992 m3984 retMem dMem dloMem un0Mem scratchMem m40 m48 m56 : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word)
    (hs_ne_0 : (clzResult b0).1 ≠ (0 : Word))
    (halign3 : ((base + v6Digit3Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit3Off + 16)
    (halign2 : ((base + v6Digit2Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit2Off + 16)
    (halign1 : ((base + v6Digit1Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit1Off + 16)
    (halign0 : ((base + v6Digit0Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit0Off + 16) :
    cpsTripleWithin 424 (base + v6ClzOff) (base + v6EpilogueOff) (divCodeV6 base)
      (((((.x5 ↦ᵣ b0) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word))) **
         ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
          ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984))) **
        ((.x10 ↦ᵣ v10) ** ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
         ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
         ((sp + signExtend12 4024) ↦ₘ u4Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
         ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
         ((sp + signExtend12 4056) ↦ₘ u0Old))) **
       ((.x9 ↦ᵣ v9d) ** (.x11 ↦ᵣ v11d) **
        (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        ((sp + signExtend12 4064) ↦ₘ qm3) ** ((sp + signExtend12 4072) ↦ₘ qm2) **
        ((sp + signExtend12 4080) ↦ₘ qm1) ** ((sp + signExtend12 4088) ↦ₘ qm0) **
        ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56)))
      ((((((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ (v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))) **
          (.x5 ↦ᵣ (v6chainR0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))) ** (.x10 ↦ᵣ (v6nD b0)) **
          (.x7 ↦ᵣ (v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0) * (v6nD b0))) **
          ((sp + signExtend12 4088) ↦ₘ (v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))) **
          ((sp + signExtend12 4056) ↦ₘ (v6chainR0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))) **
          ((sp + signExtend12 3984) ↦ₘ (v6nD b0))) **
         ((.x2 ↦ᵣ (base + v6Digit0Off + 16)) ** regOwn .x6 ** regOwn .x9 ** (.x0 ↦ᵣ (0 : Word)) **
          memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
          memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
          memOwn (sp + signExtend12 3936) **
          ((sp + signExtend12 4048) ↦ₘ (v6chainR1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0))))) **
        (((sp + signExtend12 4064) ↦ₘ (v6chainQ3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0))) ** ((sp + signExtend12 4024) ↦ₘ (v6nU4 a3 b0)) **
         ((sp + signExtend12 4072) ↦ₘ (v6chainQ2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0))) **
         ((sp + signExtend12 4032) ↦ₘ (v6chainR3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0))) **
         ((sp + signExtend12 4080) ↦ₘ (v6chainQ1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0))) **
         ((sp + signExtend12 4040) ↦ₘ (v6chainR2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0)))))) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 32) ↦ₘ b0) ** ((sp + signExtend12 3992) ↦ₘ ((clzResult b0).1)) **
        ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56))) := by
  have hcsn := divK_clzSetupNormA_shiftNz_spec_within_v6 sp b0 a0 a1 a2 a3 v6Old v7Old v2Old v10
    m3992 m3984 u0Old u1Old u2Old u3Old u4Old base hs_ne_0
  have hcsnf := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ v9d) ** (.x11 ↦ᵣ v11d) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
     (sp + signExtend12 3936 ↦ₘ scratchMem) **
     ((sp + signExtend12 4064) ↦ₘ qm3) ** ((sp + signExtend12 4072) ↦ₘ qm2) **
     ((sp + signExtend12 4080) ↦ₘ qm1) ** ((sp + signExtend12 4088) ↦ₘ qm0) **
     ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56))
    (by pcFree) hcsn
  have hdc := divK_digitChain_spec_within_v6 sp (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0)
    (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0) base
    ((0 : Word) - (clzResult b0).1) (v6nU1 a1 a0 b0) ((clzResult b0).1) (v6nU0 a0 b0) v9d
    (v6nX10 a0 b0) v11d qm3 qm2 qm1 qm0 retMem dMem dloMem un0Mem scratchMem
    halign3 halign2 halign1 halign0
  have hdcf := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 32) ↦ₘ b0) ** ((sp + signExtend12 3992) ↦ₘ ((clzResult b0).1)) **
     ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56))
    (by pcFree) hdc
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [normAFullPost_unfold] at hp
      simp only [v6nU4, v6nU3, v6nU2, v6nU1, v6nU0, v6nD, v6nX10]
      xperm_hyp hp) hcsnf hdcf

end EvmAsm.Evm64
