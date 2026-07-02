/-
  EvmAsm.Evm64.DivMod.Compose.BodyV6Mod

  Body-prefix + full-body compositions for the v6 MOD fast path over `modCodeV6`.
  MOD mirror of `Compose/BodyV6.lean` (DIV over `divCodeV6`): the CLZ ;; fastSetup
  ;; normA/copyAU ;; digitChain windows are IDENTICAL code at IDENTICAL offsets
  (the mod-only `divK_fastDenorm` + `divK_mod_epilogue` blocks are inserted AFTER
  the digits), so these are verbatim mirrors using the `_v6_mod` leaf specs
  (`Compose/FastPrefixV6Mod.lean`) and the MOD digit chain
  (`divK_digitChain_spec_within_v6_mod`, `Compose/FastDigitChainV6Mod.lean`).
  Only the tail differs: instead of DIV's `divK_div_epilogue`, MOD composes the
  fast tail `modK_fastDenormEpilogue_spec_within_v6` (denormalize + store the
  single-limb remainder), landing `base+v6ClzOff → base+modV6ExitOff`.

  Brick 6 of the MOD v6 fast arm.
-/

import EvmAsm.Evm64.DivMod.Compose.FastDigitChainV6Mod
import EvmAsm.Evm64.DivMod.Compose.FastDenormEpilogueV6Mod
import EvmAsm.Evm64.DivMod.Compose.FastPrefixV6Mod
import EvmAsm.Evm64.DivMod.Compose.BodyV6

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CLZ ;; fastSetup, shift≠0 lane over `modCodeV6`: `v6ClzOff` → `v6NormAOff`. -/
theorem divK_clzSetup_shiftNz_spec_within_v6_mod
    (sp b0 v6Old v7Old v2Old m3992 m3984 : Word) (base : Word)
    (hs_ne_0 : (clzResult b0).1 ≠ (0 : Word)) :
    cpsTripleWithin 31 (base + v6ClzOff) (base + v6NormAOff) (modCodeV6 base)
      (((.x5 ↦ᵣ b0) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
        ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984)))
      ((divKFastSetupPost sp ((clzResult b0).1) b0 ((0 : Word) - (clzResult b0).1)
          (b0 <<< (((clzResult b0).1).toNat % 64))) **
       (.x7 ↦ᵣ ((clzResult b0).2 >>> (63 : Nat)))) := by
  have hclz := divK_clz_spec_within_v6_mod b0 v6Old v7Old base
  have hclzf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
     ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984))
    (by pcFree) hclz
  have hsetup := divK_fastSetup_shiftNz_spec_within_v6_mod sp ((clzResult b0).2)
    ((clzResult b0).1) b0 v2Old m3992 m3984 base hs_ne_0
  have hsetupf := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ ((clzResult b0).2 >>> (63 : Nat)))) (by pcFree) hsetup
  exact cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hclzf hsetupf

/-- CLZ ;; fastSetup, shift=0 lane over `modCodeV6`: `v6ClzOff` → `v6CopyAUOff`. -/
theorem divK_clzSetup_shift0_spec_within_v6_mod
    (sp b0 v6Old v7Old v2Old m3992 m3984 : Word) (base : Word)
    (hs_eq_0 : (clzResult b0).1 = (0 : Word)) :
    cpsTripleWithin 31 (base + v6ClzOff) (base + v6CopyAUOff) (modCodeV6 base)
      (((.x5 ↦ᵣ b0) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
        ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984)))
      ((divKFastSetupPost sp ((clzResult b0).1) b0 ((0 : Word) - (clzResult b0).1)
          (b0 <<< (((clzResult b0).1).toNat % 64))) **
       (.x7 ↦ᵣ ((clzResult b0).2 >>> (63 : Nat)))) := by
  have hclz := divK_clz_spec_within_v6_mod b0 v6Old v7Old base
  have hclzf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
     ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984))
    (by pcFree) hclz
  have hsetup := divK_fastSetup_shift0_spec_within_v6_mod sp ((clzResult b0).2)
    ((clzResult b0).1) b0 v2Old m3992 m3984 base hs_eq_0
  have hsetupf := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ ((clzResult b0).2 >>> (63 : Nat)))) (by pcFree) hsetup
  exact cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hclzf hsetupf

/-- CLZ ;; fastSetup ;; normA, shift≠0 lane over `modCodeV6`: `v6ClzOff` → `v6Digit3Off`. -/
theorem divK_clzSetupNormA_shiftNz_spec_within_v6_mod
    (sp b0 a0 a1 a2 a3 v6Old v7Old v2Old v10 m3992 m3984 : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word)
    (hs_ne_0 : (clzResult b0).1 ≠ (0 : Word)) :
    cpsTripleWithin 52 (base + v6ClzOff) (base + v6Digit3Off) (modCodeV6 base)
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
  have hcs := divK_clzSetup_shiftNz_spec_within_v6_mod sp b0 v6Old v7Old v2Old m3992 m3984 base hs_ne_0
  have hcsf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ v10) ** ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4056) ↦ₘ u0Old))
    (by pcFree) hcs
  have hnorma := divK_normA_full_spec_within_v6_mod sp a0 a1 a2 a3
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

/-- CLZ ;; fastSetup ;; copyAU, shift=0 lane over `modCodeV6`: `v6ClzOff` → `v6Digit3Off`. -/
theorem divK_clzSetupCopyAU_shift0_spec_within_v6_mod
    (sp b0 a0 a1 a2 a3 v6Old v7Old v2Old m3992 m3984 : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word)
    (hs_eq_0 : (clzResult b0).1 = (0 : Word)) :
    cpsTripleWithin 40 (base + v6ClzOff) (base + v6Digit3Off) (modCodeV6 base)
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
  have hcs := divK_clzSetup_shift0_spec_within_v6_mod sp b0 v6Old v7Old v2Old m3992 m3984 base hs_eq_0
  have hcsf := cpsTripleWithin_frameR
    (((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4024) ↦ₘ u4Old))
    (by pcFree) hcs
  have hcopy := divK_copyAU_full_spec_within_v6_mod sp a0 a1 a2 a3
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

/-- CLZ ;; fastSetup ;; normA ;; digitChain, shift≠0 lane over `modCodeV6`:
    `v6ClzOff` → `modV6DenormOff` (424 steps).  The digit-chain output is identical
    in structure to the DIV chain (`v6chain{Q,R}*` abbreviations); only the exit
    lands at the mod fast-denorm block. -/
theorem divK_clzSetupNormADigits_shiftNz_spec_within_v6_mod
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
    cpsTripleWithin 424 (base + v6ClzOff) (base + modV6DenormOff) (modCodeV6 base)
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
  have hcsn := divK_clzSetupNormA_shiftNz_spec_within_v6_mod sp b0 a0 a1 a2 a3 v6Old v7Old v2Old v10
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
  have hdc := divK_digitChain_spec_within_v6_mod sp (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0)
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

/-- CLZ ;; fastSetup ;; copyAU ;; digitChain, shift=0 lane over `modCodeV6`:
    `v6ClzOff` → `modV6DenormOff` (412 steps). -/
theorem divK_clzSetupCopyAUDigits_shift0_spec_within_v6_mod
    (sp b0 a0 a1 a2 a3 v6Old v7Old v2Old v10 v9d v11d : Word)
    (qm3 qm2 qm1 qm0 m3992 m3984 retMem dMem dloMem un0Mem scratchMem m40 m48 m56 : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word)
    (hs_eq_0 : (clzResult b0).1 = (0 : Word))
    (halign3 : ((base + v6Digit3Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit3Off + 16)
    (halign2 : ((base + v6Digit2Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit2Off + 16)
    (halign1 : ((base + v6Digit1Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit1Off + 16)
    (halign0 : ((base + v6Digit0Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit0Off + 16) :
    cpsTripleWithin 412 (base + v6ClzOff) (base + modV6DenormOff) (modCodeV6 base)
      (((((.x5 ↦ᵣ b0) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word))) **
         ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
          ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984))) **
        (((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
         ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
         ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
         ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
         ((sp + signExtend12 4024) ↦ₘ u4Old))) **
       ((.x9 ↦ᵣ v9d) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11d) **
        (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        ((sp + signExtend12 4064) ↦ₘ qm3) ** ((sp + signExtend12 4072) ↦ₘ qm2) **
        ((sp + signExtend12 4080) ↦ₘ qm1) ** ((sp + signExtend12 4088) ↦ₘ qm0) **
        ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56)))
      ((((((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ (v6chainQ0 (0 : Word) a3 a2 a1 a0 (v6nD b0))) **
          (.x5 ↦ᵣ (v6chainR0 (0 : Word) a3 a2 a1 a0 (v6nD b0))) ** (.x10 ↦ᵣ (v6nD b0)) **
          (.x7 ↦ᵣ (v6chainQ0 (0 : Word) a3 a2 a1 a0 (v6nD b0) * (v6nD b0))) **
          ((sp + signExtend12 4088) ↦ₘ (v6chainQ0 (0 : Word) a3 a2 a1 a0 (v6nD b0))) **
          ((sp + signExtend12 4056) ↦ₘ (v6chainR0 (0 : Word) a3 a2 a1 a0 (v6nD b0))) **
          ((sp + signExtend12 3984) ↦ₘ (v6nD b0))) **
         ((.x2 ↦ᵣ (base + v6Digit0Off + 16)) ** regOwn .x6 ** regOwn .x9 ** (.x0 ↦ᵣ (0 : Word)) **
          memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
          memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
          memOwn (sp + signExtend12 3936) **
          ((sp + signExtend12 4048) ↦ₘ (v6chainR1 (0 : Word) a3 a2 a1 (v6nD b0))))) **
        (((sp + signExtend12 4064) ↦ₘ (v6chainQ3 (0 : Word) a3 (v6nD b0))) ** ((sp + signExtend12 4024) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 4072) ↦ₘ (v6chainQ2 (0 : Word) a3 a2 (v6nD b0))) **
         ((sp + signExtend12 4032) ↦ₘ (v6chainR3 (0 : Word) a3 (v6nD b0))) **
         ((sp + signExtend12 4080) ↦ₘ (v6chainQ1 (0 : Word) a3 a2 a1 (v6nD b0))) **
         ((sp + signExtend12 4040) ↦ₘ (v6chainR2 (0 : Word) a3 a2 (v6nD b0)))))) **
       (((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 32) ↦ₘ b0) ** ((sp + signExtend12 3992) ↦ₘ ((clzResult b0).1)) **
        ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56))) := by
  have hcs := divK_clzSetupCopyAU_shift0_spec_within_v6_mod sp b0 a0 a1 a2 a3 v6Old v7Old v2Old
    m3992 m3984 u0Old u1Old u2Old u3Old u4Old base hs_eq_0
  have hcsf := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ v9d) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11d) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
     (sp + signExtend12 3936 ↦ₘ scratchMem) **
     ((sp + signExtend12 4064) ↦ₘ qm3) ** ((sp + signExtend12 4072) ↦ₘ qm2) **
     ((sp + signExtend12 4080) ↦ₘ qm1) ** ((sp + signExtend12 4088) ↦ₘ qm0) **
     ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56))
    (by pcFree) hcs
  have hdc := divK_digitChain_spec_within_v6_mod sp (0 : Word) a3 a2 a1 a0 (v6nD b0) base
    ((0 : Word) - (clzResult b0).1) a3 ((clzResult b0).1) ((clzResult b0).2 >>> (63 : Nat)) v9d
    v10 v11d qm3 qm2 qm1 qm0 retMem dMem dloMem un0Mem scratchMem
    halign3 halign2 halign1 halign0
  have hdcf := cpsTripleWithin_frameR
    (((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 32) ↦ₘ b0) ** ((sp + signExtend12 3992) ↦ₘ ((clzResult b0).1)) **
     ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56))
    (by pcFree) hdc
  exact cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcsf hdcf

/-- `modK_fastDenormEpilogue_spec_within_v6` with the clobbered input `x6` exposed
    as `regOwn` (the form the digit chain leaves it in). -/
theorem modK_fastDenormEpilogue_own_spec_within_v6 (sp base : Word)
    (s u0 u1m u2m u3m v5 v7 v10 m0 m8 m16 m24 : Word) :
    cpsTripleWithin (7 + 10) (base + modV6DenormOff) (base + modV6ExitOff) (modCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** regOwn .x6 ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1m) **
       ((sp + signExtend12 4040) ↦ₘ u2m) ** ((sp + signExtend12 4032) ↦ₘ u3m) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ (u0 >>> (s.toNat % 64))) ** (.x6 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 4056) ↦ₘ (u0 >>> (s.toNat % 64))) **
       ((sp + signExtend12 4048) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4040) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4032) ↦ₘ (0 : Word)) **
       ((sp + 32) ↦ₘ (u0 >>> (s.toNat % 64))) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
        (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ s) **
        ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1m) **
        ((sp + signExtend12 4040) ↦ₘ u2m) ** ((sp + signExtend12 4032) ↦ₘ u3m) **
        ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
        ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (r := .x6) (fun v6 => ?_))
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (modK_fastDenormEpilogue_spec_within_v6 sp base s u0 u1m u2m u3m v5 v6 v7 v10 m0 m8 m16 m24)

/-- **Full MOD fast-path body, shift≠0 lane** over `modCodeV6`: clz ;; fastSetup ;;
    normA ;; digitChain ;; fastDenorm ;; mod_epilogue, `v6ClzOff` → `modV6ExitOff`
    (441 steps).  Divides the 4-limb dividend `a[0..3]` by the single-limb divisor
    `b0`; the denormalized single-limb remainder `v6chainR0 … >>> s` lands in `x5`
    and the output cells `sp+32..56` (high limbs zeroed); the quotient digits remain
    in the scratch cells `4088/4080/4072/4064` (framed, unread by MOD). -/
theorem modK_fastBody_shiftNz_spec_within_v6
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
    cpsTripleWithin 441 (base + v6ClzOff) (base + modV6ExitOff) (modCodeV6 base)
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
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x5 ↦ᵣ ((v6chainR0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0)) >>> (((clzResult b0).1).toNat % 64))) **
       (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ (v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))) **
       (.x2 ↦ᵣ (base + v6Digit0Off + 16)) ** regOwn .x9 **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ ((v6chainR0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0)) >>> (((clzResult b0).1).toNat % 64))) **
       ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ ((clzResult b0).1)) ** ((sp + signExtend12 3984) ↦ₘ (v6nD b0)) **
       ((sp + signExtend12 4056) ↦ₘ ((v6chainR0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0)) >>> (((clzResult b0).1).toNat % 64))) **
       ((sp + signExtend12 4048) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4040) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4032) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4088) ↦ₘ (v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))) **
       ((sp + signExtend12 4080) ↦ₘ (v6chainQ1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0))) **
       ((sp + signExtend12 4072) ↦ₘ (v6chainQ2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0))) **
       ((sp + signExtend12 4064) ↦ₘ (v6chainQ3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0))) **
       ((sp + signExtend12 4024) ↦ₘ (v6nU4 a3 b0)) **
       memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
       memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
       memOwn (sp + signExtend12 3936)) := by
  have hdigits := divK_clzSetupNormADigits_shiftNz_spec_within_v6_mod sp b0 a0 a1 a2 a3 v6Old v7Old
    v2Old v10 v9d v11d qm3 qm2 qm1 qm0 m3992 m3984 retMem dMem dloMem un0Mem scratchMem
    m40 m48 m56 u0Old u1Old u2Old u3Old u4Old base hs_ne_0 halign3 halign2 halign1 halign0
  have htail := modK_fastDenormEpilogue_own_spec_within_v6 sp base ((clzResult b0).1)
    (v6chainR0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))
    (v6chainR1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0))
    (v6chainR2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0))
    (v6chainR3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0))
    (v6chainR0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))
    (v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0) * (v6nD b0))
    (v6nD b0) b0 m40 m48 m56
  have htailf := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))) **
     (.x2 ↦ᵣ (base + v6Digit0Off + 16)) ** regOwn .x9 **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3984) ↦ₘ (v6nD b0)) **
     ((sp + signExtend12 4088) ↦ₘ (v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))) **
     ((sp + signExtend12 4080) ↦ₘ (v6chainQ1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0))) **
     ((sp + signExtend12 4072) ↦ₘ (v6chainQ2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0))) **
     ((sp + signExtend12 4064) ↦ₘ (v6chainQ3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0))) **
     ((sp + signExtend12 4024) ↦ₘ (v6nU4 a3 b0)) **
     memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
     memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
     memOwn (sp + signExtend12 3936))
    (by pcFree) htail
  have hbody := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by simp only [EvmAsm.Rv64.AddrNorm.se12_32] at hp; xperm_hyp hp) hdigits htailf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) hbody

/-- **Full MOD fast-path body, shift=0 lane** over `modCodeV6`: `v6ClzOff` →
    `modV6ExitOff` (429 steps).  When the divisor is already normalized (`s = 0`),
    the remainder is `v6chainR0 (0, a3, a2, a1, a0, b0)` directly (no denorm shift). -/
theorem modK_fastBody_shift0_spec_within_v6
    (sp b0 a0 a1 a2 a3 v6Old v7Old v2Old v10 v9d v11d : Word)
    (qm3 qm2 qm1 qm0 m3992 m3984 retMem dMem dloMem un0Mem scratchMem m40 m48 m56 : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word)
    (hs_eq_0 : (clzResult b0).1 = (0 : Word))
    (halign3 : ((base + v6Digit3Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit3Off + 16)
    (halign2 : ((base + v6Digit2Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit2Off + 16)
    (halign1 : ((base + v6Digit1Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit1Off + 16)
    (halign0 : ((base + v6Digit0Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit0Off + 16) :
    cpsTripleWithin 429 (base + v6ClzOff) (base + modV6ExitOff) (modCodeV6 base)
      (((((.x5 ↦ᵣ b0) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word))) **
         ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
          ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984))) **
        (((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
         ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
         ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
         ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
         ((sp + signExtend12 4024) ↦ₘ u4Old))) **
       ((.x9 ↦ᵣ v9d) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11d) **
        (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        ((sp + signExtend12 4064) ↦ₘ qm3) ** ((sp + signExtend12 4072) ↦ₘ qm2) **
        ((sp + signExtend12 4080) ↦ₘ qm1) ** ((sp + signExtend12 4088) ↦ₘ qm0) **
        ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56)))
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x5 ↦ᵣ ((v6chainR0 (0 : Word) a3 a2 a1 a0 (v6nD b0)) >>> (((clzResult b0).1).toNat % 64))) **
       (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ (v6chainQ0 (0 : Word) a3 a2 a1 a0 (v6nD b0))) **
       (.x2 ↦ᵣ (base + v6Digit0Off + 16)) ** regOwn .x9 **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ ((v6chainR0 (0 : Word) a3 a2 a1 a0 (v6nD b0)) >>> (((clzResult b0).1).toNat % 64))) **
       ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ ((clzResult b0).1)) ** ((sp + signExtend12 3984) ↦ₘ (v6nD b0)) **
       ((sp + signExtend12 4056) ↦ₘ ((v6chainR0 (0 : Word) a3 a2 a1 a0 (v6nD b0)) >>> (((clzResult b0).1).toNat % 64))) **
       ((sp + signExtend12 4048) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4040) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4032) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4088) ↦ₘ (v6chainQ0 (0 : Word) a3 a2 a1 a0 (v6nD b0))) **
       ((sp + signExtend12 4080) ↦ₘ (v6chainQ1 (0 : Word) a3 a2 a1 (v6nD b0))) **
       ((sp + signExtend12 4072) ↦ₘ (v6chainQ2 (0 : Word) a3 a2 (v6nD b0))) **
       ((sp + signExtend12 4064) ↦ₘ (v6chainQ3 (0 : Word) a3 (v6nD b0))) **
       ((sp + signExtend12 4024) ↦ₘ (0 : Word)) **
       memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
       memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
       memOwn (sp + signExtend12 3936)) := by
  have hdigits := divK_clzSetupCopyAUDigits_shift0_spec_within_v6_mod sp b0 a0 a1 a2 a3 v6Old v7Old
    v2Old v10 v9d v11d qm3 qm2 qm1 qm0 m3992 m3984 retMem dMem dloMem un0Mem scratchMem
    m40 m48 m56 u0Old u1Old u2Old u3Old u4Old base hs_eq_0 halign3 halign2 halign1 halign0
  have htail := modK_fastDenormEpilogue_own_spec_within_v6 sp base ((clzResult b0).1)
    (v6chainR0 (0 : Word) a3 a2 a1 a0 (v6nD b0))
    (v6chainR1 (0 : Word) a3 a2 a1 (v6nD b0))
    (v6chainR2 (0 : Word) a3 a2 (v6nD b0))
    (v6chainR3 (0 : Word) a3 (v6nD b0))
    (v6chainR0 (0 : Word) a3 a2 a1 a0 (v6nD b0))
    (v6chainQ0 (0 : Word) a3 a2 a1 a0 (v6nD b0) * (v6nD b0))
    (v6nD b0) b0 m40 m48 m56
  have htailf := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (v6chainQ0 (0 : Word) a3 a2 a1 a0 (v6nD b0))) **
     (.x2 ↦ᵣ (base + v6Digit0Off + 16)) ** regOwn .x9 **
     ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3984) ↦ₘ (v6nD b0)) **
     ((sp + signExtend12 4088) ↦ₘ (v6chainQ0 (0 : Word) a3 a2 a1 a0 (v6nD b0))) **
     ((sp + signExtend12 4080) ↦ₘ (v6chainQ1 (0 : Word) a3 a2 a1 (v6nD b0))) **
     ((sp + signExtend12 4072) ↦ₘ (v6chainQ2 (0 : Word) a3 a2 (v6nD b0))) **
     ((sp + signExtend12 4064) ↦ₘ (v6chainQ3 (0 : Word) a3 (v6nD b0))) **
     ((sp + signExtend12 4024) ↦ₘ (0 : Word)) **
     memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
     memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
     memOwn (sp + signExtend12 3936))
    (by pcFree) htail
  have hbody := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by simp only [EvmAsm.Rv64.AddrNorm.se12_32] at hp; xperm_hyp hp) hdigits htailf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) hbody

end EvmAsm.Evm64
