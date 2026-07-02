/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5ParamShift0

  Flag-PARAMETERIZED v5 n=2 shift=0 execution path (loop / preloop+loop /
  full base→nopOff), taking the three runtime borrow flags `bltu_2 bltu_1 bltu_0`
  and their clean `ult (iterN2V5 …) b1` dispatch hypotheses as inputs.  These are
  the shift=0 analogs of the EXISTENTIAL `divK_loop_n2_shift0_from_shape_v5_noNop`
  (#7471) / `evm_div_n2_to_denorm_shift0_from_shape_v5_noNop` (#7472) /
  `evm_div_n2_full_shift0_spec_v5_noNop` (#7478), but in the flag-parameterized
  form the lane needs (mirroring the shift≠0 chain #7449/#7463 consumed by
  `evm_div_n2_lane_shiftNz_v5`, #7465) so that the per-digit `bltu` dispatch facts
  are available for the quotient-correctness (`hdiv`) proof.  Bead
  `evm-asm-wbc4i.9.2.3`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopUnifiedBorrowCarry
import EvmAsm.Evm64.DivMod.Spec.N2V5Shift0BundleOfShape
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5PreloopShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5FullShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Loop
import EvmAsm.Evm64.DivMod.Compose.FullPathN3Loop
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Flag-parameterized shift=0 LOOP body (`loopBodyOff → denormOff`): the
    existential `divK_loop_n2_shift0_from_shape_v5_noNop` (#7471) with the three
    flags + their clean dispatch hypotheses lifted to parameters. -/
theorem divK_loop_n2_shift0_param_v5_noNop (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hb1ge : b1.toNat ≥ 2^63)
    (hbltu_2 : bltu_2 = BitVec.ult (0 : Word) b1)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    cpsTripleWithin 702 (base + loopBodyOff) (base + denormOff)
      (divCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        b0 b1 0 0 a2 a3 0 0 0 a1 a0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2UnifiedPostV5NoX1 bltu_2 bltu_1 bltu_0 sp base
        b0 b1 0 0 a2 a3 0 0 0 a1 a0
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| (0:Word) ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : b1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hz] at hb1ge; simp at hb1ge
  have hvpos : 2^127 ≤ val256 b0 b1 0 0 := by simp only [EvmWord.val256, h0]; omega
  have hfwv : val256 a2 a3 0 0 < 2^64 * val256 b0 b1 0 0 := by
    have ha : val256 a2 a3 0 0 < 2^128 := by
      have := a2.isLt; have := a3.isLt; simp only [EvmWord.val256, h0]; omega
    calc val256 a2 a3 0 0 < 2^128 := ha
      _ ≤ 2^64 * 2^127 := by norm_num
      _ ≤ 2^64 * val256 b0 b1 0 0 := Nat.mul_le_mul_left _ hvpos
  have hc2 : bltu_2 = true → BitVec.ult (0:Word) b1 = true := fun h => by rw [← hbltu_2]; exact h
  have hm2 : bltu_2 = false → ¬ BitVec.ult (0:Word) b1 := fun h => by rw [← hbltu_2, h]; decide
  obtain ⟨hR2u3, hR2uTop, _⟩ := iterN2V5_collapse bltu_2 b0 b1 a2 a3 0 hbnz hb1ge hfwv hc2 hm2
  apply divK_loop_n2_unified_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
    bltu_2 bltu_1 bltu_0 sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    b0 b1 0 0 a2 a3 0 0 0 a1 a0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign
  case hbltu_2 =>
    exact hbltu_2
  case hbltu_1 =>
    cases bltu_2 <;>
      simp only [iterN2V5, reduceIte, Bool.false_eq_true] at hbltu_1 ⊢ <;> exact hbltu_1
  case hbltu_0 =>
    cases bltu_2 <;> cases bltu_1 <;>
      simp only [iterN2V5, reduceIte, Bool.false_eq_true] at hR2u3 hR2uTop hbltu_0 ⊢ <;>
      rw [hR2u3, hR2uTop] <;> exact hbltu_0
  case hcarry =>
    exact loopN2SelectedBorrowCarryV5_shift0_of_shape a0 a1 a2 a3 b0 b1
      bltu_2 bltu_1 bltu_0 hb1ge hc2 hm2
      (fun h => by rw [← hbltu_1]; exact h)
      (fun h => by rw [← hbltu_1, h]; decide)
      (fun h => by rw [← hbltu_0]; exact h)
      (fun h => by rw [← hbltu_0, h]; decide)

/-- Flag-parameterized shift=0 path `base → denormOff`: preloop (#7468) ∘ bridge ∘
    flag-param loop, the carry discharged from shape.  Flag-param form of #7472. -/
theorem evm_div_n2_to_denorm_shift0_param_v5_noNop (bltu_2 bltu_1 bltu_0 : Bool)
    (x9In : Word)
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 v2 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| (0 : Word) ||| 0 ≠ 0) (hb1nz : b1 ≠ 0)
    (hshift_z : (clzResult b1).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 = BitVec.ult (0 : Word) b1)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    cpsTripleWithin (((8 + 21 + 24 + 4) + 13) + 702) base (base + denormOff)
      (divCode_noNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
        (.x9 ↦ᵣ x9In) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
        ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
        ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
        ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
        ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
        ((sp + signExtend12 4024) ↦ₘ u4Old) **
        ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
        ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        ((sp + signExtend12 3968) ↦ₘ retMem) ** ((sp + signExtend12 3960) ↦ₘ dMem) **
        ((sp + signExtend12 3952) ↦ₘ dloMem) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0) **
        ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal)))
      ((loopN2UnifiedPostV5NoX1 bltu_2 bltu_1 bltu_0 sp base
        b0 b1 0 0 a2 a3 0 0 0 a1 a0
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) := by
  have hb1ge : b1.toNat ≥ 2^63 := clz_zero_imp_msb hshift_z
  have hPre := evm_div_n2_to_loopSetup_shift0_spec_v5_noNop sp base a0 a1 a2 a3 b0 b1 0 0
    v2 v5 v6 v7 v10 q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem x9In
    hbnz rfl rfl hb1nz hshift_z
  have hPref := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     ((sp + signExtend12 3968) ↦ₘ retMem) ** ((sp + signExtend12 3960) ↦ₘ dMem) **
     ((sp + signExtend12 3952) ↦ₘ dloMem) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0) **
     ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hPre
  have hLoop := divK_loop_n2_shift0_param_v5_noNop bltu_2 bltu_1 bltu_0
    sp base jMem (2 : Word) (clzResult b1).1 ((clzResult b1).2 >>> (63 : Nat)) (0 : Word)
    v11Old (signExtend12 (0 : BitVec 12) - (clzResult b1).1)
    a0 a1 a2 a3 b0 b1 0 0 0 raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hb1ge hbltu_2 hbltu_1 hbltu_0
  have hLoopf := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))
    (by pcFree) hLoop
  have hPre' := cpsTripleWithin_weaken (fun h hp => hp)
    (n2_shift0_loopExit_to_loopN2PreWithScratch sp a0 a1 a2 a3 b0 b1 v11Old
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal)
    hPref
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPre' hLoopf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => hp) (fun h hq => hq) hFull

/-- Flag-parameterized full shift=0 code path `base → nopOff`: flag-param path ∘
    epilogue bridge ∘ shift=0 epilogue.  Flag-param form of
    `evm_div_n2_full_shift0_spec_v5_noNop` (#7478). -/
theorem evm_div_n2_full_shift0_param_v5_noNop (bltu_2 bltu_1 bltu_0 : Bool)
    (x9In : Word)
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 v2 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| (0 : Word) ||| 0 ≠ 0) (hb1nz : b1 ≠ 0)
    (hshift_z : (clzResult b1).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 = BitVec.ult (0 : Word) b1)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    cpsTripleWithin (((((8 + 21 + 24 + 4) + 13) + 702)) + 12) base (base + nopOff)
      (divCode_noNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
        (.x9 ↦ᵣ x9In) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
        ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
        ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
        ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
        ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
        ((sp + signExtend12 4024) ↦ₘ u4Old) **
        ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
        ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        ((sp + signExtend12 3968) ↦ₘ retMem) ** ((sp + signExtend12 3960) ↦ₘ dMem) **
        ((sp + signExtend12 3952) ↦ₘ dloMem) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0) **
        ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal)))
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x5 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1) **
        (.x6 ↦ᵣ (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1) **
        (.x7 ↦ᵣ (n2Shift0R2 bltu_2 a2 a3 b0 b1).1) **
        (.x2 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1) **
        ((sp + signExtend12 4088) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1) **
        ((sp + signExtend12 4080) ↦ₘ (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1) **
        ((sp + signExtend12 4072) ↦ₘ (n2Shift0R2 bltu_2 a2 a3 b0 b1).1) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + 32) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1) **
        ((sp + 40) ↦ₘ (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1) **
        ((sp + 48) ↦ₘ (n2Shift0R2 bltu_2 a2 a3 b0 b1).1) **
        ((sp + 56) ↦ₘ (0 : Word))) **
       fullDivN2FrameShift0V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
         retMem dMem dloMem scratchUn0 scratchMem raVal) := by
  have hA := evm_div_n2_to_denorm_shift0_param_v5_noNop bltu_2 bltu_1 bltu_0
    x9In sp base a0 a1 a2 a3 b0 b1 v2 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem raVal hbnz hb1nz hshift_z halign
    hbltu_2 hbltu_1 hbltu_0
  have hB := evm_div_shift0_epilogue_spec_v5_noNop sp base
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) (clzResult b1).1
    (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1
    (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    (n2Shift0C3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1)
    (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1
    (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1
    (n2Shift0R2 bltu_2 a2 a3 b0 b1).1
    (0 : Word)
    b0 b1 0 0 hshift_z
  have hBf := cpsTripleWithin_frameR
    (fullDivN2FrameShift0V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (by exact fullDivN2FrameShift0V5_pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hbr := loopN2UnifiedPostV5NoX1_shift0_to_epiloguePre bltu_2 bltu_1 bltu_0
        sp base a0 a1 a2 a3 b0 b1 retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      xperm_hyp hbr) hA hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

end EvmAsm.Evm64
