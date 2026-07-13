/-
  Shared declaration home for the MOD n=2 V5 shift/loop path.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopUnifiedBorrowCarry
import EvmAsm.Evm64.DivMod.Spec.N2V5Shift0BundleOfShape
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5PreloopShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Loop
import EvmAsm.Evm64.DivMod.Compose.FullPathN3Loop
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5BridgeShift0
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopUnifiedBorrowCarryMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5PreloopShift0Mod
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5Mod
import EvmAsm.Evm64.DivMod.ModN2V5LaneShared
import EvmAsm.Evm64.DivMod.Spec.N2V5Shift0Shared
import EvmAsm.Evm64.DivMod.Spec.N2V5ModPostShared
import EvmAsm.Evm64.DivMod.Spec.StackPostBridgeMod
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod
import EvmAsm.Evm64.EvmWordArith.CLZLemmas

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

theorem n2_shift0_dispatchPre_to_pathEntry (sp : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2z : b.getLimbN 2 = 0) (hb3z : b.getLimbN 3 = 0) :
    ∀ h,
      (divModStackDispatchPreNoX1 sp a b
        (x9In) raVal
        x2In v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem)) h →
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
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
        ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal))) h := by
  intro h hp
  rw [divModStackDispatchPreNoX1_unfold, divScratchValuesCallNoX1_unfold] at hp
  rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp b b0 b1 0 0 hb0 hb1 hb2z hb3z,
      divScratchValues_unfold] at hp
  rw [word_add_zero]
  xperm_hyp hp

open EvmWord EvmAsm.Rv64

theorem divK_loop_n2_shift0_from_shape_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hb1ge : b1.toNat ≥ 2^63) :
    ∃ bltu_2 bltu_1 bltu_0 : Bool,
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
  -- The three runtime borrow flags, in clean `ult (iterN2V5 …).2.2.1 b1` form.
  obtain ⟨bltu_2, hbltu_2⟩ : ∃ x, x = BitVec.ult (0 : Word) b1 := ⟨_, rfl⟩
  obtain ⟨bltu_1, hbltu_1⟩ :
      ∃ x, x = BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1 := ⟨_, rfl⟩
  obtain ⟨bltu_0, hbltu_0⟩ :
      ∃ x, x = BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1 := ⟨_, rfl⟩
  -- Per-digit `bltu` path matches (shared by the collapse + carry bundle).
  have hc2 : bltu_2 = true → BitVec.ult (0:Word) b1 = true := fun h => by rw [← hbltu_2]; exact h
  have hm2 : bltu_2 = false → ¬ BitVec.ult (0:Word) b1 := fun h => by rw [← hbltu_2, h]; decide
  -- digit-2 remainder collapse (u3 = uTop = 0).
  obtain ⟨hR2u3, hR2uTop, _⟩ := iterN2V5_collapse bltu_2 b0 b1 a2 a3 0 hbnz hb1ge hfwv hc2 hm2
  refine ⟨bltu_2, bltu_1, bltu_0, ?_⟩
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

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Bridge: shift=0 preloop exit (b2 = b3 = 0) plus the framed scratch/return
    cells implies the loop entry bundle over the raw divisor. -/
theorem n2_shift0_loopExit_to_loopN2PreWithScratch (sp : Word)
    (a0 a1 a2 a3 b0 b1 v11Old jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    ∀ h,
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) **
        (.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (2 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (clzResult b1).1) **
        (.x7 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
        (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - (clzResult b1).1)) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
        ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
        ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
        ((sp + signExtend12 4024) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (2 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        ((sp + signExtend12 3968) ↦ₘ retMem) ** ((sp + signExtend12 3960) ↦ₘ dMem) **
        ((sp + signExtend12 3952) ↦ₘ dloMem) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0) **
        ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal))) h →
      ((loopN2PreWithScratchV4NoX1 sp jMem (2 : Word) (clzResult b1).1
        ((clzResult b1).2 >>> (63 : Nat)) (0 : Word) v11Old
        (signExtend12 (0 : BitVec 12) - (clzResult b1).1)
        b0 b1 0 0 a2 a3 0 0 0 a1 a0 0 0 0
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) h := by
  intro h hp
  rw [show signExtend12 (4 : BitVec 12) - (2 : Word) = (2 : Word) from by decide] at hp
  delta loopN2PreWithScratchV4NoX1 loopN2PreWithScratchNoX1 loopN2Pre
  simp only [n2_ub2_off0, n2_ub2_off4088, n2_ub2_off4080, n2_ub2_off4072, n2_ub2_off4064,
    n3_ub1_off0, n3_ub0_off0, n2_qa2, n3_qa1, n3_qa0,
    se12_32, se12_40, se12_48, se12_56] at hp ⊢
  xperm_hyp hp

/-- n=2 v5 shift=0 path `base → denormOff`: preloop (#7468) ∘ bridge ∘ loop
    (#7471), the carry discharged from shape.  Shift=0 analog of
    `fullDivN2_preloop_loop_unified_exact_x1_scratch_v5_noNop_borrowCarry`. -/
theorem evm_div_n2_to_denorm_shift0_from_shape_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 v2 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| (0 : Word) ||| 0 ≠ 0) (hb1nz : b1 ≠ 0)
    (hshift_z : (clzResult b1).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    ∃ bltu_2 bltu_1 bltu_0 : Bool,
    cpsTripleWithin (((8 + 21 + 24 + 4) + 13) + 702) base (base + denormOff)
      (divCode_noNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
        (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
    v2 v5 v6 v7 v10 q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem (signExtend12 (4 : BitVec 12) - (4 : Word))
    hbnz rfl rfl hb1nz hshift_z
  have hPref := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     ((sp + signExtend12 3968) ↦ₘ retMem) ** ((sp + signExtend12 3960) ↦ₘ dMem) **
     ((sp + signExtend12 3952) ↦ₘ dloMem) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0) **
     ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hPre
  obtain ⟨bltu_2, bltu_1, bltu_0, hLoop⟩ := divK_loop_n2_shift0_from_shape_v5_noNop
    sp base jMem (2 : Word) (clzResult b1).1 ((clzResult b1).2 >>> (63 : Nat)) (0 : Word)
    v11Old (signExtend12 (0 : BitVec 12) - (clzResult b1).1)
    a0 a1 a2 a3 b0 b1 0 0 0 raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hb1ge
  have hLoopf := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))
    (by pcFree) hLoop
  refine ⟨bltu_2, bltu_1, bltu_0, ?_⟩
  have hPre' := cpsTripleWithin_weaken (fun h hp => hp)
    (n2_shift0_loopExit_to_loopN2PreWithScratch sp a0 a1 a2 a3 b0 b1 v11Old
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal)
    hPref
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPre' hLoopf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => hp) (fun h hq => hq) hFull

open EvmAsm.Rv64

theorem evm_div_n2_full_shift0_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 v2 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| (0 : Word) ||| 0 ≠ 0) (hb1nz : b1 ≠ 0)
    (hshift_z : (clzResult b1).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    ∃ bltu_2 bltu_1 bltu_0 : Bool,
    cpsTripleWithin (((((8 + 21 + 24 + 4) + 13) + 702)) + 12) base (base + nopOff)
      (divCode_noNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
        (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
  obtain ⟨bltu_2, bltu_1, bltu_0, hA⟩ := evm_div_n2_to_denorm_shift0_from_shape_v5_noNop
    sp base a0 a1 a2 a3 b0 b1 v2 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem raVal hbnz hb1nz hshift_z halign
  refine ⟨bltu_2, bltu_1, bltu_0, ?_⟩
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

open EvmWord EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

@[irreducible]
def fullModN2FrameShift0V5 (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Assertion :=
  let r2 := n2Shift0R2 bltu_2 a2 a3 b0 b1
  let r1 := n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1
  let r0 := n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1
  let scratch2 := if bltu_2 then divKTrialCallV5ScratchOut 0 a3 b1 scratchMem else scratchMem
  let scratch1 := if bltu_1 then divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 b1 scratch2 else scratch2
  let scratchMemF := if bltu_0 then divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 b1 scratch1 else scratch1
  let scratchRet2 := if bltu_2 then (base + div128CallRetOff) else retMem
  let scratchD2 := if bltu_2 then b1 else dMem
  let scratchDLo2 := if bltu_2 then divKTrialCallV5DLo b1 else dloMem
  let scratchUn02 := if bltu_2 then divKTrialCallV5Un0 a3 else scratchUn0
  let scratchRet1 := if bltu_1 then (base + div128CallRetOff) else scratchRet2
  let scratchD1 := if bltu_1 then b1 else scratchD2
  let scratchDLo1 := if bltu_1 then divKTrialCallV5DLo b1 else scratchDLo2
  let scratchUn01 := if bltu_1 then divKTrialCallV5Un0 r2.2.1 else scratchUn02
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (2 : Word)) **
  ((sp + signExtend12 4088) ↦ₘ r0.1) ** ((sp + signExtend12 4080) ↦ₘ r1.1) **
  ((sp + signExtend12 4072) ↦ₘ r2.1) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) ** ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + div128CallRetOff) else scratchRet1)) **
  (sp + signExtend12 3960 ↦ₘ (if bltu_0 then b1 else scratchD1)) **
  (sp + signExtend12 3952 ↦ₘ (if bltu_0 then divKTrialCallV5DLo b1 else scratchDLo1)) **
  (sp + signExtend12 3944 ↦ₘ (if bltu_0 then divKTrialCallV5Un0 r1.2.1 else scratchUn01)) **
  (sp + signExtend12 3936 ↦ₘ scratchMemF) **
  (.x1 ↦ᵣ raVal)

theorem fullModN2FrameShift0V5_unfold {bltu_2 bltu_1 bltu_0 : Bool}
    {sp base a0 a1 a2 a3 b0 b1 retMem dMem dloMem scratchUn0 scratchMem raVal : Word} :
    fullModN2FrameShift0V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
      retMem dMem dloMem scratchUn0 scratchMem raVal =
    (let r2 := n2Shift0R2 bltu_2 a2 a3 b0 b1
     let r1 := n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1
     let r0 := n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1
     let scratch2 := if bltu_2 then divKTrialCallV5ScratchOut 0 a3 b1 scratchMem else scratchMem
     let scratch1 := if bltu_1 then divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 b1 scratch2 else scratch2
     let scratchMemF := if bltu_0 then divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 b1 scratch1 else scratch1
     let scratchRet2 := if bltu_2 then (base + div128CallRetOff) else retMem
     let scratchD2 := if bltu_2 then b1 else dMem
     let scratchDLo2 := if bltu_2 then divKTrialCallV5DLo b1 else dloMem
     let scratchUn02 := if bltu_2 then divKTrialCallV5Un0 a3 else scratchUn0
     let scratchRet1 := if bltu_1 then (base + div128CallRetOff) else scratchRet2
     let scratchD1 := if bltu_1 then b1 else scratchD2
     let scratchDLo1 := if bltu_1 then divKTrialCallV5DLo b1 else scratchDLo2
     let scratchUn01 := if bltu_1 then divKTrialCallV5Un0 r2.2.1 else scratchUn02
     (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (2 : Word)) **
     ((sp + signExtend12 4088) ↦ₘ r0.1) ** ((sp + signExtend12 4080) ↦ₘ r1.1) **
     ((sp + signExtend12 4072) ↦ₘ r2.1) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) ** ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + div128CallRetOff) else scratchRet1)) **
     (sp + signExtend12 3960 ↦ₘ (if bltu_0 then b1 else scratchD1)) **
     (sp + signExtend12 3952 ↦ₘ (if bltu_0 then divKTrialCallV5DLo b1 else scratchDLo1)) **
     (sp + signExtend12 3944 ↦ₘ (if bltu_0 then divKTrialCallV5Un0 r1.2.1 else scratchUn01)) **
     (sp + signExtend12 3936 ↦ₘ scratchMemF) **
     (.x1 ↦ᵣ raVal)) := by
  delta fullModN2FrameShift0V5; rfl

theorem fullModN2FrameShift0V5_pcFree {bltu_2 bltu_1 bltu_0 : Bool}
    {sp base a0 a1 a2 a3 b0 b1 retMem dMem dloMem scratchUn0 scratchMem raVal : Word} :
    (fullModN2FrameShift0V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
      retMem dMem dloMem scratchUn0 scratchMem raVal).pcFree := by
  rw [fullModN2FrameShift0V5_unfold]
  cases bltu_2 <;> cases bltu_1 <;> cases bltu_0 <;>
    simp only [Bool.false_eq_true, if_true, if_false] <;> pcFree

/-- Flag-parameterized shift=0 LOOP body (`loopBodyOff → denormOff`): the
    existential `divK_loop_n2_shift0_from_shape_v5_noNop` (#7471) with the three
    flags + their clean dispatch hypotheses lifted to parameters. -/
theorem divK_loop_n2_shift0_param_v5_noNop_modCode (bltu_2 bltu_1 bltu_0 : Bool)
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
      (modCode_noNop_v5 base)
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
  apply divK_loop_n2_unified_from_source_exact_loopIterScratch_v5_noNop_borrowCarry_modCode
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
theorem evm_mod_n2_to_denorm_shift0_param_v5_noNop (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 v2 v5 v6 v7 v10 v11Old x9In : Word)
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
      (modCode_noNop_v5 base)
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
  have hPre := evm_mod_n2_to_loopSetup_shift0_spec_v5_noNop sp base a0 a1 a2 a3 b0 b1 0 0
    v2 v5 v6 v7 v10 x9In q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz rfl rfl hb1nz hshift_z
  have hPref := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     ((sp + signExtend12 3968) ↦ₘ retMem) ** ((sp + signExtend12 3960) ↦ₘ dMem) **
     ((sp + signExtend12 3952) ↦ₘ dloMem) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0) **
     ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hPre
  have hLoop := divK_loop_n2_shift0_param_v5_noNop_modCode bltu_2 bltu_1 bltu_0
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
  exact cpsTripleWithin_mono_nSteps (by omega) <| cpsTripleWithin_weaken
    (fun h hp => hp) (fun h hq => hq) hFull

/-- Flag-parameterized full shift=0 code path `base → nopOff`: flag-param path ∘
    epilogue bridge ∘ shift=0 epilogue.  Flag-param form of
    `evm_div_n2_full_shift0_spec_v5_noNop` (#7478). -/
theorem evm_mod_n2_full_shift0_param_v5_noNop (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 v2 v5 v6 v7 v10 v11Old x9In : Word)
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
      (modCode_noNop_v5 base)
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
        (.x5 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1) **
        (.x6 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1) **
        (.x7 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1) **
        (.x2 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1) **
        ((sp + signExtend12 4056) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1) **
        ((sp + signExtend12 4048) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1) **
        ((sp + signExtend12 4040) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1) **
        ((sp + signExtend12 4032) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) **
        ((sp + 32) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1) **
        ((sp + 40) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1) **
        ((sp + 48) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1) **
        ((sp + 56) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1)) **
       fullModN2FrameShift0V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
         retMem dMem dloMem scratchUn0 scratchMem raVal) := by
  have hA := evm_mod_n2_to_denorm_shift0_param_v5_noNop bltu_2 bltu_1 bltu_0
    sp base a0 a1 a2 a3 b0 b1 v2 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem raVal hbnz hb1nz hshift_z halign
    hbltu_2 hbltu_1 hbltu_0
  have hB := evm_mod_shift0_epilogue_spec_v5_noNop sp base
    (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1
    (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1
    (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1
    (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1
    (clzResult b1).1
    (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1
    (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    (n2Shift0C3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1)
    b0 b1 0 0 hshift_z
  have hBf := cpsTripleWithin_frameR
    (fullModN2FrameShift0V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (by exact fullModN2FrameShift0V5_pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hbr := loopN2UnifiedPostV5NoX1_shift0_to_epiloguePre bltu_2 bltu_1 bltu_0
        sp base a0 a1 a2 a3 b0 b1 retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      rw [fullDivN2FrameShift0V5_unfold] at hbr
      rw [fullModN2FrameShift0V5_unfold]
      xperm_hyp hbr) hA hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      rw [fullModN2FrameShift0V5_unfold] at hq ⊢
      xperm_hyp hq)
    hFull

open EvmWord EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- THREADED-digit form of the shift=0 remainder correctness: the three v5 n=2
    threaded digit iterates (`n2Shift0R0/R1/R2`) give the limbs of
    `EvmWord.mod a b`.  Bridges the PADDED `n2_shift0_mod_getLimbN_lane` (#7475)
    by collapsing the digit-2 / digit-1 remainder tails to zero. -/
theorem n2_shift0_mod_getLimbN_threaded (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2z : b.getLimbN 2 = 0) (hb3z : b.getLimbN 3 = 0)
    (hb1ge : b1.toNat ≥ 2^63)
    (hc2 : bltu_2 = true → BitVec.ult (0:Word) b1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (0:Word) b1)
    (hc1 : bltu_1 = true → BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1)
    (hc0 : bltu_0 = true → BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    (EvmWord.mod a b).getLimbN 0 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1 ∧
    (EvmWord.mod a b).getLimbN 1 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1 ∧
    (EvmWord.mod a b).getLimbN 2 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1 ∧
    (EvmWord.mod a b).getLimbN 3 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1 := by
  obtain ⟨hd0, hd1, hd2, hd3⟩ := n2_shift0_mod_getLimbN_lane a b a0 a1 a2 a3 b0 b1
    bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2z hb3z hb1ge hc2 hm2 hc1 hm1 hc0 hm0
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
  obtain ⟨hR2u3, hR2uTop, _⟩ := iterN2V5_collapse bltu_2 b0 b1 a2 a3 0 hbnz hb1ge hfwv hc2 hm2
  have hR2 := iterN2V5_step bltu_2 b0 b1 a2 a3 0 hbnz hb1ge hfwv hc2 hm2
  have hR1valid := n2_next_window_lt a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
    (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 _ hR2.2
  obtain ⟨hR1u3, hR1uTop, _⟩ := iterN2V5_collapse bltu_1 b0 b1 a1
    (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
    (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 hbnz hb1ge hR1valid hc1 hm1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [n2Shift0R0, n2Shift0R1, n2Shift0R2]
    rw [hR2u3, hR2uTop, hR1u3, hR1uTop]; exact hd0
  · simp only [n2Shift0R0, n2Shift0R1, n2Shift0R2]
    rw [hR2u3, hR2uTop, hR1u3, hR1uTop]; exact hd1
  · simp only [n2Shift0R0, n2Shift0R1, n2Shift0R2]
    rw [hR2u3, hR2uTop, hR1u3, hR1uTop]; exact hd2
  · simp only [n2Shift0R0, n2Shift0R1, n2Shift0R2]
    rw [hR2u3, hR2uTop, hR1u3, hR1uTop]; exact hd3

/-- The `sp+3936` scratch-mem value carried by `fullDivN2FrameShift0V5` (matches
    its `scratchMemF` let exactly). -/
def n2Shift0ModScratchMemF (bltu_2 bltu_1 bltu_0 : Bool) (a1 a2 a3 b0 b1 scratchMem : Word) : Word :=
  let r2 := n2Shift0R2 bltu_2 a2 a3 b0 b1
  let r1 := n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1
  let scratch2 := if bltu_2 then divKTrialCallV5ScratchOut 0 a3 b1 scratchMem else scratchMem
  let scratch1 := if bltu_1 then divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 b1 scratch2 else scratch2
  if bltu_0 then divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 b1 scratch1 else scratch1

/-- Shift=0 post bridge: the flag-param full-path post → `modStackDispatchPostV5`.
    Routes through the all-regIs `modConcretePostNoX1ExactRegsFrame` (pure `xperm`,
    no per-atom weaken), then the bulk regIs→regOwn weakeners.  Mirrors the DIV shift0 post bridge. -/
theorem n2_shift0_fullPost_to_modStackDispatchPostV5
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.mod a b).getLimbN 0 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1)
    (hdiv1 : (EvmWord.mod a b).getLimbN 1 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1)
    (hdiv2 : (EvmWord.mod a b).getLimbN 2 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1)
    (hdiv3 : (EvmWord.mod a b).getLimbN 3 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) :
    ∀ h,
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x5 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1) **
        (.x6 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1) **
        (.x7 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1) **
        (.x2 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1) **
        ((sp + signExtend12 4056) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1) **
        ((sp + signExtend12 4048) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1) **
        ((sp + signExtend12 4040) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1) **
        ((sp + signExtend12 4032) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) **
        ((sp + 32) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1) **
        ((sp + 40) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1) **
        ((sp + 48) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1) **
        ((sp + 56) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1)) **
       fullModN2FrameShift0V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
         retMem dMem dloMem scratchUn0 scratchMem raVal) h →
      modStackDispatchPostV5 sp a b h := by
  intro h hq
  rw [fullModN2FrameShift0V5_unfold] at hq
  -- Map to the all-regIs ExactRegs frame (pure xperm, no atom weaken).
  have hExact :
      (modConcretePostNoX1ExactRegsFrame sp a b (signExtend12 4095) raVal
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1
        (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1
        (n2Shift0R2 bltu_2 a2 a3 b0 b1).1
        (0 : Word)
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.2
        (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).2.2.2.2.2
        (n2Shift0R2 bltu_2 a2 a3 b0 b1).2.2.2.2.2
        (0 : Word)
        (clzResult b1).1 (2 : Word) (0 : Word)
        (if bltu_0 then (base + div128CallRetOff)
          else if bltu_1 then (base + div128CallRetOff)
          else if bltu_2 then (base + div128CallRetOff) else retMem)
        (if bltu_0 then b1 else if bltu_1 then b1 else if bltu_2 then b1 else dMem)
        (if bltu_0 then divKTrialCallV5DLo b1
          else if bltu_1 then divKTrialCallV5DLo b1
          else if bltu_2 then divKTrialCallV5DLo b1 else dloMem)
        (if bltu_0 then divKTrialCallV5Un0 (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).2.1
          else if bltu_1 then divKTrialCallV5Un0 (n2Shift0R2 bltu_2 a2 a3 b0 b1).2.1
          else if bltu_2 then divKTrialCallV5Un0 a3 else scratchUn0) **
       ((sp + signExtend12 3936) ↦ₘ n2Shift0ModScratchMemF bltu_2 bltu_1 bltu_0 a1 a2 a3 b0 b1 scratchMem)) h := by
    rw [modConcretePostNoX1ExactRegsFrame_unfold,
        evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
        evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b)
          (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1
          (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1
          (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1
          (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1 hdiv0 hdiv1 hdiv2 hdiv3,
        divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
    delta n2Shift0ModScratchMemF
    rw [word_add_zero] at hq
    xperm_hyp hq
  rw [modStackDispatchPostV5]
  exact sepConj_mono
    (fun h hp => modStackDispatchPostCallableExactFrame_weaken sp a b raVal (signExtend12 4095) h
      (by rw [modStackDispatchPostCallableExactFrame_unfold]
          exact modConcretePostNoX1ExactRegs_weaken_callable_frame sp a b h hp))
    (fun h hp => memIs_implies_memOwn h hp)
    h hExact

/-- The shift=0 half of `lane_n2`: dispatch precondition → `modStackDispatchPostV5`
    over `modCode_noNop_v5`, given the normalization shift is zero.  Pins the three
    borrow flags to their canonical `ult` values, then composes the pre-lift
    (#7475), the flag-param full shift=0 path, and the shift=0 post bridge. -/
theorem evm_mod_n2_lane_shift0_v5 (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0)
    (hb2z : b.getLimbN 2 = 0) (hb3z : b.getLimbN 3 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 1)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  have hb1ge : (b.getLimbN 1).toNat ≥ 2 ^ 63 := clz_zero_imp_msb hshift_z
  have hb1ne : b.getLimbN 1 ≠ 0 := hb1nz
  have hbnz' : b0 ||| b.getLimbN 1 ||| (0 : Word) ||| 0 ≠ 0 := by
    intro hz
    exact hb1ne ((BitVec.or_eq_zero_iff.mp (BitVec.or_eq_zero_iff.mp
      (BitVec.or_eq_zero_iff.mp hz).1).1).2)
  -- canonical flags (clean ult, threaded iterN2V5 form)
  obtain ⟨bltu_2, hbltu_2⟩ : ∃ x, x = BitVec.ult (0 : Word) (b.getLimbN 1) := ⟨_, rfl⟩
  obtain ⟨bltu_1, hbltu_1⟩ :
      ∃ x, x = BitVec.ult (iterN2V5 bltu_2 b0 (b.getLimbN 1) 0 0 a2 a3 0 0 0).2.2.1
        (b.getLimbN 1) := ⟨_, rfl⟩
  obtain ⟨bltu_0, hbltu_0⟩ :
      ∃ x, x = BitVec.ult (iterN2V5 bltu_1 b0 (b.getLimbN 1) 0 0 a1
        (iterN2V5 bltu_2 b0 (b.getLimbN 1) 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 (b.getLimbN 1) 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1
        (b.getLimbN 1) := ⟨_, rfl⟩
  have hc2 : bltu_2 = true → BitVec.ult (0 : Word) (b.getLimbN 1) = true :=
    fun h => by rw [← hbltu_2]; exact h
  have hm2 : bltu_2 = false → ¬ BitVec.ult (0 : Word) (b.getLimbN 1) :=
    fun h => by rw [← hbltu_2, h]; decide
  have hc1 : bltu_1 = true →
      BitVec.ult (iterN2V5 bltu_2 b0 (b.getLimbN 1) 0 0 a2 a3 0 0 0).2.2.1 (b.getLimbN 1) = true :=
    fun h => by rw [← hbltu_1]; exact h
  have hm1 : bltu_1 = false →
      ¬ BitVec.ult (iterN2V5 bltu_2 b0 (b.getLimbN 1) 0 0 a2 a3 0 0 0).2.2.1 (b.getLimbN 1) :=
    fun h => by rw [← hbltu_1, h]; decide
  have hc0 : bltu_0 = true →
      BitVec.ult (iterN2V5 bltu_1 b0 (b.getLimbN 1) 0 0 a1
        (iterN2V5 bltu_2 b0 (b.getLimbN 1) 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 (b.getLimbN 1) 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1
        (b.getLimbN 1) = true :=
    fun h => by rw [← hbltu_0]; exact h
  have hm0 : bltu_0 = false →
      ¬ BitVec.ult (iterN2V5 bltu_1 b0 (b.getLimbN 1) 0 0 a1
        (iterN2V5 bltu_2 b0 (b.getLimbN 1) 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 (b.getLimbN 1) 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1
        (b.getLimbN 1) :=
    fun h => by rw [← hbltu_0, h]; decide
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ := n2_shift0_mod_getLimbN_threaded a b
    a0 a1 a2 a3 b0 (b.getLimbN 1) bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 rfl hb2z hb3z
    hb1ge hc2 hm2 hc1 hm1 hc0 hm0
  have hpath := evm_mod_n2_full_shift0_param_v5_noNop bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 (b.getLimbN 1) ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
    (signExtend12 (4 : BitVec 12) - (4 : Word))
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem raVal hbnz' hb1ne hshift_z halign
    hbltu_2 hbltu_1 hbltu_0
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n2_shift0_dispatchPre_to_pathEntry sp a b a0 a1 a2 a3 b0 (b.getLimbN 1)
      raVal v5 v6 v7 v10 v11Old (signExtend12 (4 : BitVec 12) - (4 : Word))
      ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
      ha0 ha1 ha2 ha3 hb0 rfl hb2z hb3z h hp
  · intro h hq
    exact n2_shift0_fullPost_to_modStackDispatchPostV5 bltu_2 bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 (b.getLimbN 1) retMem dMem dloMem scratch_un0 scratchMem raVal
      ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq

/-- The complete v5 n=2 MOD lane: discharges the `shift0lane` hypothesis of
    `evm_mod_n2_lane_v5` (#7473) with `evm_mod_n2_lane_shift0_v5`. -/
theorem evm_mod_n2_lane_complete_v5 (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1nz : b.getLimbN 1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) :=
  evm_mod_n2_lane_v5 sp base a b raVal v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem hbnz hb3z hb2z hb1nz halign
    (fun hsh => evm_mod_n2_lane_shift0_v5 sp base a b raVal v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem rfl rfl rfl rfl rfl hb2z hb3z
      hb1nz hsh halign)

end EvmAsm.Evm64
