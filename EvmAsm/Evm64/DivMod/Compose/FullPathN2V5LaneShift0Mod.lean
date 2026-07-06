/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5LaneShift0Mod

  The v5 n=2 MOD lane, shift=0 case, and the full discharged combiner.

  - `n2_shift0_mod_getLimbN_threaded`: THREADED-digit form of the shift=0 remainder
    correctness, `(EvmWord.mod a b).getLimbN i = (n2Shift0R0 …) remainder fields`, bridged
    from the PADDED `n2_shift0_mod_getLimbN_lane` (#7475) via the digit-2/digit-1
    `iterN2V5_collapse` telescope (as in `n2_shift0_acc_quot`).
  - `n2_shift0_fullPost_to_modStackDispatchPostV5`: the shift=0 post bridge,
    mapping the flag-param full-path post (epilogue regs + `fullModN2FrameShift0V5`,
    regIs `x1`) to `modStackDispatchPostV5` via the all-regIs
    `modConcretePostNoX1ExactRegsFrame` (so the regIs→regOwn weakening is done in
    bulk by `modConcretePostNoX1ExactRegs_weaken_callable_frame` +
    `modStackDispatchPostCallableExactFrame_weaken`).  Mirrors the DIV shift0 post bridge.
  - `evm_mod_n2_lane_shift0_v5`: the shift=0 half of `lane_n2` (pins canonical
    flags, composes pre-lift #7475 + flag-param full path + post bridge).  Mirrors the DIV n=2 shift0 lane.
  - `evm_mod_n2_lane_complete_v5`: discharges the `shift0lane` hypothesis of the
    combiner `evm_mod_n2_lane_v5` (#7473) — the COMPLETE n=2 MOD lane.

  Bead `evm-asm-wbc4i.10.3.2.4.4`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5ParamShift0Mod
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5LaneMod
import EvmAsm.Evm64.DivMod.Spec.N2V5Shift0ModLimb
import EvmAsm.Evm64.DivMod.Spec.N2V5Shift0PreLift
import EvmAsm.Evm64.DivMod.Spec.N2V5ConcretePostBridgeMod
import EvmAsm.Evm64.DivMod.Spec.StackPostBridgeMod
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod
import EvmAsm.Evm64.EvmWordArith.CLZLemmas

namespace EvmAsm.Evm64

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
