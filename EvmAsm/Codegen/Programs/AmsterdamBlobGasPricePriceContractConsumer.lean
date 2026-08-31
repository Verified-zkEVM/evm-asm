import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBodySpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody10Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody11Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14TerminalSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Composition
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceOuterSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundQBackComposition
import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceU256Sat
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceTaylorTie
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody7Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody8Spec
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceDivisionBridge
import EvmAsm.Rv64.MemSat
import Batteries.Tactic.OpenPrivate
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPricePriceContractWitness

set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

/-!
  Consumer side of the `priceContract` excess=0 witness (#12346, K70 seam):
  the exit-divide + tail assembly, the single-exit body triple, the ABI-shell
  lift, and the final `priceContract_ex0_inhabited` non-vacuity witness.
  This file is split from `AmsterdamBlobGasPricePriceContractWitness.lean`
  (which holds the collapse/drop-absurd-exit scaffold) to stay under the
  1500-line cap.  NON-VACUITY witness for the single `excess = 0` input, NOT
  a discharge of the contract; `excess ≠ 0` inputs are NOT covered here.
-/

namespace EvmAsm.Codegen.AmsterdamBlobGasPricePriceContractWitness

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14TerminalSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody10Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceU256Sat
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell
open EvmAsm.Codegen.AmsterdamBlobGasPrice
open EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceTaylorTie
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody5Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceDivisionBridge

open private bodyVals cpsNBranchWithin_drop_absurd_exit loopCells loopFrame orMem orPost orPre
  or_chainP2_owned parity1 price_setup_spec_owned roundPreHead roundPreMem roundQBACKPost
  roundQBACKPost_to_parity1 setupBase setupFrame taylor_round_excess0_qback_owned
  taylor_round_quotient_excess0 temps7
  from EvmAsm.Codegen.Programs.AmsterdamBlobGasPricePriceContractWitness

/-! ## The exit-divide and tail at `excess = 0` -/

/-- The caller residual through the exit-divide: the output-geometry pure over
    the empty caller scratch. -/
@[reducible] private def exitdivFR : Assertion := ⌜priceOutputGeometry sampleOutPtr⌝

private theorem exitdivFR_pcFree : exitdivFR.pcFree := by unfold exitdivFR; pcf

/-- The exit-divide quotient limbs at `excess = 0` (`s = [taylorDW, 0, 0, 0, 0, 0]`). -/
private def edQ0 : Word := exitdivQ0 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
private def edQ1 : Word := exitdivQ1 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
private def edQ2 : Word := exitdivQ2 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
private def edQ3 : Word := exitdivQ3 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
private def edQ4 : Word := exitdivQ4 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
private def edQ5 : Word := exitdivQ5 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
private def edZ1 : Word := (exitdivZ0 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)).2.1

private def edZ0 : Word := (exitdivZ0 taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)).1
private def sampleSumX30 : Word :=
  ((sampleNewSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) +
    signExtend12 (-8 : BitVec 12)

/-- `(x.zeroExtend 64).truncate 8` is the identity on 8-bit words (the emitted
    tail spells `tailOutputFullReplaceBE` with the simplification applied). -/
private theorem truncate_zeroExtend_byte (x : BitVec 8) :
    (x.zeroExtend 64).truncate 8 = x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.truncate, BitVec.zeroExtend]

/-- The exit-divide quotient limbs at `excess = 0` equal `natToLimbs 6 1`
    (`taylorExp384 0 = some 1`, model result 1). -/
private theorem edQs_eq_natToLimbs : [edQ0, edQ1, edQ2, edQ3, edQ4, edQ5] = natToLimbs 6 1 := by
  simpa only [edQ0, edQ1, edQ2, edQ3, edQ4, edQ5] using exitdiv_q_model_step 0 1
    taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    (by decide : 0 < EvmAsm.Stateless.SpecRef.taylorWord64Bound)
    (by simpa [EvmAsm.Stateless.SpecRef.taylorExp384] using taylor_price_outcome_zero)
    (by decide : limbsToNat [taylorDW, (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word)] =
      (priceLoopPrefix 0 495).2)

private theorem edQk_val (k : Nat) :
    List.head? ([edQ0, edQ1, edQ2, edQ3, edQ4, edQ5].drop k) =
      List.head? ((natToLimbs 6 1).drop k) := by
  exact congrArg (fun l => List.head? (l.drop k)) edQs_eq_natToLimbs

private theorem edQ0_one : edQ0 = (1 : Word) := by
  have hsome : some edQ0 = some (BitVec.ofNat 64 1) := by
    simpa only [List.head?, List.drop, natToLimbs] using edQk_val 0
  exact Option.some.inj hsome

private theorem edQk_zero (k : Nat) (hk : k < 6) (hkge : 1 ≤ k) :
    List.head? ([edQ0, edQ1, edQ2, edQ3, edQ4, edQ5].drop k) = (0 : Word) := by
  have h := edQk_val k
  interval_cases k <;> simp only [List.head?, List.drop, natToLimbs] at h ⊢ <;> exact h

private theorem edQ1_zero : edQ1 = (0 : Word) := by
  have hsome : some edQ1 = some (0 : Word) := by
    simpa only [List.head?, List.drop] using edQk_zero 1 (by decide) (by decide)
  exact Option.some.inj hsome

private theorem edQ2_zero : edQ2 = (0 : Word) := by
  have hsome : some edQ2 = some (0 : Word) := by
    simpa only [List.head?, List.drop] using edQk_zero 2 (by decide) (by decide)
  exact Option.some.inj hsome

private theorem edQ3_zero : edQ3 = (0 : Word) := by
  have hsome : some edQ3 = some (0 : Word) := by
    simpa only [List.head?, List.drop] using edQk_zero 3 (by decide) (by decide)
  exact Option.some.inj hsome

private theorem edQ4_zero : edQ4 = (0 : Word) :=
  Option.some.inj (by simpa only [List.head?, List.drop] using edQk_zero 4 (by decide) (by decide))
private theorem edQ5_zero : edQ5 = (0 : Word) :=
  Option.some.inj (by simpa only [List.head?, List.drop] using edQk_zero 5 (by decide) (by decide))

private theorem edTailBytes_eq :
    tailOutputBytes edQ0 edQ1 edQ2 edQ3 = natToBeBytes 32 1 := by
  rw [edQ0_one, edQ1_zero, edQ2_zero, edQ3_zero]
  decide

/-- The status-0 tail post at `excess = 0` with the output cells in the
    caller-value-independent `tailOutputFullReplaceBE (0 : Word)` form.  The
    frame and workspace pins are kept; the `priceBodyPost` weaken owns them. -/
private def edStatus0RawExit : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ sampleOutPtr) **
    (.x22 ↦ᵣ (sampleNewSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x7 ↦ᵣ BitVec.setWidth 64 (extractByte edQ0 0)) ** (.x28 ↦ᵣ (sampleOutPtr + 31)) **
    (.x29 ↦ᵣ (32 : Word)) ** (.x30 ↦ᵣ (32 : Word)) **
    ((sampleNewSp + signExtend12 (160 : BitVec 12)) ↦ₘ edQ0) **
    bytesRegion sampleOutPtr (tailOutputBytes edQ0 edQ1 edQ2 edQ3) **
    (.x2 ↦ᵣ sampleNewSp) ** (.x1 ↦ᵣ (sampleSaved .x1)) **
    (.x11 ↦ᵣ sampleOutPtr) ** (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ taylorDW) **
    (.x18 ↦ᵣ (2 : Word)) ** (.x19 ↦ᵣ sampleStackB) ** (.x20 ↦ᵣ sampleStackA) **
    (.x31 ↦ᵣ (lcnt 5 + signExtend12 (-1 : BitVec 12))) **
    (.x5 ↦ᵣ (edQ4 ||| edQ5)) ** (.x6 ↦ᵣ edQ5) **
    frameSlotsSaved priceFrame sampleNewSp sampleSaved **
    ((sampleNewSp + signExtend12 (64 : BitVec 12)) + signExtend12 (0 : BitVec 12) ↦ₘ taylorDW) **
    ((sampleNewSp + signExtend12 (64 : BitVec 12)) + signExtend12 (8 : BitVec 12) ↦ₘ (0 : Word)) **
    ((sampleNewSp + signExtend12 (64 : BitVec 12)) + signExtend12 (16 : BitVec 12) ↦ₘ (0 : Word)) **
    ((sampleNewSp + signExtend12 (64 : BitVec 12)) + signExtend12 (24 : BitVec 12) ↦ₘ (0 : Word)) **
    ((sampleNewSp + signExtend12 (64 : BitVec 12)) + signExtend12 (32 : BitVec 12) ↦ₘ (0 : Word)) **
    ((sampleNewSp + signExtend12 (64 : BitVec 12)) + signExtend12 (40 : BitVec 12) ↦ₘ (0 : Word)) **
    ((sampleNewSp + signExtend12 (112 : BitVec 12)) + signExtend12 (0 : BitVec 12) ↦ₘ (0 : Word)) **
    ((sampleNewSp + signExtend12 (112 : BitVec 12)) + signExtend12 (8 : BitVec 12) ↦ₘ (0 : Word)) **
    ((sampleNewSp + signExtend12 (112 : BitVec 12)) + signExtend12 (16 : BitVec 12) ↦ₘ (0 : Word)) **
    ((sampleNewSp + signExtend12 (112 : BitVec 12)) + signExtend12 (24 : BitVec 12) ↦ₘ (0 : Word)) **
    ((sampleNewSp + signExtend12 (112 : BitVec 12)) + signExtend12 (32 : BitVec 12) ↦ₘ (0 : Word)) **
    ((sampleNewSp + signExtend12 (112 : BitVec 12)) + signExtend12 (40 : BitVec 12) ↦ₘ (0 : Word)) **
    ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (8 : Word) ↦ₘ edQ1) **
    ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (16 : Word) ↦ₘ edQ2) **
    ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (24 : Word) ↦ₘ edQ3) **
    ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (32 : Word) ↦ₘ edQ4) **
    ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (40 : Word) ↦ₘ edQ5) **
    exitdivFR

/-- The exit-divide precondition at `excess = 0`, structured with the temps and
    output cells trailing (matching `roundZero` up to permutation). -/
private def edHead (_o0 _o1 _o2 _o3 : Word) : Assertion :=
  (.x18 ↦ᵣ (2 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜(0 : Word) = (0 : Word)⌝ **
    (.x2 ↦ᵣ sampleNewSp) ** (.x1 ↦ᵣ (sampleSaved .x1)) **
    (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ sampleOutPtr) **
    (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ taylorDW) **
    (.x19 ↦ᵣ sampleStackB) ** (.x20 ↦ᵣ sampleStackA) **
    (.x21 ↦ᵣ sampleOutPtr) ** (.x22 ↦ᵣ (sampleNewSp + signExtend12 (160 : BitVec 12))) **
    (.x6 ↦ᵣ (0 : Word)) **
    frameSlotsSaved priceFrame sampleNewSp sampleSaved ** loopCells

private def edPre (o0 o1 o2 o3 v7 v28 v29 v30 v31 : Word) : Assertion :=
  edHead o0 o1 o2 o3 **
  (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
  (sampleOutPtr ↦ₘ o0) ** ((sampleOutPtr + (8 : Word)) ↦ₘ o1) **
  ((sampleOutPtr + (16 : Word)) ↦ₘ o2) ** ((sampleOutPtr + (24 : Word)) ↦ₘ o3) **
  exitdivFR

/-- The exit-divide precondition with all five temps and the output cells owned. -/
private def edPre0 : Assertion :=
  edHead (0 : Word) (0 : Word) (0 : Word) (0 : Word) **
  regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  priceOutputOwn sampleOutPtr ** exitdivFR

/-- The exit-divide and tail at `excess = 0` with the five temps and the output
    cells owned (lifted from `round_zero_exitdiv_tail_swapped`), and the
    status-1 exit dropped (its `q4 ||| q5 ≠ 0` pure is false).  The tail is the
    public `tail_core` (Body8Spec), so its exit posts are spelled out and can be
    weakened directly. -/
private theorem round_zero_exitdiv_tail_swapped_owned :
    cpsNBranchWithin 4183 (PriceK + 804) priceCode edPre0
      [(PriceK + 968, edStatus0RawExit)] := by
  have hBase : ∀ (o0 o1 o2 o3 v7 v28 v29 v30 v31 : Word),
      cpsNBranchWithin 4183 (PriceK + 804) priceCode
        (edPre o0 o1 o2 o3 v7 v28 v29 v30 v31)
        [(PriceK + 968, edStatus0RawExit)] := by
    intro o0 o1 o2 o3 v7 v28 v29 v30 v31
    have hSumAlign : (sampleNewSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0 := by decide
    have hOutAlign : sampleOutPtr.toNat % 8 = 0 := by decide
    have hSumRange : (sampleNewSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64 := by decide
    have hOutRange : sampleOutPtr.toNat + 32 < 2 ^ 64 := by decide
    have hSumValid : ∀ i < 32,
        isValidByteAccess ((sampleNewSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true := by
      intro i hi; interval_cases i <;> decide
    have hOutValid : ∀ i < 32, isValidByteAccess (sampleOutPtr + BitVec.ofNat 64 i) = true := by
      intro i hi; interval_cases i <;> decide
    have hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
        (exitdivTailPre sampleNewSp (0 : Word) sampleOutPtr (2 : Word) sampleSaved
          taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
          (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
          taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
          o0 o1 o2 o3 sampleStackB sampleStackA exitdivFR)
        [(PriceK + 968, edStatus0RawExit)] := by
      refine cpsNBranchWithin_weaken_posts
        (tail_core sampleNewSp (0 : Word) sampleOutPtr sampleSaved
          edQ0 edQ1 edQ2 edQ3 edQ4 edQ5 o0 o1 o2 o3
          taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
          (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
          taylorDW edZ0 edZ1 (2 : Word) sampleStackB sampleStackA edQ0 (0 : Word)
          sampleSumX30 (lcnt 5 + signExtend12 (-1 : BitVec 12))
          hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid
          exitdivFR exitdivFR_pcFree) ?_
      intro ex hmem
      simp at hmem
      rcases hmem with h1 | h2
      · subst ex
        refine ⟨(PriceK + 968, edStatus0RawExit), by simp, rfl, ?_⟩
        intro h hq
        obtain ⟨h1, h2, hd, hu, hx10, htail⟩ := hq
        obtain ⟨h3, h4, hd1, hu1, hx5x0, hrest⟩ := htail
        obtain ⟨h5, h6, hd2, hu2, hx5, hx0p⟩ := hx5x0
        obtain ⟨h7, h8, hd3, hu3, hx0, hpure⟩ := hx0p
        exact (hpure.2 edQ4_zero edQ5_zero).elim
      · subst ex
        refine ⟨(PriceK + 968, edStatus0RawExit), by simp, rfl, ?_⟩
        intro h hq
        simp only [edStatus0RawExit] at ⊢
        rw [← tailOutputCells_eq_bytesRegion sampleOutPtr edQ0 edQ1 edQ2 edQ3 o3 o2 o1 o0]
        simp only [tailOutputFullReplaceBE, truncate_zeroExtend_byte,
          EvmAsm.Rv64.AddrNorm.word_add_zero, EvmAsm.Rv64.AddrNorm.se12_0,
          show (signExtend12 (-1 : BitVec 12)) = signExtend12 (4095 : BitVec 12) from by decide,
          show (signExtend12 (-8 : BitVec 12)) = signExtend12 (4088 : BitVec 12) from by decide,
          show (BitVec.ofNat 12 0 : BitVec 12) = 0 by decide,
          show (BitVec.ofNat 12 8 : BitVec 12) = 8 by decide,
          show (BitVec.ofNat 12 16 : BitVec 12) = 16 by decide,
          show (BitVec.ofNat 12 24 : BitVec 12) = 24 by decide,
          show (BitVec.ofNat 12 32 : BitVec 12) = 32 by decide,
          show (BitVec.ofNat 12 40 : BitVec 12) = 40 by decide,
          show (BitVec.ofNat 12 48 : BitVec 12) = 48 by decide,
          show (BitVec.ofNat 12 56 : BitVec 12) = 56 by decide,
          show (BitVec.ofNat 12 64 : BitVec 12) = 64 by decide,
          show (BitVec.ofNat 12 72 : BitVec 12) = 72 by decide,
          show (BitVec.ofNat 12 80 : BitVec 12) = 80 by decide,
          show (BitVec.ofNat 12 88 : BitVec 12) = 88 by decide,
          show (BitVec.ofNat 12 96 : BitVec 12) = 96 by decide,
          show (BitVec.ofNat 12 104 : BitVec 12) = 104 by decide,
          show (BitVec.ofNat 12 112 : BitVec 12) = 112 by decide,
          show (BitVec.ofNat 12 120 : BitVec 12) = 120 by decide,
          show (BitVec.ofNat 12 128 : BitVec 12) = 128 by decide,
          show (BitVec.ofNat 12 136 : BitVec 12) = 136 by decide,
          show (BitVec.ofNat 12 144 : BitVec 12) = 144 by decide,
          show (BitVec.ofNat 12 152 : BitVec 12) = 152 by decide,
          show (BitVec.ofNat 12 160 : BitVec 12) = 160 by decide,
          show (BitVec.ofNat 12 168 : BitVec 12) = 168 by decide,
          show (BitVec.ofNat 12 176 : BitVec 12) = 176 by decide,
          show (BitVec.ofNat 12 184 : BitVec 12) = 184 by decide,
          show (BitVec.ofNat 12 192 : BitVec 12) = 192 by decide,
          show (BitVec.ofNat 12 200 : BitVec 12) = 200 by decide,
          show (BitVec.ofNat 12 208 : BitVec 12) = 208 by decide,
          show (BitVec.ofNat 12 4088 : BitVec 12) = 4088 by decide,
          show (BitVec.ofNat 12 4095 : BitVec 12) = 4095 by decide,
          show (BitVec.ofNat 64 0 : Word) = 0 by decide,
          show (BitVec.ofNat 64 2 : Word) = 2 by decide,
          show (BitVec.ofNat 64 8 : Word) = 8 by decide,
          show (BitVec.ofNat 64 16 : Word) = 16 by decide,
          show (BitVec.ofNat 64 24 : Word) = 24 by decide,
          show (BitVec.ofNat 64 31 : Word) = 31 by decide,
          show (BitVec.ofNat 64 40 : Word) = 40 by decide,
          show (BitVec.ofNat 64 32 : Word) = 32 by decide] at hq ⊢
        obtain ⟨hq0, _hq1⟩ := (sepConj_pure_right h).1 hq
        xperm_hyp hq0
    have hZero := round_zero_exitdiv_tail_swapped
      sampleNewSp (0 : Word) sampleOutPtr (2 : Word) sampleStackB sampleStackA sampleSaved
      (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      taylorDW (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      v7 v28 v29 v30 v31 o0 o1 o2 o3 exitdivFR exitdivFR_pcFree
      (by decide : sampleStackB = sampleNewSp + signExtend12 (112 : BitVec 12))
      (by decide : sampleStackA = sampleNewSp + signExtend12 (64 : BitVec 12))
      (exits := [(PriceK + 968, edStatus0RawExit)]) hTail
    refine cpsNBranchWithin_weaken_pre ?_ hZero
    intro h hp
    rw [show roundAccum (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) = (0 : Word) from by decide]
    simp only [edPre, edHead, roundZero, roundFrame, loopCells, cellsOf_six, exitdivOutputCells,
      EvmAsm.Rv64.AddrNorm.se12_0, EvmAsm.Rv64.AddrNorm.se12_8,
      EvmAsm.Rv64.AddrNorm.se12_16, EvmAsm.Rv64.AddrNorm.se12_24,
      EvmAsm.Rv64.AddrNorm.se12_32, EvmAsm.Rv64.AddrNorm.se12_40,
      EvmAsm.Rv64.AddrNorm.word_add_zero,
      show (BitVec.ofNat 64 0 : Word) = 0 by decide,
      show (BitVec.ofNat 64 8 : Word) = 8 by decide,
      show (BitVec.ofNat 64 16 : Word) = 16 by decide,
      show (BitVec.ofNat 64 24 : Word) = 24 by decide] at hp ⊢
    xperm_hyp hp
  -- lift the five temps and four output cells: the exit list is independent of
  -- all nine values, so one destructuring pass over `edPre0` recovers the nine
  -- concrete values and feeds `hBase`.
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨h3, h4, hd3, hu3, hHd, hO7⟩ := hPP
  obtain ⟨h5, h6, hd5, hu5, hR7, hO28⟩ := hO7
  obtain ⟨v7, hv7⟩ := hR7
  obtain ⟨h7, h8, hd7, hu7, hR28, hO29⟩ := hO28
  obtain ⟨v28, hv28⟩ := hR28
  obtain ⟨h9, h10, hd9, hu9, hR29, hO30⟩ := hO29
  obtain ⟨v29, hv29⟩ := hR29
  obtain ⟨h11, h12, hd11, hu11, hR30, hO31⟩ := hO30
  obtain ⟨v30, hv30⟩ := hR30
  obtain ⟨h13, h14, hd13, hu13, hR31, hOPr⟩ := hO31
  obtain ⟨v31, hv31⟩ := hR31
  obtain ⟨h15, h16, hd15, hu15, hPO, hFr⟩ := hOPr
  obtain ⟨h17, h18, hd17, hu17, hC0, hOwnRest⟩ := hPO
  obtain ⟨v0, hv0⟩ := hC0
  obtain ⟨h19, h20, hd19, hu19, hC1, hOwnRest2⟩ := hOwnRest
  obtain ⟨v1, hv1⟩ := hC1
  obtain ⟨h21, h22, hd21, hu21, hC2, hC3⟩ := hOwnRest2
  obtain ⟨v2, hv2⟩ := hC2
  obtain ⟨v3, hv3⟩ := hC3
  have hPre : edPre v0 v1 v2 v3 v7 v28 v29 v30 v31 h1 := by
    refine ⟨h3, h4, hd3, hu3, hHd, ?_⟩
    refine ⟨h5, h6, hd5, hu5, hv7, ?_⟩
    refine ⟨h7, h8, hd7, hu7, hv28, ?_⟩
    refine ⟨h9, h10, hd9, hu9, hv29, ?_⟩
    refine ⟨h11, h12, hd11, hu11, hv30, ?_⟩
    refine ⟨h13, h14, hd13, hu13, hv31, ?_⟩
    rw [← hu15]
    rw [show ((sampleOutPtr ↦ₘ v0) ** ((sampleOutPtr + 8 ↦ₘ v1) ** ((sampleOutPtr + 16 ↦ₘ v2) ** ((sampleOutPtr + 24 ↦ₘ v3) ** exitdivFR)))) =
        (((sampleOutPtr ↦ₘ v0) ** ((sampleOutPtr + 8 ↦ₘ v1) ** ((sampleOutPtr + 16 ↦ₘ v2) ** (sampleOutPtr + 24 ↦ₘ v3)))) ** exitdivFR) from by
      rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']]
    refine ⟨h15, h16, hd15, rfl, ?cells, hFr⟩
    refine ⟨h17, h18, hd17, hu17, hv0, ?_⟩
    refine ⟨h19, h20, hd19, hu19, hv1, ?_⟩
    exact ⟨h21, h22, hd21, hu21, hv2, hv3⟩
  exact hBase v0 v1 v2 v3 v7 v28 v29 v30 v31 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu, hPre, hRb⟩ hpc
/-! ## The whole body triple and the ABI shell -/

/-- A zero-step triple with the same code request (refl). -/
private theorem cpsTripleWithin_refl_any {addr : Word} {cr : CodeReq} {P Q : Assertion}
    (h : ∀ hp, P hp → Q hp) : cpsTripleWithin 0 addr addr cr P Q := by
  intro R hR s hcr hPR hpc
  exact ⟨0, Nat.le_refl 0, s, stepN_zero, hpc, by
    obtain ⟨hp, hcompat, hpq⟩ := hPR
    exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

private def priceScratchPost : Assertion := empAssertion

/-- The setup post (caller residual absorbed into the round frame) weakens to
    the owned round precondition.  The address normalisation (the eighteen
    `bufCells` offsets to the `sampleStackA`/`sampleStackB`/`sampleStackC` group
    bases) is pushed into the small `roundPreMem_to_cells_eq` helper so the
    final `xperm` sees syntactically matching atoms. -/
private theorem roundPreMem_to_cells_eq (FR : Assertion) :
    roundPreMem FR =
      (frameSlotsSaved priceFrame sampleNewSp sampleSaved **
        (sampleStackA ↦ₘ taylorDW) ** (sampleStackA + (8 : Word) ↦ₘ (0 : Word)) **
        (sampleStackA + (16 : Word) ↦ₘ (0 : Word)) ** (sampleStackA + (24 : Word) ↦ₘ (0 : Word)) **
        (sampleStackA + (32 : Word) ↦ₘ (0 : Word)) ** (sampleStackA + (40 : Word) ↦ₘ (0 : Word)) **
        (sampleStackB ↦ₘ (0 : Word)) ** (sampleStackB + (8 : Word) ↦ₘ (0 : Word)) **
        (sampleStackB + (16 : Word) ↦ₘ (0 : Word)) ** (sampleStackB + (24 : Word) ↦ₘ (0 : Word)) **
        (sampleStackB + (32 : Word) ↦ₘ (0 : Word)) ** (sampleStackB + (40 : Word) ↦ₘ (0 : Word)) **
        (sampleNewSp + signExtend12 (160 : BitVec 12) ↦ₘ (0 : Word)) **
        ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (8 : Word) ↦ₘ (0 : Word)) **
        ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (16 : Word) ↦ₘ (0 : Word)) **
        ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (24 : Word) ↦ₘ (0 : Word)) **
        ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (32 : Word) ↦ₘ (0 : Word)) **
        ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (40 : Word) ↦ₘ (0 : Word)) ** FR) := by
  unfold roundPreMem
  rw [EvmAsm.Rv64.AddrNorm.se12_0, EvmAsm.Rv64.AddrNorm.se12_8, EvmAsm.Rv64.AddrNorm.se12_16,
    EvmAsm.Rv64.AddrNorm.se12_24, EvmAsm.Rv64.AddrNorm.se12_32, EvmAsm.Rv64.AddrNorm.se12_40,
    EvmAsm.Rv64.AddrNorm.word_add_zero]
  simp only [EvmAsm.Rv64.AddrNorm.word_add_zero]

private theorem taylorLoopInv_to_roundPre :
    ∀ h, (setupFrame empAssertion ** taylorLoopInv sampleNewSp (0 : Word) sampleOutPtr (1 : Word)
        sampleSaved
        [(64, taylorDW), (72, 0), (80, 0), (88, 0), (96, 0), (104, 0)]
        [(112, 0), (120, 0), (128, 0), (136, 0), (144, 0), (152, 0)]
        [(160, 0), (168, 0), (176, 0), (184, 0), (192, 0), (200, 0)]) h →
      (roundPreHead ** (temps7 ** roundPreMem (priceOutputOwn sampleOutPtr ** ⌜priceOutputGeometry sampleOutPtr⌝))) h := by
  intro h hp
  unfold setupFrame at hp
  simp only [taylorLoopInv, bufCells] at hp
  rw [show (sampleNewSp + signExtend12 (64 : BitVec 12)) = sampleStackA from by decide,
    show (sampleNewSp + signExtend12 (72 : BitVec 12)) = sampleStackA + (8 : Word) from by decide,
    show (sampleNewSp + signExtend12 (80 : BitVec 12)) = sampleStackA + (16 : Word) from by decide,
    show (sampleNewSp + signExtend12 (88 : BitVec 12)) = sampleStackA + (24 : Word) from by decide,
    show (sampleNewSp + signExtend12 (96 : BitVec 12)) = sampleStackA + (32 : Word) from by decide,
    show (sampleNewSp + signExtend12 (104 : BitVec 12)) = sampleStackA + (40 : Word) from by decide,
    show (sampleNewSp + signExtend12 (112 : BitVec 12)) = sampleStackB from by decide,
    show (sampleNewSp + signExtend12 (120 : BitVec 12)) = sampleStackB + (8 : Word) from by decide,
    show (sampleNewSp + signExtend12 (128 : BitVec 12)) = sampleStackB + (16 : Word) from by decide,
    show (sampleNewSp + signExtend12 (136 : BitVec 12)) = sampleStackB + (24 : Word) from by decide,
    show (sampleNewSp + signExtend12 (144 : BitVec 12)) = sampleStackB + (32 : Word) from by decide,
    show (sampleNewSp + signExtend12 (152 : BitVec 12)) = sampleStackB + (40 : Word) from by decide,
    show (sampleNewSp + signExtend12 (168 : BitVec 12)) =
        (sampleNewSp + signExtend12 (160 : BitVec 12)) + (8 : Word) from by decide,
    show (sampleNewSp + signExtend12 (176 : BitVec 12)) =
        (sampleNewSp + signExtend12 (160 : BitVec 12)) + (16 : Word) from by decide,
    show (sampleNewSp + signExtend12 (184 : BitVec 12)) =
        (sampleNewSp + signExtend12 (160 : BitVec 12)) + (24 : Word) from by decide,
    show (sampleNewSp + signExtend12 (192 : BitVec 12)) =
        (sampleNewSp + signExtend12 (160 : BitVec 12)) + (32 : Word) from by decide,
    show (sampleNewSp + signExtend12 (200 : BitVec 12)) =
        (sampleNewSp + signExtend12 (160 : BitVec 12)) + (40 : Word) from by decide] at hp
  simp only [sepConj_emp_right', sepConj_emp_left'] at hp
  rw [roundPreMem_to_cells_eq] at ⊢
  unfold roundPreHead temps7 at ⊢
  xperm_hyp hp

/-- The body entry (plus the architectural `x0` rider) weakens to the setup
    precondition. -/
private theorem priceBodyPre_to_setupPre :
    ∀ h, ((.x0 ↦ᵣ (0 : Word)) ** priceBodyPre sampleNewSp sampleSaved (0 : Word) sampleOutPtr priceScratch) h →
      (setupFrame empAssertion ** setupBase ** priceWorkspaceOwn sampleNewSp) h := by
  intro h hp
  unfold priceBodyPre at hp
  simp only [setupFrame, setupBase, priceScratch, priceFrame,
    regsAt_cons, regsAt_nil, regOwns_cons, regOwns_nil,
    sepConj_emp_right', sepConj_emp_left', sepConj_assoc', sepConj_comm'] at hp ⊢
  xperm_hyp hp

/-- The QBACK post at `excess = 0` reaches the parity-1 or-chain precondition
    (zero steps). -/
private theorem qback_to_orPre (FR0 : Assertion) (_hFR0 : FR0.pcFree) :
    cpsTripleWithin 0 (PriceK + 144) (PriceK + 144) priceCode
      (roundQBACKPost (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR0)
      (orPre FR0) := by
  refine cpsTripleWithin_refl_any ?_
  intro h hp
  have hpar := roundQBACKPost_to_parity1 FR0 h hp
  simp only [orPre, orMem, loopCells, parity1, taylorLoopInvParityAt, cellsOf_six, sepConj_emp_right',
    show parityBuffer 1 sampleStackA sampleStackB = sampleStackB from by decide,
    show parityBuffer 1 sampleStackB sampleStackA = sampleStackA from by decide] at hpar ⊢
  xperm_hyp hpar

/-- The or-chain post at `excess = 0` branches: `beqz` fires (acc = 0) to the
    exit-divide precondition `edPre0`, and the not-taken post is absurd. -/
private theorem orPost_beqz :
    cpsBranchWithin 1 (PriceK + 196) priceCode
      (orPost (priceOutputOwn sampleOutPtr ** ⌜priceOutputGeometry sampleOutPtr⌝))
      (PriceK + 804) edPre0 (PriceK + 200) ⌜False⌝ := by
  let FR0 : Assertion := priceOutputOwn sampleOutPtr ** ⌜priceOutputGeometry sampleOutPtr⌝
  have hfr0 : FR0.pcFree := by unfold FR0 priceOutputOwn; pcf
  have hbr := cpsBranchWithin_frameR
    (loopFrame ** ((.x6 ↦ᵣ (0 : Word)) **
      (regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
      orMem FR0))
    (by unfold loopFrame orMem; pcf)
    (AmsterdamBlobGasPriceBody11Spec.loop_test_beqz_branch 0)
  have hw := cpsBranchWithin_weaken (P' := orPost FR0) (Q_t' := edPre0) (Q_f' := ⌜False⌝)
    (by intro h hp
        simp only [orPost, loopFrame, orMem, FR0, priceOutputOwn, sepConj_emp_right'] at hp ⊢
        xperm_hyp hp)
    (by intro h hp
        simp only [edPre0, edHead, loopFrame, orMem, loopCells, FR0, priceOutputOwn, cellsOf_six,
          EvmAsm.Rv64.AddrNorm.se12_0, EvmAsm.Rv64.AddrNorm.se12_8,
          EvmAsm.Rv64.AddrNorm.se12_16, EvmAsm.Rv64.AddrNorm.se12_24,
          EvmAsm.Rv64.AddrNorm.se12_32, EvmAsm.Rv64.AddrNorm.se12_40,
          EvmAsm.Rv64.AddrNorm.word_add_zero, sepConj_emp_right'] at hp ⊢
        xperm_hyp hp)
    (by intro h hp
        obtain ⟨h1, h2, hd, hu, hx5x0, hrest⟩ := hp
        obtain ⟨h3, h4, hd1, hu1, hx5, hx0p⟩ := hx5x0
        obtain ⟨h5, h6, hd2, hu2, hx0, hpure⟩ := hx0p
        exact (hpure.2 rfl).elim)
    hbr
  simpa [FR0] using hw

/-! ### x0-freedom for the body precondition -/

private theorem x0Free_sepConj {P Q : Assertion}
    (hP : x0FreeAssertion P) (hQ : x0FreeAssertion Q) : x0FreeAssertion (P ** Q) := by
  intro h hh
  obtain ⟨h1, h2, hd, hu, hp, hq⟩ := hh
  have h1x := hP h1 hp
  have h2x := hQ h2 hq
  rw [← hu]
  simp [PartialState.union, h1x, h2x]

private theorem x0Free_regIs {r : Reg} {v : Word} (hr : r ≠ .x0) : x0FreeAssertion (r ↦ᵣ v) := by
  intro h hh
  rw [hh]
  simp [PartialState.singletonReg, Ne.symm hr]

private theorem x0Free_regOwns {rs : List Reg} (hrs : ∀ r ∈ rs, r ≠ .x0) : x0FreeAssertion (regOwns rs) := by
  induction rs with
  | nil => intro h hh; rw [hh]; rfl
  | cons r rs ih =>
      have hr : r ≠ .x0 := hrs r (by simp)
      have hOwn : x0FreeAssertion (regOwn r) := by
        intro h hh
        obtain ⟨v, hv⟩ := hh
        exact x0Free_regIs hr h hv
      have ih' : x0FreeAssertion (regOwns rs) := ih (fun r' hr' => hrs r' (by simp [hr']))
      simpa only [regOwns_cons] using x0Free_sepConj hOwn ih'

private theorem x0Free_memIs {a v : Word} : x0FreeAssertion (a ↦ₘ v) := by
  intro h hh
  rw [hh.1]
  rfl

private theorem x0Free_pure {P : Prop} : x0FreeAssertion (⌜P⌝) := by
  intro h hh
  rw [hh.1]
  rfl

private theorem x0Free_frameSlotsSaved (frame : FrameDesc) (newSp : Word) (vals : Reg → Word) :
    x0FreeAssertion (frameSlotsSaved frame newSp vals) := by
  induction frame with
  | nil => intro h hh; rw [hh]; rfl
  | cons p rest ih => simpa only [frameSlotsSaved_cons] using x0Free_sepConj x0Free_memIs ih

private theorem x0Free_regOwn (r : Reg) (hr : r ≠ .x0) : x0FreeAssertion (regOwn r) := by
  intro h hh
  obtain ⟨v, hv⟩ := hh
  exact x0Free_regIs hr h hv

private theorem x0Free_emp : x0FreeAssertion empAssertion := by
  intro h hh
  rw [hh]
  rfl

private theorem x0Free_memOwn (a : Word) : x0FreeAssertion (memOwn a) := by
  intro h hh
  obtain ⟨v, hv⟩ := hh
  exact x0Free_memIs h hv

private theorem x0Free_priceWorkspaceOwn (newSp : Word) : x0FreeAssertion (priceWorkspaceOwn newSp) := by
  unfold priceWorkspaceOwn
  repeat' first
    | apply x0Free_sepConj
    | exact x0Free_memOwn _

private theorem x0Free_priceOutputOwn (outPtr : Word) : x0FreeAssertion (priceOutputOwn outPtr) := by
  unfold priceOutputOwn
  repeat' first
    | apply x0Free_sepConj
    | exact x0Free_memOwn _

private theorem priceBodyPre_x0Free :
    x0FreeAssertion (priceBodyPre sampleNewSp sampleSaved (0 : Word) sampleOutPtr priceScratch) := by
  unfold priceBodyPre priceScratch
  repeat' first
    | apply x0Free_sepConj
    | exact x0Free_regIs (by decide)
    | exact x0Free_regOwn _ (by decide)
    | exact x0Free_memIs
    | exact x0Free_memOwn _
    | exact x0Free_pure
    | exact x0Free_emp

/-- The status-0 tail post weakens to `priceBodyPost` (temps and workspace
    cells to ownership, output bytes folded to the model encoding, the output
    geometry pure dropped). -/
private theorem hid_assert {A : Assertion} : ∀ _h, A _h → A _h := fun _h hp => hp

private theorem pure_drop_geo : ∀ _h, ⌜priceOutputGeometry sampleOutPtr⌝ _h → empAssertion _h := fun _h hp => hp.1

private theorem edStatus0Raw_to_bodyPost :
    ∀ h, edStatus0RawExit h →
      (priceBodyPost sampleNewSp sampleSaved bodyVals (0 : Word) sampleOutPtr (natToBeBytes 32 1)
        priceScratchPost ** (.x0 ↦ᵣ (0 : Word))) h := by
  intro h hp
  simp only [edStatus0RawExit, exitdivFR] at hp
  rw [edTailBytes_eq] at hp
  obtain ⟨h1a, h1b, hd1, hu1, h1val, hrest1⟩ := hp
  obtain ⟨h2a, h2b, hd2, hu2, h2val, hrest2⟩ := hrest1
  obtain ⟨h3a, h3b, hd3, hu3, h3val, hrest3⟩ := hrest2
  obtain ⟨h4a, h4b, hd4, hu4, h4val, hrest4⟩ := hrest3
  obtain ⟨h5a, h5b, hd5, hu5, h5val, hrest5⟩ := hrest4
  obtain ⟨h6a, h6b, hd6, hu6, h6val, hrest6⟩ := hrest5
  obtain ⟨h7a, h7b, hd7, hu7, h7val, hrest7⟩ := hrest6
  obtain ⟨h8a, h8b, hd8, hu8, h8val, hrest8⟩ := hrest7
  obtain ⟨h9a, h9b, hd9, hu9, h9val, hrest9⟩ := hrest8
  obtain ⟨h10a, h10b, hd10, hu10, h10val, hrest10⟩ := hrest9
  obtain ⟨h11a, h11b, hd11, hu11, h11val, hrest11⟩ := hrest10
  obtain ⟨h12a, h12b, hd12, hu12, h12val, hrest12⟩ := hrest11
  obtain ⟨h13a, h13b, hd13, hu13, h13val, hrest13⟩ := hrest12
  obtain ⟨h14a, h14b, hd14, hu14, h14val, hrest14⟩ := hrest13
  obtain ⟨h15a, h15b, hd15, hu15, h15val, hrest15⟩ := hrest14
  obtain ⟨h16a, h16b, hd16, hu16, h16val, hrest16⟩ := hrest15
  obtain ⟨h17a, h17b, hd17, hu17, h17val, hrest17⟩ := hrest16
  obtain ⟨h18a, h18b, hd18, hu18, h18val, hrest18⟩ := hrest17
  obtain ⟨h19a, h19b, hd19, hu19, h19val, hrest19⟩ := hrest18
  obtain ⟨h20a, h20b, hd20, hu20, h20val, hrest20⟩ := hrest19
  obtain ⟨h21a, h21b, hd21, hu21, h21val, hrest21⟩ := hrest20
  obtain ⟨h22a, h22b, hd22, hu22, h22val, hrest22⟩ := hrest21
  obtain ⟨h23a, h23b, hd23, hu23, h23val, hrest23⟩ := hrest22
  obtain ⟨h24a, h24b, hd24, hu24, h24val, hrest24⟩ := hrest23
  obtain ⟨h25a, h25b, hd25, hu25, h25val, hrest25⟩ := hrest24
  obtain ⟨h26a, h26b, hd26, hu26, h26val, hrest26⟩ := hrest25
  obtain ⟨h27a, h27b, hd27, hu27, h27val, hrest27⟩ := hrest26
  obtain ⟨h28a, h28b, hd28, hu28, h28val, hrest28⟩ := hrest27
  obtain ⟨h29a, h29b, hd29, hu29, h29val, hrest29⟩ := hrest28
  obtain ⟨h30a, h30b, hd30, hu30, h30val, hrest30⟩ := hrest29
  obtain ⟨h31a, h31b, hd31, hu31, h31val, hrest31⟩ := hrest30
  obtain ⟨h32a, h32b, hd32, hu32, h32val, hrest32⟩ := hrest31
  obtain ⟨h33a, h33b, hd33, hu33, h33val, hrest33⟩ := hrest32
  obtain ⟨h34a, h34b, hd34, hu34, h34val, hrest34⟩ := hrest33
  obtain ⟨h35a, h35b, hd35, hu35, h35val, hrest35⟩ := hrest34
  obtain ⟨h36a, h36b, hd36, hu36, h36val, hrest36⟩ := hrest35
  obtain ⟨h37a, h37b, hd37, hu37, h37val, hrest37⟩ := hrest36
  obtain ⟨h38a, h38b, hd38, hu38, h38val, hrest38⟩ := hrest37
  obtain ⟨h39a, h39b, hd39, hu39, h39val, hrest39⟩ := hrest38
  have hw : ((.x10 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ sampleOutPtr) ** (.x22 ↦ᵣ (sampleNewSp + signExtend12 (160 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) ** bytesRegion sampleOutPtr (natToBeBytes 32 1) ** (.x2 ↦ᵣ sampleNewSp) ** (.x1 ↦ᵣ (sampleSaved .x1)) ** (.x11 ↦ᵣ sampleOutPtr) ** (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ taylorDW) ** (.x18 ↦ᵣ (2 : Word)) ** (.x19 ↦ᵣ sampleStackB) ** (.x20 ↦ᵣ sampleStackA) ** regOwn .x31 ** regOwn .x5 ** regOwn .x6 ** frameSlotsSaved priceFrame sampleNewSp sampleSaved ** memOwn (sampleNewSp + signExtend12 (64 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (72 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (80 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (88 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (96 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (104 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (112 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (120 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (128 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (136 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (144 : BitVec 12)) ** memOwn (sampleNewSp + signExtend12 (152 : BitVec 12)) ** memOwn ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (8 : Word)) ** memOwn ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (16 : Word)) ** memOwn ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (24 : Word)) ** memOwn ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (32 : Word)) ** memOwn ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (40 : Word))) h := by
    refine ⟨h1a, h1b, hd1, hu1, h1val, ?_⟩
    refine ⟨h2a, h2b, hd2, hu2, h2val, ?_⟩
    refine ⟨h3a, h3b, hd3, hu3, h3val, ?_⟩
    refine ⟨h4a, h4b, hd4, hu4, h4val, ?_⟩
    have hw5 : regOwn .x7 h5a := ⟨BitVec.setWidth 64 (extractByte edQ0 0), h5val⟩
    refine ⟨h5a, h5b, hd5, hu5, hw5, ?_⟩
    have hw6 : regOwn .x28 h6a := ⟨(sampleOutPtr + 31), h6val⟩
    refine ⟨h6a, h6b, hd6, hu6, hw6, ?_⟩
    have hw7 : regOwn .x29 h7a := ⟨(32 : Word), h7val⟩
    refine ⟨h7a, h7b, hd7, hu7, hw7, ?_⟩
    have hw8 : regOwn .x30 h8a := ⟨(32 : Word), h8val⟩
    refine ⟨h8a, h8b, hd8, hu8, hw8, ?_⟩
    have hw9 : memOwn (sampleNewSp + signExtend12 (160 : BitVec 12)) h9a := ⟨edQ0, h9val⟩
    refine ⟨h9a, h9b, hd9, hu9, hw9, ?_⟩
    refine ⟨h10a, h10b, hd10, hu10, h10val, ?_⟩
    refine ⟨h11a, h11b, hd11, hu11, h11val, ?_⟩
    refine ⟨h12a, h12b, hd12, hu12, h12val, ?_⟩
    refine ⟨h13a, h13b, hd13, hu13, h13val, ?_⟩
    refine ⟨h14a, h14b, hd14, hu14, h14val, ?_⟩
    refine ⟨h15a, h15b, hd15, hu15, h15val, ?_⟩
    refine ⟨h16a, h16b, hd16, hu16, h16val, ?_⟩
    refine ⟨h17a, h17b, hd17, hu17, h17val, ?_⟩
    refine ⟨h18a, h18b, hd18, hu18, h18val, ?_⟩
    have hw19 : regOwn .x31 h19a := ⟨(lcnt 5 + signExtend12 (-1 : BitVec 12)), h19val⟩
    refine ⟨h19a, h19b, hd19, hu19, hw19, ?_⟩
    have hw20 : regOwn .x5 h20a := ⟨(edQ4 ||| edQ5), h20val⟩
    refine ⟨h20a, h20b, hd20, hu20, hw20, ?_⟩
    have hw21 : regOwn .x6 h21a := ⟨edQ5, h21val⟩
    refine ⟨h21a, h21b, hd21, hu21, hw21, ?_⟩
    refine ⟨h22a, h22b, hd22, hu22, h22val, ?_⟩
    have hw23 : memOwn (sampleNewSp + signExtend12 (64 : BitVec 12)) h23a := ⟨taylorDW, h23val⟩
    refine ⟨h23a, h23b, hd23, hu23, hw23, ?_⟩
    have hw24 : memOwn (sampleNewSp + signExtend12 (72 : BitVec 12)) h24a := ⟨(0 : Word), h24val⟩
    refine ⟨h24a, h24b, hd24, hu24, hw24, ?_⟩
    have hw25 : memOwn (sampleNewSp + signExtend12 (80 : BitVec 12)) h25a := ⟨(0 : Word), h25val⟩
    refine ⟨h25a, h25b, hd25, hu25, hw25, ?_⟩
    have hw26 : memOwn (sampleNewSp + signExtend12 (88 : BitVec 12)) h26a := ⟨(0 : Word), h26val⟩
    refine ⟨h26a, h26b, hd26, hu26, hw26, ?_⟩
    have hw27 : memOwn (sampleNewSp + signExtend12 (96 : BitVec 12)) h27a := ⟨(0 : Word), h27val⟩
    refine ⟨h27a, h27b, hd27, hu27, hw27, ?_⟩
    have hw28 : memOwn (sampleNewSp + signExtend12 (104 : BitVec 12)) h28a := ⟨(0 : Word), h28val⟩
    refine ⟨h28a, h28b, hd28, hu28, hw28, ?_⟩
    have hw29 : memOwn (sampleNewSp + signExtend12 (112 : BitVec 12)) h29a := ⟨(0 : Word), h29val⟩
    refine ⟨h29a, h29b, hd29, hu29, hw29, ?_⟩
    have hw30 : memOwn (sampleNewSp + signExtend12 (120 : BitVec 12)) h30a := ⟨(0 : Word), h30val⟩
    refine ⟨h30a, h30b, hd30, hu30, hw30, ?_⟩
    have hw31 : memOwn (sampleNewSp + signExtend12 (128 : BitVec 12)) h31a := ⟨(0 : Word), h31val⟩
    refine ⟨h31a, h31b, hd31, hu31, hw31, ?_⟩
    have hw32 : memOwn (sampleNewSp + signExtend12 (136 : BitVec 12)) h32a := ⟨(0 : Word), h32val⟩
    refine ⟨h32a, h32b, hd32, hu32, hw32, ?_⟩
    have hw33 : memOwn (sampleNewSp + signExtend12 (144 : BitVec 12)) h33a := ⟨(0 : Word), h33val⟩
    refine ⟨h33a, h33b, hd33, hu33, hw33, ?_⟩
    have hw34 : memOwn (sampleNewSp + signExtend12 (152 : BitVec 12)) h34a := ⟨(0 : Word), h34val⟩
    refine ⟨h34a, h34b, hd34, hu34, hw34, ?_⟩
    have hw35 : memOwn ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (8 : Word)) h35a := ⟨edQ1, h35val⟩
    refine ⟨h35a, h35b, hd35, hu35, hw35, ?_⟩
    have hw36 : memOwn ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (16 : Word)) h36a := ⟨edQ2, h36val⟩
    refine ⟨h36a, h36b, hd36, hu36, hw36, ?_⟩
    have hw37 : memOwn ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (24 : Word)) h37a := ⟨edQ3, h37val⟩
    refine ⟨h37a, h37b, hd37, hu37, hw37, ?_⟩
    have hw38 : memOwn ((sampleNewSp + signExtend12 (160 : BitVec 12)) + (32 : Word)) h38a := ⟨edQ4, h38val⟩
    refine ⟨h38a, h38b, hd38, hu38, hw38, ?_⟩
    have h39b_empty : h39b = PartialState.empty := by obtain ⟨he, _⟩ := hrest39; exact he
    have h_un : h39a.union h39b = h39a := by rw [h39b_empty]; exact PartialState.union_empty_right
    rw [← hu39, h_un]
    exact ⟨edQ5, h39val⟩
  unfold priceBodyPost priceScratchPost
  rw [show (sampleNewSp + signExtend12 (160 : BitVec 12)) + (8 : Word) = sampleNewSp + signExtend12 (168 : BitVec 12) from by decide,
    show (sampleNewSp + signExtend12 (160 : BitVec 12)) + (16 : Word) = sampleNewSp + signExtend12 (176 : BitVec 12) from by decide,
    show (sampleNewSp + signExtend12 (160 : BitVec 12)) + (24 : Word) = sampleNewSp + signExtend12 (184 : BitVec 12) from by decide,
    show (sampleNewSp + signExtend12 (160 : BitVec 12)) + (32 : Word) = sampleNewSp + signExtend12 (192 : BitVec 12) from by decide,
    show (sampleNewSp + signExtend12 (160 : BitVec 12)) + (40 : Word) = sampleNewSp + signExtend12 (200 : BitVec 12) from by decide] at hw
  simp only [priceFrame, regsAt_cons, regsAt_nil, regOwns_cons, regOwns_nil, sepConj_emp_right']
  simp only [regOwns, priceWorkspaceOwn, regsAt, priceFrame, bodyVals, sepConj_emp_right',
    show priceOutputPost (0 : Word) sampleOutPtr (natToBeBytes 32 1) =
      bytesRegion sampleOutPtr (natToBeBytes 32 1) from by unfold priceOutputPost; rfl] at hw ⊢
  xperm_hyp hw

/-- `priceBody_excess0_single_exit`: the 8252-step single-exit body triple at
    `excess = 0` (setup 27 + round 4028 + second loop-head pass 14 + exit-divide
    and tail 4183).  The model output is `natToBeBytes 32 1`. -/
private theorem priceBody_excess0_single_exit :
    cpsTripleWithin 8252 (PriceK + 36) (PriceK + 968) priceCode
      (priceBodyPre (sampleSp0 + signExtend12 (-208 : BitVec 12)) sampleSaved (0 : Word) sampleOutPtr priceScratch)
      (priceBodyPost (sampleSp0 + signExtend12 (-208 : BitVec 12)) sampleSaved bodyVals (0 : Word)
        sampleOutPtr (natToBeBytes 32 1) priceScratchPost) := by
  let FR0 : Assertion := priceOutputOwn sampleOutPtr ** ⌜priceOutputGeometry sampleOutPtr⌝
  have hfr : FR0.pcFree := by
    unfold FR0 priceOutputOwn
    pcf
  have hSetup := price_setup_spec_owned empAssertion pcFree_emp
  have hRound := taylor_round_excess0_qback_owned FR0 hfr
  have hSetupRound : cpsNBranchWithin (27 + 4028) (PriceK + 36) priceCode
      (setupFrame empAssertion ** setupBase ** priceWorkspaceOwn sampleNewSp)
      [(PriceK + 144, roundQBACKPost (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR0)] := by
    exact cpsTripleWithin_seq_cpsNBranchWithin_perm_same_cr taylorLoopInv_to_roundPre hSetup hRound
  have hAfter : cpsNBranchWithin (13 + 1 + 4183) (PriceK + 144) priceCode
      (roundQBACKPost (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR0)
      [(PriceK + 968, edStatus0RawExit)] := by
    have h0 := qback_to_orPre FR0 hfr
    have hOr := or_chainP2_owned FR0 hfr
    have h0Or : cpsTripleWithin 13 (PriceK + 144) (PriceK + 196) priceCode
        (roundQBACKPost (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR0)
        (orPost (priceOutputOwn sampleOutPtr ** ⌜priceOutputGeometry sampleOutPtr⌝)) := by
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => hp) ?_
      simpa [FR0] using (cpsTripleWithin_seq_same_cr h0 hOr)
    have hbr := orPost_beqz
    have hbrN : cpsNBranchWithin 14 (PriceK + 144) priceCode
        (roundQBACKPost (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR0)
        [(PriceK + 804, edPre0), (PriceK + 200, ⌜False⌝)] := by
      exact cpsTripleWithin_seq_cpsNBranchWithin_same_cr h0Or
        (cpsNBranchWithin_of_branch_mem (by simp) (by simp) hbr)
    have hBrExit : cpsNBranchWithin (14 + 4183) (PriceK + 144) priceCode
        (roundQBACKPost (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) FR0)
        [(PriceK + 968, edStatus0RawExit), (PriceK + 200, ⌜False⌝)] := by
      exact nb_extend_head_same_cr hbrN round_zero_exitdiv_tail_swapped_owned
    exact cpsNBranchWithin_drop_absurd_exit (pre := [(PriceK + 968, edStatus0RawExit)]) (post := [])
      (fun h hq => hq.2) hBrExit
  have hAll : cpsNBranchWithin (27 + 4028 + (13 + 1 + 4183)) (PriceK + 36) priceCode
      (setupFrame empAssertion ** setupBase ** priceWorkspaceOwn sampleNewSp)
      [(PriceK + 968, edStatus0RawExit)] := by
    exact nb_extend_head_same_cr hSetupRound hAfter
  have hAll' : cpsNBranchWithin 8252 (PriceK + 36) priceCode
      (priceBodyPre sampleNewSp sampleSaved (0 : Word) sampleOutPtr priceScratch ** (.x0 ↦ᵣ (0 : Word)))
      [(PriceK + 968, edStatus0RawExit)] := by
    refine cpsNBranchWithin_weaken_pre ?_ hAll
    intro h hp
    have hp' : ((.x0 ↦ᵣ (0 : Word)) ** priceBodyPre sampleNewSp sampleSaved (0 : Word) sampleOutPtr priceScratch) h := by
      simpa only [sepConj_comm'] using hp
    exact priceBodyPre_to_setupPre h hp'
  have hFinal : cpsNBranchWithin 8252 (PriceK + 36) priceCode
      (priceBodyPre sampleNewSp sampleSaved (0 : Word) sampleOutPtr priceScratch ** (.x0 ↦ᵣ (0 : Word)))
      [(PriceK + 968, priceBodyPost sampleNewSp sampleSaved bodyVals (0 : Word) sampleOutPtr (natToBeBytes 32 1) priceScratchPost ** (.x0 ↦ᵣ (0 : Word)))] := by
    refine cpsNBranchWithin_weaken_posts hAll' ?_
    intro ex hmem
    simp at hmem
    subst ex
    refine ⟨(PriceK + 968, priceBodyPost sampleNewSp sampleSaved bodyVals (0 : Word) sampleOutPtr (natToBeBytes 32 1) priceScratchPost ** (.x0 ↦ᵣ (0 : Word))), by simp, rfl, ?_⟩
    intro h hp
    exact edStatus0Raw_to_bodyPost h hp
  have hDrop := cpsNBranchWithin_drop_x0 (nSteps := 8252) (entry := PriceK + 36) (cr := priceCode)
    (P := priceBodyPre sampleNewSp sampleSaved (0 : Word) sampleOutPtr priceScratch)
    (exits := [(PriceK + 968, priceBodyPost sampleNewSp sampleSaved bodyVals (0 : Word) sampleOutPtr (natToBeBytes 32 1) priceScratchPost)])
    priceBodyPre_x0Free hFinal
  exact cpsNBranchWithin_as_cpsTripleWithin hDrop

/-- The ABI shell lifts the 8252-step body triple to the whole routine
    (`8271 = 1 + 8 + 8252 + 8 + 1 + 1`). -/
private theorem priceAbi_lift :
    cpsTripleWithin 8271 PriceK sampleRet priceCode
      (priceEntryRest sampleSp0 sampleRet sampleSaved (0 : Word) sampleOutPtr priceScratch)
      (priceCalleePost sampleSp0 sampleRet sampleSaved (0 : Word) sampleOutPtr (natToBeBytes 32 1) priceScratchPost) := by
  have hAbi := amsterdam_blob_gas_price_abi_from_body
    (cr := priceCode) (bodySteps := 8252)
    sampleSp0 sampleRet sampleSaved bodyVals
    (0 : Word) sampleOutPtr (0 : Word) (natToBeBytes 32 1)
    priceScratch priceScratchPost empAssertion
    (hret := by rfl)
    (hretAlign := by decide)
    (hscratch := by unfold priceScratch; exact pcFree_emp)
    (hscratchPost := by unfold priceScratchPost; exact pcFree_emp)
    (hF := pcFree_emp)
    (hsub := priceCode_sub_abiFrameProg)
    (hbody := priceBody_excess0_single_exit)
  simpa [priceFrame, sepConj_emp_right', sepConj_emp_left'] using hAbi

/-- `priceContract` at `excess = 0` is inhabited: the whole routine reaches the
    status-0 exit (`x10 = 0`, output `natToBeBytes 32 1`) in 8271 steps.  This
    covers only the `excess = 0` input; `excess ≠ 0` inputs (the general
    495-round fold) are NOT covered here. -/
theorem priceContract_ex0_inhabited :
    priceContract 8271 sampleSp0 sampleRet sampleSaved (0 : Word) sampleOutPtr
      (natToBeBytes 32 1) priceScratch := by
  unfold priceContract
  refine cpsNBranchWithin_of_triple ?_ priceAbi_lift
  simp [priceScratch, priceScratchPost, priceCalleePost]

/-- `taylorPriceContract` at `excess = 0` is inhabited: the whole routine reaches
    the model-determined status-0 exit (`x10 = 0`, output `natToBeBytes 32 1`) in
    8271 steps.  This covers only the `excess = 0` input; `excess ≠ 0` inputs (the
    general 495-round fold) are NOT covered here.  A non-vacuity witness for one
    input value, NOT a discharge of the contract. -/
theorem taylor_price_contract_excess0_inhabited :
    taylorPriceContract 8271 sampleSp0 sampleRet sampleSaved (0 : Word) sampleOutPtr
      priceScratch := by
  unfold taylorPriceContract
  rw [show priceOutcome (0 : Word).toNat = (0, natToBeBytes 32 1) from by
    change priceOutcome 0 = (0, natToBeBytes 32 1)
    simp [priceOutcome, taylor_price_outcome_zero]]
  change cpsTripleWithin 8271 PriceK sampleRet priceCode
    (priceEntryRest sampleSp0 sampleRet sampleSaved (0 : Word) sampleOutPtr priceScratch)
    (priceCalleePost sampleSp0 sampleRet sampleSaved (0 : Word) sampleOutPtr
      (natToBeBytes 32 1) priceScratchPost)
  exact priceAbi_lift

#print axioms priceContract_ex0_inhabited
#print axioms taylor_price_contract_excess0_inhabited

#print axioms taylor_round_excess0_qback_owned
#print axioms price_setup_spec_owned
#print axioms roundQBACKPost_to_parity1
#print axioms taylor_round_quotient_excess0

end EvmAsm.Codegen.AmsterdamBlobGasPricePriceContractWitness
