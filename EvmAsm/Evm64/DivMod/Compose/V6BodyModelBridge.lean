/-
  EvmAsm.Evm64.DivMod.Compose.V6BodyModelBridge

  Connects the v6 fast-path body's *concrete* normalized window
  (`v6nU{4,3,2,1,0}` / `v6nD`, the `normAFullPost` shift/antiShift limb
  expressions produced by CLZ + normA) to the division model's normalized
  components (`fullDivN1NormU` / `fullDivN1NormV`).  The identification is
  definitional — `fullDivN1Shift b0 = (clzResult b0).1`,
  `fullDivN1AntiShift b0 = signExtend12 0 - … = 0 - (clzResult b0).1` — so each
  window limb unfolds to the matching `NormU`/`NormV` projection.

  Composing these with the digit chain bridge (`v6chainQ_j_eq_model`,
  `V6ChainModelBridge`) gives the body-window quotient digits directly as the v5
  model digits `fullDivN1R_jV5.1` — the form `fullDivN1QuotientWordV5_eq_div_of_shape`
  assembles into `EvmWord.div a b`.  Bead `evm-asm-dr466.2`.
-/

import EvmAsm.Evm64.DivMod.Compose.BodyV6
import EvmAsm.Evm64.DivMod.Compose.V6ChainModelBridge
import EvmAsm.Evm64.DivMod.Spec.N1V5Quotient

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Window-bridge equalities: body normalized limb = model `NormU`/`NormV` proj.
-- ============================================================================

theorem v6nU4_eq_normU (a0 a1 a2 a3 b0 : Word) :
    v6nU4 a3 b0 = (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 := by
  unfold v6nU4 fullDivN1NormU fullDivN1AntiShift fullDivN1Shift
  simp only [AddrNorm.se12_0]

theorem v6nU3_eq_normU (a0 a1 a2 a3 b0 : Word) :
    v6nU3 a3 a2 b0 = (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 := by
  unfold v6nU3 fullDivN1NormU fullDivN1AntiShift fullDivN1Shift
  simp only [AddrNorm.se12_0]

theorem v6nU2_eq_normU (a0 a1 a2 a3 b0 : Word) :
    v6nU2 a2 a1 b0 = (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 := by
  unfold v6nU2 fullDivN1NormU fullDivN1AntiShift fullDivN1Shift
  simp only [AddrNorm.se12_0]

theorem v6nU1_eq_normU (a0 a1 a2 a3 b0 : Word) :
    v6nU1 a1 a0 b0 = (fullDivN1NormU a0 a1 a2 a3 b0).2.1 := by
  unfold v6nU1 fullDivN1NormU fullDivN1AntiShift fullDivN1Shift
  simp only [AddrNorm.se12_0]

theorem v6nU0_eq_normU (a0 a1 a2 a3 b0 : Word) :
    v6nU0 a0 b0 = (fullDivN1NormU a0 a1 a2 a3 b0).1 := by
  unfold v6nU0 fullDivN1NormU fullDivN1Shift; rfl

theorem v6nD_eq_normV (b0 b1 b2 b3 : Word) :
    v6nD b0 = (fullDivN1NormV b0 b1 b2 b3).1 := by
  unfold v6nD fullDivN1NormV fullDivN1Shift; rfl

-- ============================================================================
-- Body-window quotient digits = v5 model digits.
-- ============================================================================

variable (a0 a1 a2 a3 b0 b1 b2 b3 : Word)

/-- Body window top digit `q[3]` = v5 model top quotient digit. -/
theorem v6chainQ3_v6n_eq_model
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    v6chainQ3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0) =
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  rw [v6nU4_eq_normU a0, v6nU3_eq_normU a0,
      v6nD_eq_normV (b1 := b1) (b2 := b2) (b3 := b3),
      v6chainQ3_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz]

/-- Body window digit `q[2]` = v5 model quotient digit 2. -/
theorem v6chainQ2_v6n_eq_model
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    v6chainQ2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0) =
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  rw [v6nU4_eq_normU a0, v6nU3_eq_normU a0, v6nU2_eq_normU a0,
      v6nD_eq_normV (b1 := b1) (b2 := b2) (b3 := b3),
      v6chainQ2_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz]

/-- Body window digit `q[1]` = v5 model quotient digit 1. -/
theorem v6chainQ1_v6n_eq_model
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    v6chainQ1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0) =
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  rw [v6nU4_eq_normU a0, v6nU3_eq_normU a0, v6nU2_eq_normU a0, v6nU1_eq_normU a0,
      v6nD_eq_normV (b1 := b1) (b2 := b2) (b3 := b3),
      v6chainQ1_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz]

/-- Body window digit `q[0]` = v5 model quotient digit 0. -/
theorem v6chainQ0_v6n_eq_model
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0)
              (v6nU0 a0 b0) (v6nD b0) =
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  rw [v6nU4_eq_normU a0, v6nU3_eq_normU a0, v6nU2_eq_normU a0, v6nU1_eq_normU a0,
      v6nU0_eq_normU a0, v6nD_eq_normV (b1 := b1) (b2 := b2) (b3 := b3),
      v6chainQ0_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz]

-- ============================================================================
-- Capstone: the body-window quotient word = `EvmWord.div a b`.
-- ============================================================================

/-- **v6 DIV fast-path quotient correctness (arithmetic), from shape.** The four
    quotient digits the fast-path body stores (each `v6chainQ_j` of the concrete
    normalized window `v6nU…`/`v6nD`) assemble — as a 4-limb `EvmWord` — into the
    exact quotient `EvmWord.div a b`.  Composes the body-window digit bridges
    with `fullDivN1QuotientWordV5_eq_div_of_shape`.  The arithmetic heart of
    `evm_div_v6_stack_spec`; bead `evm-asm-dr466.2`. -/
theorem v6n_quotient_word_eq_div
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    EvmWord.fromLimbs (fun i : Fin 4 => match i with
      | 0 => v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0)
               (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0)
      | 1 => v6chainQ1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0)
      | 2 => v6chainQ2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0)
      | 3 => v6chainQ3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0)) =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  rw [v6chainQ0_v6n_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz,
      v6chainQ1_v6n_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz,
      v6chainQ2_v6n_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz,
      v6chainQ3_v6n_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz]
  exact fullDivN1QuotientWordV5_eq_div_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz

-- ============================================================================
-- Per-limb form: `(EvmWord.div a b).getLimbN j = q[j]` (for `divStackDispatchPost`).
-- ============================================================================

/-- The fast-path stored quotient limb `q[0]` is `EvmWord.div`'s limb 0. -/
theorem v6n_div_getLimbN_0
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 0
      = v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0) := by
  exact ((congrArg (fun w => w.getLimbN 0)
    (v6n_quotient_word_eq_div a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)).symm).trans
    EvmWord.getLimbN_fromLimbs_0

/-- The fast-path stored quotient limb `q[1]` is `EvmWord.div`'s limb 1. -/
theorem v6n_div_getLimbN_1
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 1
      = v6chainQ1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0) := by
  exact ((congrArg (fun w => w.getLimbN 1)
    (v6n_quotient_word_eq_div a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)).symm).trans
    EvmWord.getLimbN_fromLimbs_1

/-- The fast-path stored quotient limb `q[2]` is `EvmWord.div`'s limb 2. -/
theorem v6n_div_getLimbN_2
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 2
      = v6chainQ2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0) := by
  exact ((congrArg (fun w => w.getLimbN 2)
    (v6n_quotient_word_eq_div a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)).symm).trans
    EvmWord.getLimbN_fromLimbs_2

/-- The fast-path stored quotient limb `q[3]` is `EvmWord.div`'s limb 3. -/
theorem v6n_div_getLimbN_3
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 3
      = v6chainQ3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0) := by
  exact ((congrArg (fun w => w.getLimbN 3)
    (v6n_quotient_word_eq_div a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)).symm).trans
    EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
