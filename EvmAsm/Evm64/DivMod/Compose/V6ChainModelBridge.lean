/-
  EvmAsm.Evm64.DivMod.Compose.V6ChainModelBridge

  The abstract digit-quotient bridge for the v6 DIV fast arm (bead dr466.1):
  the v6 body's per-digit chain `v6chainQ_j` / `v6chainR_j` (each an exact
  `div128V5CodeQuot` of its window, with the remainder threaded as
  `uLo -₆₄ q·d`) equals, digit-by-digit, the v5 model `fullDivN1R_jV5.1` /
  `.2.1` — over the normalized window `NormU`/`NormV`.

  Each step composes three already-verified facts:
    - `div128V5CodeQuot_eq_div128Quot_v5` (the body trial = the model trial),
    - `fullDivN1R_jV5_quot_eq_div128_of_shape` (model digit = capped trial),
    - `fullDivN1R_jV5_rem_eq_of_shape` (model remainder = `uLo -₆₄ q·v0'`),
  the last of which lets the previous digit's threaded remainder `v6chainR_{j+1}`
  be rewritten to the model's `(R_{j+1}V5).2.1` before the next quotient step.

  Combined with `fullDivN1QuotientWordV5_eq_div_of_shape`, these pin the v6
  body's stored quotient word to `EvmWord.div a b`, en route to
  `evm_div_v6_stack_spec` (#9303).
-/

import EvmAsm.Evm64.DivMod.Compose.DigitChainV6
import EvmAsm.Evm64.DivMod.Spec.N1V5DigitSteps
import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5DigitBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

variable (a0 a1 a2 a3 b0 b1 b2 b3 : Word)

/-- Top digit (`j=3`) quotient: `v6chainQ3` over the normalized window equals the
    v5 model's top quotient digit. -/
theorem v6chainQ3_eq_model
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    v6chainQ3 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
              (fullDivN1NormV b0 b1 b2 b3).1 =
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  rw [v6chainQ3, div128V5CodeQuot_eq_div128Quot_v5,
      fullDivN1R3V5_quot_eq_div128_of_shape a0 a1 a2 a3 b0 b1 b2 b3
        hbnz hb1z hb2z hb3z hshift_nz]

/-- Top digit (`j=3`) threaded remainder: `v6chainR3` equals the v5 model's
    digit-3 remainder limb. -/
theorem v6chainR3_eq_model
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    v6chainR3 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
              (fullDivN1NormV b0 b1 b2 b3).1 =
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1 := by
  rw [v6chainR3, v6chainQ3, div128V5CodeQuot_eq_div128Quot_v5,
      fullDivN1R3V5_rem_eq_of_shape a0 a1 a2 a3 b0 b1 b2 b3
        hbnz hb1z hb2z hb3z hshift_nz]

/-- Digit `j=2` quotient (threads digit 3's remainder). -/
theorem v6chainQ2_eq_model
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    v6chainQ2 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
              (fullDivN1NormV b0 b1 b2 b3).1 =
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  rw [v6chainQ2,
      v6chainR3_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz,
      div128V5CodeQuot_eq_div128Quot_v5,
      fullDivN1R2V5_quot_eq_div128_of_shape a0 a1 a2 a3 b0 b1 b2 b3
        hbnz hb1z hb2z hb3z hshift_nz]

/-- Digit `j=2` threaded remainder. -/
theorem v6chainR2_eq_model
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    v6chainR2 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
              (fullDivN1NormV b0 b1 b2 b3).1 =
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 := by
  rw [v6chainR2, v6chainQ2,
      v6chainR3_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz,
      div128V5CodeQuot_eq_div128Quot_v5,
      fullDivN1R2V5_rem_eq_of_shape a0 a1 a2 a3 b0 b1 b2 b3
        hbnz hb1z hb2z hb3z hshift_nz]

/-- Digit `j=1` quotient (threads digit 2's remainder). -/
theorem v6chainQ1_eq_model
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    v6chainQ1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
              (fullDivN1NormU a0 a1 a2 a3 b0).2.1
              (fullDivN1NormV b0 b1 b2 b3).1 =
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  rw [v6chainQ1,
      v6chainR2_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz,
      div128V5CodeQuot_eq_div128Quot_v5,
      fullDivN1R1V5_quot_eq_div128_of_shape a0 a1 a2 a3 b0 b1 b2 b3
        hbnz hb1z hb2z hb3z hshift_nz]

/-- Digit `j=1` threaded remainder. -/
theorem v6chainR1_eq_model
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    v6chainR1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
              (fullDivN1NormU a0 a1 a2 a3 b0).2.1
              (fullDivN1NormV b0 b1 b2 b3).1 =
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 := by
  rw [v6chainR1, v6chainQ1,
      v6chainR2_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz,
      div128V5CodeQuot_eq_div128Quot_v5,
      fullDivN1R1V5_rem_eq_of_shape a0 a1 a2 a3 b0 b1 b2 b3
        hbnz hb1z hb2z hb3z hshift_nz]

/-- Digit `j=0` quotient (threads digit 1's remainder). -/
theorem v6chainQ0_eq_model
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    v6chainQ0 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
              (fullDivN1NormU a0 a1 a2 a3 b0).2.1
              (fullDivN1NormU a0 a1 a2 a3 b0).1
              (fullDivN1NormV b0 b1 b2 b3).1 =
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  rw [v6chainQ0,
      v6chainR1_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz,
      div128V5CodeQuot_eq_div128Quot_v5,
      fullDivN1R0V5_quot_eq_div128_of_shape a0 a1 a2 a3 b0 b1 b2 b3
        hbnz hb1z hb2z hb3z hshift_nz]

/-- Digit `j=0` threaded remainder (the final fast-path remainder limb). -/
theorem v6chainR0_eq_model
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    v6chainR0 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
              (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
              (fullDivN1NormU a0 a1 a2 a3 b0).2.1
              (fullDivN1NormU a0 a1 a2 a3 b0).1
              (fullDivN1NormV b0 b1 b2 b3).1 =
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 := by
  rw [v6chainR0, v6chainQ0,
      v6chainR1_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz,
      div128V5CodeQuot_eq_div128Quot_v5,
      fullDivN1R0V5_rem_eq_of_shape a0 a1 a2 a3 b0 b1 b2 b3
        hbnz hb1z hb2z hb3z hshift_nz]

end EvmAsm.Evm64
