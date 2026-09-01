/-
  EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceModelFuel

  Bridges from the bounded machine-shaped Taylor recursion to the unbounded
  model.  The recurrence and its local arithmetic definitions live in
  `AmsterdamBlobGasPriceModel`; this file owns the longer fuel inductions.
-/

import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceModel

namespace EvmAsm.Codegen.AmsterdamBlobGasPrice

open EvmAsm.Stateless.SpecRef
open EvmAsm.Evm64.EvmWord

set_option maxRecDepth 8000

/- A machine run that has already crossed the reference-level output bound can
   only finish with an oversized sum or hit one of the machine's own overflow
   guards.  The latter is deliberately retained in the conclusion: the
   machine checks a 384-bit intermediate while the reference model stops at
   the 256-bit result bound, so crossing the smaller bound is not itself a
   machine overflow. -/
theorem priceLoopFuel_bound_from_prefix
    (num j : Nat)
    (h_j : j ≤ 495)
    (h_bound : taylorOutputBound ≤
      (priceLoopPrefix num j).2 + (priceLoopPrefix num j).1) :
    priceLoopFuel num (496 - j) (j + 1)
        (priceLoopPrefix num j).1 (priceLoopPrefix num j).2 = .ovf ∨
      ∃ S, priceLoopFuel num (496 - j) (j + 1)
          (priceLoopPrefix num j).1 (priceLoopPrefix num j).2 = .done S ∧
        taylorOutputBound ≤ S := by
  let P : Nat → Prop := fun n =>
    ∀ j, 495 - j = n → j ≤ 495 →
      taylorOutputBound ≤
        (priceLoopPrefix num j).2 + (priceLoopPrefix num j).1 →
      priceLoopFuel num (496 - j) (j + 1)
          (priceLoopPrefix num j).1 (priceLoopPrefix num j).2 = .ovf ∨
        ∃ S, priceLoopFuel num (496 - j) (j + 1)
            (priceLoopPrefix num j).1 (priceLoopPrefix num j).2 = .done S ∧
          taylorOutputBound ≤ S
  have hP : P (495 - j) := by
    apply Nat.strong_induction_on
    intro n ih j' h_jn h_j' h_bound'
    by_cases h_acc : (priceLoopPrefix num j').1 = 0
    · right
      refine ⟨(priceLoopPrefix num j').2, ?_, ?_⟩
      · have h_fuel : 496 - j' = (495 - j') + 1 := by omega
        rw [h_fuel]
        simp only [priceLoopFuel, if_pos h_acc]
      · simpa [h_acc] using h_bound'
    · by_cases h_last : j' = 495
      · left
        have h_fuel : 496 - j' = 1 := by omega
        rw [h_fuel]
        simp only [priceLoopFuel, if_neg h_acc, if_pos (by omega : 496 ≤ j' + 1)]
      · have h_lt : j' < 495 := by omega
        have h_i : ¬ 496 ≤ j' + 1 := by omega
        by_cases h_sum : taylorWord384Bound ≤
            (priceLoopPrefix num j').2 + (priceLoopPrefix num j').1
        · left
          have h_fuel : 496 - j' = (496 - (j' + 1)) + 1 := by omega
          rw [h_fuel]
          simp only [priceLoopFuel, if_neg h_acc, if_neg h_i, if_pos h_sum]
        · by_cases h_prod : taylorWord384Bound ≤
              (priceLoopPrefix num j').1 * num
          · left
            have h_fuel : 496 - j' = (496 - (j' + 1)) + 1 := by omega
            rw [h_fuel]
            simp only [priceLoopFuel, if_neg h_acc, if_neg h_i, if_neg h_sum,
              if_pos h_prod]
          · have h_next_bound : taylorOutputBound ≤
                (priceLoopPrefix num (j' + 1)).2 +
                  (priceLoopPrefix num (j' + 1)).1 := by
              rw [priceLoopPrefix_step]
              exact le_trans h_bound' (Nat.le_add_right _ _)
            have h_rem : 495 - (j' + 1) < n := by omega
            have h_next := ih (495 - (j' + 1)) h_rem (j' + 1)
              (by omega) (by omega) h_next_bound
            have h_fuel : 496 - j' = (496 - (j' + 1)) + 1 := by omega
            rw [h_fuel]
            simp only [priceLoopFuel, if_neg h_acc, if_neg h_i,
              if_neg h_sum, if_neg h_prod]
            simpa [priceLoopPrefix_step] using h_next
  exact hP j rfl h_j h_bound

/- The converse bridge for the unbounded model.  A `none` caused by the
   reference's 256-bit output guard is handled by the preceding theorem; a
   `none` caused by a 384-bit product guard or by the cap is the machine's
   `.ovf` arm, and the remaining case recurses over the same prefix state. -/
theorem priceLoopFuel_none_from_prefix
    (num j : Nat)
    (h_j : j ≤ 495)
    (h_none :
      taylor384Aux num taylorDenominator (j + 1)
        (priceLoopPrefix num j).1 (priceLoopPrefix num j).2 = none) :
    priceLoopFuel num (496 - j) (j + 1)
        (priceLoopPrefix num j).1 (priceLoopPrefix num j).2 = .ovf ∨
      ∃ S, priceLoopFuel num (496 - j) (j + 1)
          (priceLoopPrefix num j).1 (priceLoopPrefix num j).2 = .done S ∧
        taylorOutputBound ≤ S := by
  let P : Nat → Prop := fun n =>
    ∀ j, 495 - j = n → j ≤ 495 →
      taylor384Aux num taylorDenominator (j + 1)
          (priceLoopPrefix num j).1 (priceLoopPrefix num j).2 = none →
      priceLoopFuel num (496 - j) (j + 1)
          (priceLoopPrefix num j).1 (priceLoopPrefix num j).2 = .ovf ∨
        ∃ S, priceLoopFuel num (496 - j) (j + 1)
            (priceLoopPrefix num j).1 (priceLoopPrefix num j).2 = .done S ∧
          taylorOutputBound ≤ S
  have hP : P (495 - j) := by
    apply Nat.strong_induction_on
    intro n ih j' h_jn h_j' h_none'
    by_cases h_acc : (priceLoopPrefix num j').1 = 0
    · right
      refine ⟨(priceLoopPrefix num j').2, ?_, ?_⟩
      · have h_fuel : 496 - j' = (495 - j') + 1 := by omega
        rw [h_fuel]
        simp only [priceLoopFuel, if_pos h_acc]
      · rw [taylor384Aux.eq_1, if_pos h_acc] at h_none'
        split at h_none'
        · cases h_none'
        · exact Nat.le_of_not_gt (by assumption)
    · by_cases h_bound : taylorOutputBound ≤
          (priceLoopPrefix num j').2 + (priceLoopPrefix num j').1
      · exact priceLoopFuel_bound_from_prefix num j' h_j' h_bound
      · rw [taylor384Aux.eq_1, if_neg h_acc, if_neg h_bound] at h_none'
        by_cases h_prod : taylorWord384Bound ≤
            (priceLoopPrefix num j').1 * num
        · left
          by_cases h_last : j' = 495
          · have h_fuel : 496 - j' = 1 := by omega
            rw [h_fuel]
            simp only [priceLoopFuel, if_neg h_acc,
              if_pos (by omega : 496 ≤ j' + 1)]
          · have h_lt : j' < 495 := by omega
            have h_i : ¬ 496 ≤ j' + 1 := by omega
            have h_fuel : 496 - j' = (496 - (j' + 1)) + 1 := by omega
            by_cases h_sum : taylorWord384Bound ≤
                (priceLoopPrefix num j').2 + (priceLoopPrefix num j').1
            · rw [h_fuel]
              simp only [priceLoopFuel, if_neg h_acc, if_neg h_i,
                if_pos h_sum]
            · rw [h_fuel]
              simp only [priceLoopFuel, if_neg h_acc, if_neg h_i,
                if_neg h_sum, if_pos h_prod]
        · by_cases h_last : j' = 495
          · subst j'
            have h_acc_pos : 0 < (priceLoopPrefix num 495).1 := by omega
            have h_cap := priceLoopPrefix_cap_output_ge (num := num) h_acc_pos
            omega
          · have h_lt : j' < 495 := by omega
            have h_i : ¬ 496 ≤ j' + 1 := by omega
            have h_none_next :
                taylor384Aux num taylorDenominator (j' + 1 + 1)
                  ((priceLoopPrefix num j').1 * num /
                    (taylorDenominator * (j' + 1)))
                  ((priceLoopPrefix num j').2 +
                    (priceLoopPrefix num j').1) = none := by
              rw [if_neg h_prod] at h_none'
              exact h_none'
            have h_rem : 495 - (j' + 1) < n := by omega
            have h_next := ih (495 - (j' + 1)) h_rem (j' + 1)
              (by omega) (by omega)
              (by simpa [priceLoopPrefix_step] using h_none_next)
            have h_fuel : 496 - j' = (496 - (j' + 1)) + 1 := by omega
            by_cases h_sum : taylorWord384Bound ≤
                (priceLoopPrefix num j').2 + (priceLoopPrefix num j').1
            · left
              rw [h_fuel]
              simp only [priceLoopFuel, if_neg h_acc, if_neg h_i,
                if_pos h_sum]
            · rw [h_fuel]
              simp only [priceLoopFuel, if_neg h_acc, if_neg h_i,
                if_neg h_sum, if_neg h_prod]
              simpa [priceLoopPrefix_step] using h_next
  exact hP j rfl h_j h_none

/- At entry, a reference `none` result therefore has exactly the two machine
   representations needed by the status-1 tail: either a machine overflow arm
   fired, or the loop reached its zero-accumulator exit after the 256-bit
   output bound had already been crossed. -/
theorem priceLoopFuel_none_initial
    (num : Nat) (h_none : taylorExp384 num = none) :
    priceLoopFuel num 496 1 taylorDenominator 0 = .ovf ∨
      ∃ S, priceLoopFuel num 496 1 taylorDenominator 0 = .done S ∧
        taylorOutputBound ≤ S := by
  have h_none' :
      taylor384Aux num taylorDenominator 1 taylorDenominator 0 = none := by
    simpa [taylorExp384] using h_none
  have h := priceLoopFuel_none_from_prefix num 0 (by omega) (by
    simpa [priceLoopPrefix] using h_none')
  simpa [priceLoopPrefix] using h

#print axioms priceLoopFuel_bound_from_prefix
#print axioms priceLoopFuel_none_from_prefix
#print axioms priceLoopFuel_none_initial

end EvmAsm.Codegen.AmsterdamBlobGasPrice
