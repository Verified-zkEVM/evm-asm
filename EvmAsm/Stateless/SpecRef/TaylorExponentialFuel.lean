/-
  EvmAsm.Stateless.SpecRef.TaylorExponentialFuel

  Fuel correspondence for the reference port's `taylor_exponential`.

  `taylorAux` is structurally fueled while the execution-specs recurrence is
  total over unbounded integers.  This file proves that the published fuel
  formula is sufficient for the `factor = 1` path used by blob-gas pricing.
  The proof is an arithmetic bound on the exact recurrence: terms are bounded
  through the quotient phase by a factorial estimate, then halve once the
  iteration index is at least twice the quotient.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic
public import EvmAsm.Stateless.SpecRef.Gas
public import EvmAsm.Stateless.SpecRef.TaylorExponential

public section

set_option maxRecDepth 8000

namespace EvmAsm.Stateless.SpecRef

def taylorFuelNeeded (num denominator : Nat) : Nat → Nat → Nat
  | i, acc =>
      if acc = 0 then 0
      else 1 + taylorFuelNeeded num denominator
        (i + 1) (acc * num / (denominator * i))
termination_by i acc => (num / denominator + 1 - i, acc)
decreasing_by
  by_cases h_den : denominator = 0
  · simp [h_den]
    omega
  · have h_den_pos : 0 < denominator := Nat.pos_of_ne_zero h_den
    by_cases h_i : i ≤ num / denominator
    · simp_wf
      omega
    · have h_num_lt : num < i * denominator := by
        apply Nat.lt_of_not_ge
        intro h_num_ge
        apply h_i
        exact (Nat.le_div_iff_mul_le h_den_pos).2
          (by simpa [Nat.mul_comm] using h_num_ge)
      have h_acc_pos : 0 < acc := by omega
      have h_prod_lt : acc * num < (denominator * i) * acc := by
        calc
          acc * num < acc * (i * denominator) :=
            Nat.mul_lt_mul_of_pos_left h_num_lt h_acc_pos
          _ = (denominator * i) * acc := by ring
      have h_acc_lt : acc * num / (denominator * i) < acc := by
        exact Nat.div_lt_of_lt_mul h_prod_lt
      have h_old_zero : num / denominator + 1 - i = 0 := by omega
      have h_new_zero : num / denominator + 1 - (i + 1) = 0 := by omega
      rw [h_old_zero, h_new_zero]
      exact Prod.Lex.right 0 h_acc_lt

theorem taylorAux_eq_pure_of_fuel
    (num denominator fuel i acc output : Nat)
    (h_fuel : taylorFuelNeeded num denominator i acc ≤ fuel) :
    taylorAux num denominator fuel i acc output =
      pure (taylorNatAux num denominator i acc output) := by
  induction fuel generalizing i acc output with
  | zero =>
      by_cases h_acc : acc = 0
      · subst acc
        rw [taylorAux.eq_1, taylorNatAux_zero]
      · have h_pos : 0 < taylorFuelNeeded num denominator i acc := by
          rw [taylorFuelNeeded.eq_1, if_neg h_acc]
          omega
        omega
  | succ fuel ih =>
      by_cases h_acc : acc = 0
      · subst acc
        rw [taylorAux.eq_1, taylorNatAux_zero]
      · have h_needed : taylorFuelNeeded num denominator
            (i + 1) (acc * num / (denominator * i)) ≤ fuel := by
          rw [taylorFuelNeeded.eq_1, if_neg h_acc] at h_fuel
          omega
        simp only [taylorAux]
        rw [taylorNatAux_step num denominator i acc output h_acc]
        exact ih (i + 1) (acc * num / (denominator * i))
          (output + acc) h_needed

def taylorPrefix (num denominator : Nat) : Nat → Nat × Nat
  | 0 => (denominator, 0)
  | j + 1 =>
      let s := taylorPrefix num denominator j
      (s.1 * num / (denominator * (j + 1)), s.2 + s.1)

theorem num_lt_den_mul_div_succ (num denominator : Nat) (h_den : 0 < denominator) :
    num < denominator * (num / denominator + 1) := by
  have h_eq := Nat.mod_add_div num denominator
  have h_mod : num % denominator < denominator := Nat.mod_lt _ h_den
  calc
    num = num % denominator + denominator * (num / denominator) := h_eq.symm
    _ < denominator + denominator * (num / denominator) :=
      Nat.add_lt_add_right h_mod _
    _ = denominator * (num / denominator + 1) := by ring

theorem pow_succ_le_four_pow_factorial (q : Nat) :
    (q + 1) ^ q ≤ 4 ^ q * q.factorial := by
  have h_fac : q.factorial * (q + 1) ^ q ≤ (q + q).factorial :=
    Nat.factorial_mul_pow_le_factorial
  have h_choose : (2 * q).choose q ≤ 2 ^ (2 * q) :=
    Nat.choose_le_two_pow (2 * q) q
  have h_choose_eq : (2 * q).choose q * q.factorial * q.factorial =
      (2 * q).factorial := by
    simpa only [show 2 * q - q = q by omega] using
      (Nat.choose_mul_factorial_mul_factorial (n := 2 * q) (k := q)
        (by omega))
  have h_central : (2 * q).factorial ≤ 4 ^ q * q.factorial * q.factorial := by
    rw [← h_choose_eq]
    calc
      (2 * q).choose q * q.factorial * q.factorial ≤
          2 ^ (2 * q) * q.factorial * q.factorial := by
        simpa [Nat.mul_assoc] using
          (Nat.mul_le_mul_right (q.factorial * q.factorial) h_choose)
      _ = 4 ^ q * q.factorial * q.factorial := by
        have hpow : 2 ^ (2 * q) = 4 ^ q := by
          calc
            2 ^ (2 * q) = 2 ^ (q * 2) := by
              congr 1
              omega
            _ = 2 ^ (2 * q) := by
              congr 1
              omega
            _ = (2 ^ 2) ^ q := by
              symm
              rw [pow_mul]
            _ = 4 ^ q := by norm_num
        rw [hpow]
  have h_combined : q.factorial * (q + 1) ^ q ≤
      (4 ^ q * q.factorial) * q.factorial := by
    exact h_fac.trans (by simpa [Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm, two_mul] using h_central)
  exact Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_comm] using h_combined)
    q.factorial_pos

theorem taylorPrefix_acc_factorial_bound
    (num denominator : Nat) (h_den : 0 < denominator) :
    ∀ j, (taylorPrefix num denominator j).1 * j.factorial ≤
      denominator * (num / denominator + 1) ^ j := by
  intro j
  induction j with
  | zero =>
      simp [taylorPrefix]
  | succ j ih =>
      simp only [taylorPrefix]
      have h_floor := Nat.div_mul_le_self
        ((taylorPrefix num denominator j).1 * num)
        (denominator * (j + 1))
      have h_num_lt := num_lt_den_mul_div_succ num denominator h_den
      have h_num_le : num ≤ denominator * (num / denominator + 1) :=
        Nat.le_of_lt h_num_lt
      apply Nat.le_of_mul_le_mul_left (c := denominator) ?_ h_den
      calc
        denominator *
              (((taylorPrefix num denominator j).1 * num /
                (denominator * (j + 1))) * (j + 1).factorial) =
            ((taylorPrefix num denominator j).1 * num /
              (denominator * (j + 1))) *
              (denominator * (j + 1)) * j.factorial := by
                rw [Nat.factorial_succ]
                ring
        _ ≤ ((taylorPrefix num denominator j).1 * num) * j.factorial := by
              exact Nat.mul_le_mul_right j.factorial h_floor
        _ ≤ (denominator * (num / denominator + 1) ^ j) * num := by
              simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
                (Nat.mul_le_mul_right num ih)
        _ ≤ (denominator * (num / denominator + 1) ^ j) *
              (denominator * (num / denominator + 1)) := by
              exact Nat.mul_le_mul_left _ h_num_le
        _ = denominator *
              (denominator * (num / denominator + 1) ^ (j + 1)) := by
              ring_nf

theorem pow_mul_factorial_le_pow_mul_factorial
    (q j : Nat) (h_j : j ≤ q) :
    (q + 1) ^ j * q.factorial ≤ (q + 1) ^ q * j.factorial := by
  have P : ∀ n, ∀ q j, q - j = n → j ≤ q →
      (q + 1) ^ j * q.factorial ≤ (q + 1) ^ q * j.factorial := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro q j h_diff h_j'
        by_cases h_eq : j = q
        · subst q
          simp
        · have h_j_lt : j < q := by omega
          have h_diff' : q - (j + 1) < n := by omega
          have h_next := ih (q - (j + 1)) h_diff' q (j + 1)
            (by omega) (by omega)
          have h_factorial : (j + 1).factorial ≤
              (q + 1) * j.factorial := by
            rw [Nat.factorial_succ]
            exact Nat.mul_le_mul_right j.factorial (by omega)
          have h_factorial' := Nat.mul_le_mul_left ((q + 1) ^ q) h_factorial
          have h_step :
              (q + 1) ^ (j + 1) * q.factorial ≤
                (q + 1) ^ (q + 1) * j.factorial := by
            calc
              (q + 1) ^ (j + 1) * q.factorial ≤
                  (q + 1) ^ q * (j + 1).factorial := h_next
              _ ≤ (q + 1) ^ q * ((q + 1) * j.factorial) := h_factorial'
              _ = (q + 1) ^ (q + 1) * j.factorial := by
                    rw [pow_succ]
                    ring
          have h_cancel :
              ((q + 1) ^ j * q.factorial) * (q + 1) ≤
                ((q + 1) ^ q * j.factorial) * (q + 1) := by
            simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
              using h_step
          exact Nat.le_of_mul_le_mul_right h_cancel (by omega)
  exact P (q - j) q j rfl h_j

theorem taylorPrefix_acc_le_four_pow
    (num denominator : Nat) (h_den : 0 < denominator)
    (j : Nat) (h_j : j ≤ num / denominator) :
    (taylorPrefix num denominator j).1 ≤
      denominator * 4 ^ (num / denominator) := by
  have h_inv := taylorPrefix_acc_factorial_bound num denominator h_den j
  have h_ratio := pow_mul_factorial_le_pow_mul_factorial
    (num / denominator) j h_j
  have h_acc_qfac :
      (taylorPrefix num denominator j).1 * (num / denominator).factorial ≤
        denominator * (num / denominator + 1) ^ (num / denominator) := by
    have h1 := Nat.mul_le_mul_right (num / denominator).factorial h_inv
    have h2 := Nat.mul_le_mul_left denominator h_ratio
    have h3 :
        ((taylorPrefix num denominator j).1 *
            (num / denominator).factorial) * j.factorial ≤
          (denominator * (num / denominator + 1) ^
              (num / denominator)) * j.factorial := by
      calc
        ((taylorPrefix num denominator j).1 *
            (num / denominator).factorial) * j.factorial =
            ((taylorPrefix num denominator j).1 * j.factorial) *
              (num / denominator).factorial := by ring
        _ ≤ (denominator * (num / denominator + 1) ^ j) *
              (num / denominator).factorial := h1
        _ ≤ (denominator *
              ((num / denominator + 1) ^ (num / denominator) * j.factorial)) := by
              simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h2
        _ = (denominator * (num / denominator + 1) ^
              (num / denominator)) * j.factorial := by ring
    exact Nat.le_of_mul_le_mul_right h3 j.factorial_pos
  have h_pow := pow_succ_le_four_pow_factorial (num / denominator)
  have h_mul := Nat.mul_le_mul_left denominator h_pow
  have h_acc_four :
      (taylorPrefix num denominator j).1 * (num / denominator).factorial ≤
        (denominator * 4 ^ (num / denominator)) *
          (num / denominator).factorial := by
    calc
      (taylorPrefix num denominator j).1 * (num / denominator).factorial ≤
          denominator * (num / denominator + 1) ^ (num / denominator) :=
            h_acc_qfac
      _ ≤ (denominator * 4 ^ (num / denominator)) *
            (num / denominator).factorial := by
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h_mul
  exact Nat.le_of_mul_le_mul_right h_acc_four
    (num / denominator).factorial_pos

theorem taylorPrefix_acc_le_at_quotient
    (num denominator : Nat) (h_den : 0 < denominator) :
    ∀ j, num / denominator ≤ j →
      (taylorPrefix num denominator j).1 ≤
        (taylorPrefix num denominator (num / denominator)).1 := by
  intro j
  induction j with
  | zero =>
      intro h_j
      have h_q : num / denominator = 0 := Nat.eq_zero_of_le_zero h_j
      simp [h_q]
  | succ j ih =>
      intro h_j
      by_cases h_qj : num / denominator ≤ j
      · have h_num_lt := num_lt_den_mul_div_succ num denominator h_den
        have h_num_le : num ≤ denominator * (num / denominator + 1) :=
          Nat.le_of_lt h_num_lt
        have h_num_step : num ≤ denominator * (j + 1) := by
          exact h_num_le.trans (Nat.mul_le_mul_left denominator (by omega))
        have h_step :
            (taylorPrefix num denominator (j + 1)).1 ≤
              (taylorPrefix num denominator j).1 := by
          simp only [taylorPrefix]
          exact Nat.div_le_of_le_mul (by
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
              (Nat.mul_le_mul_left (taylorPrefix num denominator j).1
                h_num_step))
        exact h_step.trans (ih h_qj)
      · have h_eq : num / denominator = j + 1 := by omega
        simp [h_eq]

theorem taylorPrefix_acc_le_four_pow_all
    (num denominator : Nat) (h_den : 0 < denominator) (j : Nat) :
    (taylorPrefix num denominator j).1 ≤
      denominator * 4 ^ (num / denominator) := by
  by_cases h_j : j ≤ num / denominator
  · exact taylorPrefix_acc_le_four_pow num denominator h_den j h_j
  · have h_qj : num / denominator ≤ j := by omega
    exact (taylorPrefix_acc_le_at_quotient num denominator h_den j h_qj).trans
      (taylorPrefix_acc_le_four_pow num denominator h_den
        (num / denominator) le_rfl)

theorem taylorNextAcc_two_mul_le
    (num denominator i acc : Nat) (h_den : 0 < denominator)
    (h_i : 2 * (num / denominator + 1) ≤ i) :
    2 * (acc * num / (denominator * i)) ≤ acc := by
  have h_num_lt := num_lt_den_mul_div_succ num denominator h_den
  have h_num_le : 2 * num ≤ denominator * i := by
    have h_scaled := Nat.mul_le_mul_left 2 (Nat.le_of_lt h_num_lt)
    have h_mono := Nat.mul_le_mul_left denominator h_i
    calc
      2 * num ≤ 2 * (denominator * (num / denominator + 1)) := h_scaled
      _ = denominator * (2 * (num / denominator + 1)) := by ring
      _ ≤ denominator * i := h_mono
  have h_i_pos : 0 < i := by
    exact lt_of_lt_of_le
      (Nat.mul_pos (by decide) (Nat.zero_lt_succ _)) h_i
  have h_den_pos : 0 < denominator * i := Nat.mul_pos h_den h_i_pos
  have h_floor := Nat.div_mul_le_self (acc * num) (denominator * i)
  have h_floor2 := Nat.mul_le_mul_left 2 h_floor
  have h_prod := Nat.mul_le_mul_left acc h_num_le
  have h_combined :
      (2 * (acc * num / (denominator * i))) * (denominator * i) ≤
        acc * (denominator * i) := by
    calc
      (2 * (acc * num / (denominator * i))) * (denominator * i) =
          2 * ((acc * num / (denominator * i)) * (denominator * i)) := by ring
      _ ≤ 2 * (acc * num) := h_floor2
      _ ≤ acc * (denominator * i) := by
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h_prod
  exact Nat.le_of_mul_le_mul_right h_combined h_den_pos

theorem taylorDenominator_mul_four_pow_lt_two_pow
    (q denominator : Nat) :
    denominator * 4 ^ q <
      2 ^ (2 * q + Nat.log2 (denominator + 2) + 1) := by
  have h_four : 4 ^ q = 2 ^ (2 * q) := by
    calc
      4 ^ q = (2 ^ 2) ^ q := by norm_num
      _ = 2 ^ (2 * q) := by rw [pow_mul]
  have h_den_lt : denominator <
      2 ^ (Nat.log2 (denominator + 2) + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by decide)
      (denominator + 2)
    rw [Nat.log2_eq_log_two]
    have h_plus : denominator + 2 <
        2 ^ (Nat.log 2 (denominator + 2) + 1) := by
      simpa [Nat.succ_eq_add_one] using h
    exact lt_trans (by omega) h_plus
  calc
    denominator * 4 ^ q = denominator * 2 ^ (2 * q) := by rw [h_four]
    _ < 2 ^ (Nat.log2 (denominator + 2) + 1) * 2 ^ (2 * q) :=
      Nat.mul_lt_mul_of_pos_right h_den_lt (Nat.pow_pos (by decide))
    _ = 2 ^ (2 * q + Nat.log2 (denominator + 2) + 1) := by
      rw [← Nat.pow_add]
      congr 1
      omega

theorem taylorFuelNeeded_le_of_pow
    (num denominator i acc exponent : Nat) (h_den : 0 < denominator)
    (h_i : 2 * (num / denominator + 1) ≤ i)
    (h_acc : acc < 2 ^ exponent) :
    taylorFuelNeeded num denominator i acc ≤ exponent := by
  induction exponent generalizing i acc with
  | zero =>
      have h_zero : acc = 0 := by omega
      simp [taylorFuelNeeded, h_zero]
  | succ exponent ih =>
      by_cases h_acc_zero : acc = 0
      · simp [taylorFuelNeeded, h_acc_zero]
      · have h_half := taylorNextAcc_two_mul_le
          num denominator i acc h_den h_i
        have h_next_acc :
            acc * num / (denominator * i) < 2 ^ exponent := by
          rw [pow_succ] at h_acc
          omega
        have h_next := ih (i + 1) (acc * num / (denominator * i))
          (by omega) h_next_acc
        rw [taylorFuelNeeded.eq_1, if_neg h_acc_zero]
        omega

theorem taylorFuelNeeded_entry_le
    (num denominator : Nat) (h_den : 0 < denominator) :
    taylorFuelNeeded num denominator 1 denominator ≤
      4 * (num / denominator) + Nat.log2 (denominator + 2) + 8 := by
  let phaseEnd := 2 * (num / denominator) + 1
  let tailFuel := 2 * (num / denominator) +
    Nat.log2 (denominator + 2) + 1
  have h_tail_acc :
      (taylorPrefix num denominator phaseEnd).1 < 2 ^ tailFuel := by
    have h_acc := taylorPrefix_acc_le_four_pow_all
      num denominator h_den phaseEnd
    have h_pow := taylorDenominator_mul_four_pow_lt_two_pow
      (num / denominator) denominator
    exact lt_of_le_of_lt h_acc (by simpa [phaseEnd, tailFuel] using h_pow)
  have h_tail_i :
      2 * (num / denominator + 1) ≤ phaseEnd + 1 := by
    dsimp [phaseEnd]
    omega
  have h_tail := taylorFuelNeeded_le_of_pow num denominator
    (phaseEnd + 1) (taylorPrefix num denominator phaseEnd).1 tailFuel
    h_den h_tail_i h_tail_acc
  have P : ∀ n, ∀ j, j ≤ phaseEnd → phaseEnd - j = n →
      taylorFuelNeeded num denominator (j + 1)
          (taylorPrefix num denominator j).1 ≤
        (phaseEnd - j) + tailFuel := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro j h_j h_diff
        by_cases h_eq : j = phaseEnd
        · subst j
          simpa using h_tail
        · have h_j_lt : j < phaseEnd := by omega
          have h_diff' : phaseEnd - (j + 1) < n := by omega
          have h_next := ih (phaseEnd - (j + 1)) h_diff' (j + 1)
            (by omega) (by omega)
          by_cases h_acc : (taylorPrefix num denominator j).1 = 0
          · simp [taylorFuelNeeded, h_acc]
          · rw [taylorFuelNeeded.eq_1, if_neg h_acc]
            have h_next' :
                taylorFuelNeeded num denominator (j + 1 + 1)
                    ((taylorPrefix num denominator j).1 * num /
                      (denominator * (j + 1))) ≤
                  (phaseEnd - (j + 1)) + tailFuel := by
              simpa only [taylorPrefix] using h_next
            omega
  have h_initial := P phaseEnd 0 (by omega) (by simp)
  have h_initial' :
      taylorFuelNeeded num denominator 1 denominator ≤
        phaseEnd + tailFuel := by
    simpa [taylorPrefix] using h_initial
  dsimp [phaseEnd, tailFuel] at h_initial'
  omega

theorem taylor_exponential_one_fuel_sufficient
    (num denominator : Nat) (h_den : 0 < denominator) :
    taylorFuelNeeded num denominator 1 (1 * denominator) ≤
      4 * (num / denominator) + Nat.log2 (1 * denominator + 2) + 8 := by
  simpa using taylorFuelNeeded_entry_le num denominator h_den

theorem calculate_blob_gas_price_fuel_sufficient
    (excess_blob_gas : U64) :
    taylorFuelNeeded excess_blob_gas
        GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION 1
        (GasCosts.BLOB_MIN_GASPRICE * GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION) ≤
      4 * (excess_blob_gas / GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION) +
        Nat.log2
          (GasCosts.BLOB_MIN_GASPRICE * GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION + 2) +
        8 := by
  simpa [GasCosts.BLOB_MIN_GASPRICE,
    GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION] using
    (taylor_exponential_one_fuel_sufficient excess_blob_gas
      GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION (by decide))

theorem taylor_exponential_one_eq_pure
    (num denominator : Nat) (h_den : 0 < denominator) :
    taylor_exponential 1 num denominator =
      pure (taylorExpNat 1 num denominator) := by
  have h_fuel := taylorFuelNeeded_entry_le num denominator h_den
  unfold taylor_exponential
  rw [taylorAux_eq_pure_of_fuel num denominator
    (4 * (num / denominator) + Nat.log2 (1 * denominator + 2) + 8)
    1 (1 * denominator) 0 (by simpa using h_fuel)]
  rw [taylorExpNat_eq_aux]
  simp

theorem calculate_blob_gas_price_eq_pure_taylorExpNat
    (excess_blob_gas : U64) :
    calculate_blob_gas_price excess_blob_gas =
      pure (taylorExpNat 1 excess_blob_gas
        GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION) := by
  unfold calculate_blob_gas_price
  apply taylor_exponential_one_eq_pure
  norm_num [GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION]

#print axioms taylor_exponential_one_fuel_sufficient
#print axioms calculate_blob_gas_price_fuel_sufficient
#print axioms taylor_exponential_one_eq_pure
#print axioms calculate_blob_gas_price_eq_pure_taylorExpNat

end EvmAsm.Stateless.SpecRef
