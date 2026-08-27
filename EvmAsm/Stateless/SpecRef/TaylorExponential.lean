/-
  EvmAsm.Stateless.SpecRef.TaylorExponential

  Exact Nat model and bounded implementation of execution-specs'
  `taylor_exponential` (ethereum/utils/numeric.py).

  The reference uses unbounded integers.  `taylorExp384` models the
  implementation budget needed by the two 256-bit consumers: when the
  numerator is below `2^64` and the result fits in `2^256`, its running output
  is bounded by `2^256 * D` and its intermediate product by `2^384`.  The final
  division by `D` is part of the bounded model.  The recurrence computes `D * i`
  exactly in `Nat`; a separate 64-bit divisor bound and a numeric iteration
  cap remain machine-facing obligations rather than claims of this file.  The
  exactness theorems below are intentionally separate from the RISC-V model;
  they are the arithmetic foundation for the later consumer proofs.

  The asymmetry is intentional: overflow detection is unconditional, while
  exact agreement on a returned value uses the `numerator < 2^64` premise to
  establish the 384-bit product bound.  The concrete traces below only show
  that these general premises are inhabited at their stated witness points;
  they do not discharge them for future consumers.

  The reference helper is total: `taylor_exponential` returns an unbounded
  `Uint` and has no failure arm.  A bounded `none` therefore needs a
  consumer-level interpretation.  An output outside `2^256` corresponds to
  a real reference exception only at a consumer that explicitly converts the
  returned value to `U256`, such as the `U256(blob_base_fee)` conversion in
  the `BLOBBASEFEE` opcode; `run_stateless_guest` catches that exception in
  `forks/amsterdam/stateless.py` at the validation `except` arm.  The
  `calculate_blob_gas_price` and header-validation consumers retain `Uint`,
  so their reference execution does not fail merely because the result is
  wider than `U256`.  A `none` caused by the 384-bit product guard has no
  corresponding reference failure; under the `numerator < 2^64` contract it
  must be ruled out as a model-only false reject.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Ring
meta import Mathlib.Data.Nat.Basic
meta import Mathlib.Tactic.NormNum.Basic
meta import Mathlib.Tactic.Ring

public section

set_option exponentiation.threshold 384
set_option maxRecDepth 8000

namespace EvmAsm.Stateless.SpecRef

/-! ## The exact Nat recurrence -/

def taylorDenominator : Nat := 11684671

def taylorResultBound : Nat := 2 ^ 256

def taylorOutputBound : Nat := taylorResultBound * taylorDenominator

def taylorWord384Bound : Nat := 2 ^ 384

def taylorWord64Bound : Nat := 2 ^ 64

def taylorNatAux (num denominator : Nat) : Nat → Nat → Nat → Nat
  | i, acc, output =>
      if acc = 0 then output
      else
        taylorNatAux num denominator (i + 1)
          (acc * num / (denominator * i)) (output + acc)
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
        exact (Nat.le_div_iff_mul_le h_den_pos).2 (by simpa [Nat.mul_comm] using h_num_ge)
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
      simp [h_old_zero, h_new_zero]
      exact Prod.Lex.right 0 h_acc_lt

def taylorExpNat (factor numerator denominator : Nat) : Nat :=
  taylorNatAux numerator denominator 1 (factor * denominator) 0 / denominator

theorem taylorNatAux_output_le (num denominator i acc output : Nat) :
    output ≤ taylorNatAux num denominator i acc output := by
  induction i, acc, output using taylorNatAux.induct num denominator with
  | case1 i output =>
      rw [taylorNatAux.eq_1]
      simp
  | case2 i acc output h_acc ih =>
      rw [taylorNatAux.eq_1, if_neg h_acc]
      exact le_trans (Nat.le_add_right output acc) ih

theorem taylorNatAux_step (num denominator i acc output : Nat) (h_acc : acc ≠ 0) :
    taylorNatAux num denominator i acc output =
      taylorNatAux num denominator (i + 1)
        (acc * num / (denominator * i)) (output + acc) := by
  rw [taylorNatAux.eq_1, if_neg h_acc]

theorem taylorNatAux_next_output_le (num denominator i acc output : Nat)
    (h_acc : acc ≠ 0) :
    output + acc ≤ taylorNatAux num denominator i acc output := by
  rw [taylorNatAux_step num denominator i acc output h_acc]
  exact taylorNatAux_output_le num denominator (i + 1)
    (acc * num / (denominator * i)) (output + acc)

/-! Increasing the numerator cannot decrease the exact recurrence.  This is
    proved against the terminating recursion itself, rather than inferred from
    a finite sample of traces: at each common state, multiplication and floor
    division are monotone, and the larger-numerator run may simply continue
    after the smaller run's accumulator has reached zero. -/

theorem taylorNatAux_mono_num
    (num₁ num₂ denominator i acc₁ acc₂ output₁ output₂ : Nat)
    (h_num : num₁ ≤ num₂) (h_acc : acc₁ ≤ acc₂)
    (h_output : output₁ ≤ output₂) :
    taylorNatAux num₁ denominator i acc₁ output₁ ≤
      taylorNatAux num₂ denominator i acc₂ output₂ := by
  induction i, acc₂, output₂ using taylorNatAux.induct num₂ denominator
    generalizing num₁ acc₁ output₁ with
  | case1 i output₂ =>
      have h_acc₁ : acc₁ = 0 := Nat.eq_zero_of_le_zero h_acc
      rw [taylorNatAux.eq_1, if_pos h_acc₁,
        taylorNatAux.eq_1, if_pos rfl]
      exact h_output
  | case2 i acc₂ output₂ h_acc₂ ih =>
      by_cases h_acc₁ : acc₁ = 0
      · rw [taylorNatAux.eq_1, if_pos h_acc₁,
          taylorNatAux_step num₂ denominator i acc₂ output₂ h_acc₂]
        exact le_trans h_output
          (le_trans (Nat.le_add_right output₂ acc₂)
            (taylorNatAux_output_le num₂ denominator (i + 1)
              (acc₂ * num₂ / (denominator * i)) (output₂ + acc₂)))
      · have h_prod : acc₁ * num₁ ≤ acc₂ * num₂ :=
          Nat.mul_le_mul h_acc h_num
        have h_acc' :
            acc₁ * num₁ / (denominator * i) ≤
              acc₂ * num₂ / (denominator * i) :=
          Nat.div_le_div_right h_prod
        have h_output' : output₁ + acc₁ ≤ output₂ + acc₂ :=
          Nat.add_le_add h_output h_acc
        rw [taylorNatAux_step num₁ denominator i acc₁ output₁ h_acc₁,
          taylorNatAux_step num₂ denominator i acc₂ output₂ h_acc₂]
        exact ih num₁ _ _ h_num h_acc' h_output'

theorem taylorExpNat_mono_num {num₁ num₂ : Nat} (h_num : num₁ ≤ num₂) :
    taylorExpNat 1 num₁ taylorDenominator ≤
      taylorExpNat 1 num₂ taylorDenominator := by
  unfold taylorExpNat
  apply Nat.div_le_div_right
  exact taylorNatAux_mono_num num₁ num₂ taylorDenominator 1
    taylorDenominator taylorDenominator 0 0 h_num le_rfl le_rfl

theorem taylorOutputBound_mul_word64_lt_word384 :
    taylorOutputBound * taylorWord64Bound < taylorWord384Bound := by
  rw [taylorOutputBound, taylorResultBound, taylorWord64Bound,
    taylorWord384Bound]
  have h_den_lt : taylorDenominator < 2 ^ 24 := by
    decide
  have h_left : 2 ^ 256 * taylorDenominator < 2 ^ 256 * 2 ^ 24 :=
    Nat.mul_lt_mul_of_pos_left h_den_lt
      (show 0 < 2 ^ 256 from Nat.pow_pos (by decide))
  calc
    (2 ^ 256 * taylorDenominator) * 2 ^ 64 <
        (2 ^ 256 * 2 ^ 24) * 2 ^ 64 :=
      Nat.mul_lt_mul_of_pos_right h_left
        (show 0 < 2 ^ 64 from Nat.pow_pos (by decide))
    _ < 2 ^ 384 := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      exact Nat.pow_lt_pow_right (by decide) (by decide)

theorem taylorNatAux_product_lt_word384
    (num denominator i acc output : Nat)
    (h_num : num < taylorWord64Bound)
    (h_fit : taylorNatAux num denominator i acc output < taylorOutputBound)
    (h_acc : acc ≠ 0) :
    acc * num < taylorWord384Bound := by
  have h_acc_le : acc ≤ taylorNatAux num denominator i acc output := by
    rw [taylorNatAux_step num denominator i acc output h_acc]
    exact le_trans (Nat.le_add_left acc output)
      (taylorNatAux_output_le num denominator (i + 1)
        (acc * num / (denominator * i)) (output + acc))
  by_cases h_num_zero : num = 0
  · rw [h_num_zero]
    unfold taylorWord384Bound
    exact Nat.pow_pos (by decide)
  · have h_num_pos : 0 < num := Nat.pos_of_ne_zero h_num_zero
    calc
      acc * num ≤ taylorNatAux num denominator i acc output * num :=
        Nat.mul_le_mul_right num h_acc_le
      _ < taylorOutputBound * num :=
        (Nat.mul_lt_mul_right h_num_pos).2 h_fit
      _ ≤ taylorOutputBound * taylorWord64Bound :=
        Nat.mul_le_mul_left taylorOutputBound (Nat.le_of_lt h_num)
      _ < taylorWord384Bound := taylorOutputBound_mul_word64_lt_word384

/-! ## The 384-bit bounded recurrence -/

def taylor384Aux (num denominator : Nat) : Nat → Nat → Nat → Option Nat
  | i, acc, output =>
      if acc = 0 then
        if output < taylorOutputBound then some (output / denominator) else none
      else if taylorOutputBound ≤ output + acc then none
      else if taylorWord384Bound ≤ acc * num then none
      else
        taylor384Aux num denominator (i + 1)
          (acc * num / (denominator * i)) (output + acc)
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
        exact (Nat.le_div_iff_mul_le h_den_pos).2 (by simpa [Nat.mul_comm] using h_num_ge)
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
      simp [h_old_zero, h_new_zero]
      exact Prod.Lex.right 0 h_acc_lt

def taylorExp384 (numerator : Nat) : Option Nat :=
  taylor384Aux numerator taylorDenominator 1 taylorDenominator 0

/-! `taylorExpNat` is total, like the reference `Uint` function.  Thus
`none` is a bounded-representation outcome, not a reference-level exception:
the reference returns an arbitrary-precision `Uint` for every input.  Under
the `numerator < 2^64` premise, the iff lemmas below identify it exactly with
a result outside the 256-bit output range, which is a downstream U256
representability failure rather than a failure of `taylor_exponential` itself.
Without that premise the 384-bit intermediate guard is an additional possible
source of `none`; if it fired on a result that still fit, that would be a
model-only false rejection and not a reference failure.

The sizing audit follows this exact guard order (output bound before product
bound), rather than treating a single boundary trace as a domain bound.  Across
the full U64 domain it found a maximum of 495 nonzero states, attained at
`2073394370`, and a maximum pre-division product of 377 bits, attained at
`4033036207587913316` in state `i = 9`.  The latter is the domain maximum from
the monotone fixed-state prefix analysis; U64_MAX reaches only `i = 8` and has
359 bits.  These are sizing measurements, while the exactness claims below
remain kernel-checked theorems.
-/

theorem taylor384Aux_some_of_nat_lt
    (num denominator i acc output : Nat)
    (h_num : num < taylorWord64Bound)
    (h_fit : taylorNatAux num denominator i acc output < taylorOutputBound) :
    taylor384Aux num denominator i acc output =
      some (taylorNatAux num denominator i acc output / denominator) := by
  revert h_fit
  induction i, acc, output using taylor384Aux.induct num denominator with
  | case1 i output h_output =>
      intro h_fit
      have h_exact : taylorNatAux num denominator i 0 output = output := by
        rw [taylorNatAux.eq_1]
        simp
      rw [taylor384Aux.eq_1, if_pos rfl, if_pos h_output, h_exact]
  | case2 i output h_output =>
      intro h_fit
      have h_exact : taylorNatAux num denominator i 0 output = output := by
        rw [taylorNatAux.eq_1]
        simp
      exfalso
      apply h_output
      simpa [h_exact] using h_fit
  | case3 i acc output h_acc h_output =>
      intro h_fit
      exfalso
      exact (Nat.not_lt_of_ge h_output)
        (lt_of_le_of_lt (taylorNatAux_next_output_le num denominator
          i acc output h_acc) h_fit)
  | case4 i acc output h_acc h_output h_product =>
      intro h_fit
      exfalso
      exact (Nat.not_lt_of_ge h_product)
        (taylorNatAux_product_lt_word384 num denominator i acc output
          h_num h_fit h_acc)
  | case5 i acc output h_acc h_output h_product ih =>
      intro h_fit
      have h_step := taylorNatAux_step num denominator i acc output h_acc
      have h_next_fit :
          taylorNatAux num denominator (i + 1)
              (acc * num / (denominator * i)) (output + acc) <
            taylorOutputBound := by
        simpa [h_step] using h_fit
      have h_next_output_le := taylorNatAux_output_le num denominator
        (i + 1) (acc * num / (denominator * i)) (output + acc)
      have h_output_lt : output + acc < taylorOutputBound :=
        lt_of_le_of_lt h_next_output_le h_next_fit
      have h_not_output : ¬taylorOutputBound ≤ output + acc :=
        Nat.not_le_of_gt h_output_lt
      rw [taylor384Aux.eq_1]
      simp only [h_acc, if_false, h_not_output, h_product]
      rw [ih h_next_fit]
      simp [h_step]

theorem taylor384Aux_some_implies_nat_lt
    (num i acc output result : Nat)
    (h_some : taylor384Aux num taylorDenominator i acc output = some result) :
    taylorNatAux num taylorDenominator i acc output / taylorDenominator <
        taylorResultBound ∧
      result = taylorNatAux num taylorDenominator i acc output /
        taylorDenominator := by
  revert h_some
  induction i, acc, output using taylor384Aux.induct num taylorDenominator with
  | case1 i output h_output =>
      intro h_some
      rw [taylor384Aux.eq_1, if_pos rfl, if_pos h_output] at h_some
      have h_exact : taylorNatAux num taylorDenominator i 0 output = output := by
        rw [taylorNatAux.eq_1]
        simp
      constructor
      · apply (Nat.div_lt_iff_lt_mul (by norm_num [taylorDenominator])).2
        simpa [taylorOutputBound, h_exact] using h_output
      · simpa [h_exact] using h_some.symm
  | case2 i output h_output =>
      intro h_some
      rw [taylor384Aux.eq_1, if_pos rfl, if_neg h_output] at h_some
      cases h_some
  | case3 i acc output h_acc h_output =>
      intro h_some
      rw [taylor384Aux.eq_1, if_neg h_acc, if_pos h_output] at h_some
      cases h_some
  | case4 i acc output h_acc h_output h_product =>
      intro h_some
      rw [taylor384Aux.eq_1, if_neg h_acc, if_neg h_output, if_pos h_product] at h_some
      cases h_some
  | case5 i acc output h_acc h_output h_product ih =>
      intro h_some
      have h_next_some :
          taylor384Aux num taylorDenominator (i + 1)
              (acc * num / (taylorDenominator * i)) (output + acc) = some result := by
        rw [taylor384Aux.eq_1, if_neg h_acc, if_neg h_output, if_neg h_product] at h_some
        exact h_some
      have h_next := ih h_next_some
      have h_step := taylorNatAux_step num taylorDenominator i acc output h_acc
      simpa [h_step] using h_next

theorem taylorExp384_some_of_lt
    (numerator : Nat)
    (h_num : numerator < taylorWord64Bound)
    (h_result : taylorExpNat 1 numerator taylorDenominator < taylorResultBound) :
    taylorExp384 numerator =
      some (taylorExpNat 1 numerator taylorDenominator) := by
  unfold taylorExp384 taylorExpNat at *
  apply taylor384Aux_some_of_nat_lt numerator taylorDenominator 1
    taylorDenominator 0 h_num
  apply (Nat.div_lt_iff_lt_mul (by norm_num [taylorDenominator])).1
    h_result

theorem taylorExp384_none_of_ge
    (numerator : Nat)
    (h_result : taylorResultBound ≤
      taylorExpNat 1 numerator taylorDenominator) :
    taylorExp384 numerator = none := by
  unfold taylorExp384 taylorExpNat at *
  cases h_value : taylor384Aux numerator taylorDenominator 1
      taylorDenominator 0 with
  | none => rfl
  | some result =>
      have h_some := taylor384Aux_some_implies_nat_lt numerator
        1 taylorDenominator 0 result h_value
      exact False.elim ((Nat.not_lt_of_ge h_result) h_some.1)

theorem taylorExp384_some_iff_lt
    (numerator : Nat)
    (h_num : numerator < taylorWord64Bound) :
    (∃ result, taylorExp384 numerator = some result) ↔
      taylorExpNat 1 numerator taylorDenominator < taylorResultBound := by
  constructor
  · rintro ⟨result, h_some⟩
    have h_aux :
        taylor384Aux numerator taylorDenominator 1 taylorDenominator 0 =
          some result := by
      simpa [taylorExp384] using h_some
    have h_lt := taylor384Aux_some_implies_nat_lt numerator
      1 taylorDenominator 0 result h_aux
    simpa [taylorExpNat] using h_lt.1
  · intro h_result
    exact ⟨taylorExpNat 1 numerator taylorDenominator,
      taylorExp384_some_of_lt numerator h_num h_result⟩

theorem taylorExp384_none_iff_ge
    (numerator : Nat)
    (h_num : numerator < taylorWord64Bound) :
    taylorExp384 numerator = none ↔
      taylorResultBound ≤ taylorExpNat 1 numerator taylorDenominator := by
  constructor
  · intro h_none
    by_contra h_not_ge
    have h_result :
        taylorExpNat 1 numerator taylorDenominator < taylorResultBound :=
      Nat.lt_of_not_ge h_not_ge
    have h_some := taylorExp384_some_of_lt numerator h_num h_result
    rw [h_none] at h_some
    cases h_some
  · exact taylorExp384_none_of_ge numerator

theorem taylorExp384_exact_iff_lt
    (numerator : Nat)
    (h_num : numerator < taylorWord64Bound) :
    taylorExp384 numerator =
        some (taylorExpNat 1 numerator taylorDenominator) ↔
      taylorExpNat 1 numerator taylorDenominator < taylorResultBound := by
  constructor
  · intro h_some
    exact (taylorExp384_some_iff_lt numerator h_num).1 ⟨_, h_some⟩
  · exact taylorExp384_some_of_lt numerator h_num

/-! ## Concrete non-degenerate checks -/

structure TaylorState where
  i : Nat
  acc : Nat
  output : Nat

def taylorTraceStep (num denominator : Nat) (s next : TaylorState) : Prop :=
  s.acc ≠ 0 ∧
    next.i = s.i + 1 ∧
    next.acc = s.acc * num / (denominator * s.i) ∧
    next.output = s.output + s.acc

def taylorTraceValidTo (num denominator : Nat) (s : TaylorState) :
    List TaylorState → Prop
  | [] => s.acc = 0
  | next :: rest =>
      taylorTraceStep num denominator s next ∧
        taylorTraceValidTo num denominator next rest

def taylorTraceFinal (s : TaylorState) : List TaylorState → TaylorState
  | [] => s
  | next :: rest => taylorTraceFinal next rest

theorem taylorNatAux_eq_trace
    (num denominator : Nat) (s : TaylorState) (trace : List TaylorState)
    (h_trace : taylorTraceValidTo num denominator s trace) :
    taylorNatAux num denominator s.i s.acc s.output =
      (taylorTraceFinal s trace).output := by
  induction trace generalizing s with
  | nil =>
      simp only [taylorTraceValidTo] at h_trace
      rw [taylorNatAux.eq_1, if_pos h_trace]
      simp [taylorTraceFinal]
  | cons next rest ih =>
      simp only [taylorTraceValidTo] at h_trace
      rcases h_trace with ⟨h_step, h_rest⟩
      rcases h_step with ⟨h_acc, h_i, h_next_acc, h_next_output⟩
      rw [taylorNatAux_step num denominator s.i s.acc s.output h_acc]
      simpa [taylorTraceFinal, h_i, h_next_acc, h_next_output] using
        ih (s := next) h_rest

def taylorTrace10D : List TaylorState :=
[
  { i := 2, acc := 116846710, output := 11684671 },
  { i := 3, acc := 584233550, output := 128531381 },
  { i := 4, acc := 1947445166, output := 712764931 },
  { i := 5, acc := 4868612915, output := 2660210097 },
  { i := 6, acc := 9737225830, output := 7528823012 },
  { i := 7, acc := 16228709716, output := 17266048842 },
  { i := 8, acc := 23183871022, output := 33494758558 },
  { i := 9, acc := 28979838777, output := 56678629580 },
  { i := 10, acc := 32199820863, output := 85658468357 },
  { i := 11, acc := 32199820863, output := 117858289220 },
  { i := 12, acc := 29272564420, output := 150058110083 },
  { i := 13, acc := 24393803683, output := 179330674503 },
  { i := 14, acc := 18764464371, output := 203724478186 },
  { i := 15, acc := 13403188836, output := 222488942557 },
  { i := 16, acc := 8935459224, output := 235892131393 },
  { i := 17, acc := 5584662015, output := 244827590617 },
  { i := 18, acc := 3285095302, output := 250412252632 },
  { i := 19, acc := 1825052945, output := 253697347934 },
  { i := 20, acc := 960554181, output := 255522400879 },
  { i := 21, acc := 480277090, output := 256482955060 },
  { i := 22, acc := 228703376, output := 256963232150 },
  { i := 23, acc := 103956080, output := 257191935526 },
  { i := 24, acc := 45198295, output := 257295891606 },
  { i := 25, acc := 18832622, output := 257341089901 },
  { i := 26, acc := 7533048, output := 257359922523 },
  { i := 27, acc := 2897326, output := 257367455571 },
  { i := 28, acc := 1073083, output := 257370352897 },
  { i := 29, acc := 383243, output := 257371425980 },
  { i := 30, acc := 132152, output := 257371809223 },
  { i := 31, acc := 44050, output := 257371941375 },
  { i := 32, acc := 14209, output := 257371985425 },
  { i := 33, acc := 4440, output := 257371999634 },
  { i := 34, acc := 1345, output := 257372004074 },
  { i := 35, acc := 395, output := 257372005419 },
  { i := 36, acc := 112, output := 257372005814 },
  { i := 37, acc := 31, output := 257372005926 },
  { i := 38, acc := 8, output := 257372005957 },
  { i := 39, acc := 2, output := 257372005965 },
  { i := 40, acc := 0, output := 257372005967 }
]

def taylorTraceMeasured : List TaylorState :=
[
  { i := 2, acc := 2073394371, output := 11684671 },
  { i := 3, acc := 183957435245, output := 2085079042 },
  { i := 4, acc := 10880817290179, output := 186042514287 },
  { i := 5, acc := 482688501056996, output := 11066859804466 },
  { i := 6, acc := 17130197692994574, output := 493755360861462 },
  { i := 7, acc := 506613258099324260, output := 17623953053856036 },
  { i := 8, acc := 12842333315126032334, output := 524237211153180296 },
  { i := 9, acc := 284852068214929677918, output := 13366570526279212630 },
  { i := 10, acc := 5616196494673740705579, output := 298218638741208890548 },
  { i := 11, acc := 99656979631574269061243, output := 5914415133414949596127 },
  { i := 12, acc := 1607609122312065901945149, output := 105571394764989218657370 },
  { i := 13, acc := 23771940925637301116380811, output := 1713180517077055120602519 },
  { i := 14, acc := 324479090879382514343503087, output := 25485121442714356236983330 },
  { i := 15, acc := 4112672311908905175211706620, output := 349964212322096870580486417 },
  { i := 16, acc := 48651728526942009492931501104, output := 4462636524231002045792193037 },
  { i := 17, acc := 539564935478188069683737451174, output := 53114365051173011538723694141 },
  { i := 18, acc := 5631968585213574147256777611635, output := 592679300529361081222461145315 },
  { i := 19, acc := 55520471423298755502987764394539, output := 6224647885742935228479238756950 },
  { i := 20, acc := 518519353146456394433356788013392, output := 61745119309041690731467003151489 },
  { i := 21, acc := 4600450915855584752087062181304066, output := 580264472455498085164823791164881 },
  { i := 22, acc := 38872863482325991662763181365865430, output := 5180715388311082837251885972468947 },
  { i := 23, acc := 313537346684644153557200597377995472, output := 44053578870637074500015067338334377 },
  { i := 24, acc := 2418949875938784130167149708631349684, output := 357590925555281228057215664716329849 },
  { i := 25, acc := 17884675060251387466224977918328960470, output := 2776540801494065358224365373347679533 },
  { i := 26, acc := 126942331870839367637859283621978109147, output := 20661215861745452824449343291676640003 },
  { i := 27, acc := 866360314633302449473979808351214705510, output := 147603547732584820462308626913654749150 },
  { i := 28, acc := 5693773839241484682762955447586517290131, output := 1013963862365887269936288435264869454660 },
  { i := 29, acc := 36083412887187083618612773437308438688761, output := 6707737701607371952699243882851386744791 },
  { i := 30, acc := 220787781868854463987661580726116140770438, output := 42791150588794455571312017320159825433552 },
  { i := 31, acc := 1305927923608799671096829155995609686587580, output := 263578932457648919558973598046275966203990 },
  { i := 32, acc := 7475202134881435807921989770076450466139568, output := 1569506856066448590655802754041885652791570 },
  { i := 33, acc := 41451322283032059044878357070334117227589533, output := 9044708990947884398577792524118336118931138 },
  { i := 34, acc := 222889636298613436242444226984430128517118745, output := 50496031273979943443456149594452453346520671 },
  { i := 35, acc := 1163258902740739590030218051121557499187964709, output := 273385667572593379685900376578882581863639416 },
  { i := 36, acc := 5897579000135637875703014969901353309254891298, output := 1436644570313332969716118427700440081051604125 },
  { i := 37, acc := 29069441829216148538107531621563082227540571511, output := 7334223570448970845419133397601793390306495423 },
  { i := 38, acc := 139412076281703923725440434937996038205058072411, output := 36403665399665119383526665019164875617847066934 },
  { i := 39, acc := 651001853561878153146436466105740543663593075480, output := 175815741681369043108967099957160913822905139345 },
  { i := 40, acc := 2961986293915938027764132295654653190861976345639, output := 826817595243247196255403566062901457486498214825 },
  { i := 41, acc := 13139791674032708011100598419736562727975846288233, output := 3788803889159185224019535861717554648348474560464 },
  { i := 42, acc := 56868274292044228153033684105280233336758619983945, output := 16928595563191893235120134281454117376324320848697 },
  { i := 43, acc := 240262607238248733330352152746351358601941911065808, output := 73796869855236121388153818386734350713082940832642 },
  { i := 44, acc := 991478169888324705127097292289679911266030726352637, output := 314059477093484854718505971133085709315024851898450 },
  { i := 45, acc := 3998489007940858704052122425656431773285715321794836, output := 1305537646981809559845603263422765620581055578251087 },
  { i := 46, acc := 15766990979644186507049422135983711039829021046116967, output := 5304026654922668263897725689079197393866770900045923 },
  { i := 47, acc := 60821400189526706821773482159272239481580553440038719, output := 21071017634566854770947147825062908433695791946162890 },
  { i := 48, acc := 229627544897586027642600307130715226917992535627999857, output := 81892417824093561592720629984335147915276345386201609 },
  { i := 49, acc := 848883655305750302401928055654598149532396979040445122, output := 311519962721679589235320937115050374833268881014201466 },
  { i := 50, acc := 3074096652881311397924692138190735193994656617745057007, output := 1160403618027429891637248992769648524365665860054646588 },
  { i := 51, acc := 10909703312988533410234995510327375885174882605270614656, output := 4234500270908741289561941130960383718360322477799703595 },
  { i := 52, acc := 37958425571334353208721022608776806520105959210725169887, output := 15144203583897274699796936641287759603535205083070318251 },
  { i := 53, acc := 129529972532828410075915103423177198824366020547303731516, output := 53102629155231627908517959250064566123641164293795488138 },
  { i := 54, acc := 433670449676624683257658216707152626893604069756604971820, output := 182632601688060037984433062673241764948007184841099219654 },
  { i := 55, acc := 1425054575743110097846376056481921852743621511142495199942, output := 616303051364684721242091279380394391841611254597704191474 },
  { i := 56, acc := 4597632286723127356591516492394639146902989780149274715182, output := 2041357627107794819088467335862316244585232765740199391416 },
  { i := 57, acc := 14568392492332766421482837339507078972106918502198359063448, output := 6638989913830922175679983828256955391488222545889474106598 },
  { i := 58, acc := 45352601529112738641305120236263892247806490473961499609774, output := 21207382406163688597162821167764034363595141048087833170046 },
  { i := 59, acc := 138752123100174615931561876344668456790528663795227355864472, output := 66559983935276427238467941404027926611401631522049332779820 },
  { i := 60, acc := 417304484668237582514597893157151654143726843061039510530738, output := 205312107035451043170029817748696383401930295317276688644292 },
  { i := 61, acc := 1234147955476851688958430090444277603957843658819262334590660, output := 622616591703688625684627710905848037545657138378316199175030 },
  { i := 62, acc := 3590069197535846376662226389087296542662759545185736741742970, output := 1856764547180540314643057801350125641503500797197578533765690 },
  { i := 63, acc := 10274875222681550935674619866050056135119150762283981087503937, output := 5446833744716386691305284190437422184166260342383315275508660 },
  { i := 64, acc := 28940193699465612621432095606059304339427302557912509380338444, output := 15721708967397937626979904056487478319285411104667296363012597 },
  { i := 65, acc := 80239254693341476673455147170405454598305071136697091294438280, output := 44661902666863550248411999662546782658712713662579805743351041 },
  { i := 66, acc := 219047830357475716446155042019247330839658742948290404940286470, output := 124901157360205026921867146832952237257017784799276897037789321 },
  { i := 67, acc := 588925618669152176733983727439521675280896501052301084454621187, output := 343948987717680743368022188852199568096676527747567301978075791 },
  { i := 68, acc := 1559735908320962266400829355609868747145778148414745465662326070, output := 932874606386832920102005916291721243377573028799868386432696978 },
  { i := 69, acc := 4070123473233152604582234299125071306194644863868748638962208365, output := 2492610514707795186502835271901589990523351177214613852095023048 },
  { i := 70, acc := 10467040874863088498070470751137125678440240321711928327935761288, output := 6562733987940947791085069571026661296717996041083362491057231413 },
  { i := 71, acc := 26533302393694198746832077705822389290815964098756569035371763696, output := 17029774862804036289155540322163786975158236362795290818992992701 },
  { i := 72, acc := 66312955494227904134528512477185377249725093912104300302619204374, output := 43563077256498235035987618027986176265974200461551859854364756397 },
  { i := 73, acc := 163429824527871767757920522667404046712487515355711466630492319221, output := 109876032750726139170516130505171553515699294373656160156983960771 },
  { i := 74, acc := 397259124157527736909805997824893425128438847910760769694460013103, output := 273305857278597906928436653172575600228186809729367626787476279992 },
  { i := 75, acc := 952593442385775770602264133174615805123924882155544124587283284241, output := 670564981436125643838242650997469025356625657640128396481936293095 },
  { i := 76, acc := 2253781193376267981911140083823718294885756798330785732705006824442, output := 1623158423821901414440506784172084830480550539795672521069219577336 },
  { i := 77, acc := 5262154375515192555184038796588784062858989212328331860243120140858, output := 3876939617198169396351646867995803125366307338126458253774226401778 },
  { i := 78, acc := 12126578601872688050176514491922069852527007614685483009284984310042, output := 9139093992713361951535685664584587188225296550454790114017346542636 },
  { i := 79, acc := 27587294424982078000461471035867666237614833158455975449688530233070, output := 21265672594586050001712200156506657040752304165140273123302330852678 },
  { i := 80, acc := 61965141404773808006677013146136981334134099235978196495565025505043, output := 48852967019568128002173671192374323278367137323596248572990861085748 },
  { i := 81, acc := 137443081823695598756352285691541312430968008764466489142737149324345, output := 110818108424341936008850684338511304612501236559574445068555886590791 },
  { i := 82, acc := 301094825657196688287127205712431396263649635707343960459897533242520, output := 248261190248037534765202970030052617043469245324040934211293035915136 },
  { i := 83, acc := 651560677602949749535796525463934654357605483445046235465249901555747, output := 549356015905234223052330175742484013307118881031384894671190569157656 },
  { i := 84, acc := 1392971402093074469140138668837001621747761156593094472966745559815634, output := 1200916693508183972588126701206418667664724364476431130136440470713403 },
  { i := 85, acc := 2942580419765102645613720181446509296391990395683463461414391224022298, output := 2593888095601258441728265370043420289412485521069525603103186030529037 },
  { i := 86, acc := 6142919746589639152167520581231186430936459144681353019424564091937339, output := 5536468515366361087341985551489929585804475916752989064517577254551335 },
  { i := 87, acc := 12674820476912636983586752272064340074228831318035549887041873212638229, output := 11679388261956000239509506132721116016740935061434342083942141346488674 },
  { i := 88, acc := 25851633523254130783173828649134697143082650884019371726360280515533704, output := 24354208738868637223096258404785456090969766379469891970984014559126903 },
  { i := 89, acc := 52127961875191798849817887893496623090490008360958110292528442858332549, output := 50205842262122768006270087053920153234052417263489263697344295074660607 },
  { i := 90, acc := 103931253392908297902763625655870895058015222349866686372877280484931451, output := 102333804137314566856087974947416776324542425624447373989872737932993156 },
  { i := 91, acc := 204912797246001207898585160352809341131185636722512559998904319867024469, output := 206265057530222864758851600603287671382557647974314060362750018417924607 },
  { i := 92, acc := 399570223014036050672128993411842005647727347492149697271616750989838467, output := 411177854776224072657436760956097012513743284696826620361654338284949076 },
  { i := 93, acc := 770674013485848813163047981118771559811836501553657769274696876427132008, output := 810748077790260123329565754367939018161470632188976317633271089274787543 },
  { i := 94, acc := 1470459925278590570950712261559155575829599826778736384089258110844907880, output := 1581422091276108936492613735486710577973307133742634086907967965701919551 },
  { i := 95, acc := 2775816583142017449771515177155474434982776803668130010153275001388048852, output := 3051882016554699507443325997045866153802906960521370470997226076546827431 },
  { i := 96, acc := 5184806909042231010400436790403452510178051502533238377148797172036672911, output := 5827698599696716957214841174201340588785683764189500481150501077934876283 },
  { i := 97, acc := 9583558111386981907611679953344272998758544593293523814574998772181907727, output := 11012505508738947967615277964604793098963735266722738858299298249971549194 },
  { i := 98, acc := 17531556385056244978686133054256464801798478217048570772232710430644497110, output := 20596063620125929875226957917949066097722279860016262672874297022153456921 },
  { i := 99, acc := 31743866468774211727349171222857631086557935092555323012642231466993481101, output := 38127620005182174853913090972205530899520758077064833445107007452797954031 },
  { i := 100, acc := 56897090066477918351444771439373409456640213529978826070584414591365958592, output := 69871486473956386581262262195063161986078693169620156457749238919791435132 },
  { i := 101, acc := 100961427386458148206041221716707637668596734392689479852652910718725793602, output := 126768576540434304932707033634436571442718906699598982528333653511157393724 },
  { i := 102, acc := 177377910515551449456317103896787333291877111082846030891910134244057008449, output := 227730003926892453138748255351144209111315641092288462380986564229883187326 },
  { i := 103, acc := 308577878845129391725394895762568922885375997038790558403632519385140718428, output := 405107914442443902595065359247931542403192752175134493272896698473940195775 },
  { i := 104, acc := 531609815649832527341867873510451791476026786144748764737323234350022695972, output := 713685793287573294320460255010500465288568749213925051676529217859080914203 },
  { i := 105, acc := 907037156874419937161303407326697479011719154093281438837826736108467124898, output := 1245295608937405821662328128520952256764595535358673816413852452209103610175 },
  { i := 106, acc := 1532855462105022450109794198190493470749830829134530469719181845391892124714, output := 2152332765811825758823631535847649735776314689451955255251679188317570735073 },
  { i := 107, acc := 2566024312912899042739435429689573426783764096300605246971298847931927078294, output := 3685188227916848208933425734038143206526145518586485724970861033709462859787 },
  { i := 108, acc := 4255419856744179936633788952934177903894191289797649026511372203917105234502, output := 6251212540829747251672861163727716633309909614887090971942159881641389938081 },
  { i := 109, acc := 6991720952030837752860322141699588954849949229195143332251850637763238044347, output := 10506632397573927188306650116661894537204100904684739998453532085558495172583 },
  { i := 110, acc := 11382116207647083375339515593358760388725416780409417945665555212042818841224, output := 17498353349604764941166972258361483492054050133879883330705382723321733216930 },
  { i := 111, acc := 18360975733236173526367566100559348050201881062127411704951140317429011360553, output := 28880469557251848316506487851720243880779466914289301276370937935364552058154 },
  { i := 112, acc := 29352034168927819895534427869441870378503863188276530228137720667221402356496, output := 47241445290488021842874053952279591930981347976416712981322078252793563418707 },
  { i := 113, acc := 46503496534090480043639234366185450024423902216116151976282258919298152511621, output := 76593479459415841738408481821721462309485211164693243209459798920014965775203 },
  { i := 114, acc := 73025172430001886623655946885036038039486767599568847558779203263299557617509, output := 123096975993506321782047716187906912333909113380809395185742057839313118286824 },
  { i := 115, acc := 113666677656977010430692858048962675042455000778618887188788140715714266476147, output := 196122148423508208405703663072942950373395880980378242744521261102612675904333 },
  { i := 116, acc := 175388354034434704575136803266598087150568902092686420451515416165123237739753, output := 309788826080485218836396521121905625415850881758997129933309401818326942380480 },
  { i := 117, acc := 268292288301272473105661693388787109828852566195950044021801742831365251556194, output := 485177180114919923411533324388503712566419783851683550384824817983450180120233 },
  { i := 118, acc := 406900060454885610367830575546107841059746842489125614462462605237634433131705, output := 753469468416192396517195017777290822395272350047633594406626560814815431676427 },
  { i := 119, acc := 611886925568013406585314803065116687751422338954054924870128634154711969741840, output := 1160369528871078006885025593323398663455019192536759208869089166052449864808132 },
  { i := 120, acc := 912409164153138034738010069485346729558309448085201161124627786399113603870334, output := 1772256454439091413470340396388515351206441531490814133739217800207161834549972 },
  { i := 121, acc := 1349192191635756071075081002717318539284972968669787404853238402255194366515378, output := 2684665618592229448208350465873862080764750979576015294863845586606275438420306 },
  { i := 122, acc := 1978581186499031576149519802273121685475538968061671302872792799531440146931826, output := 4033857810227985519283431468591180620049723948245802699717083988861469804935684 },
  { i := 123, acc := 2877792464408994097199538154877406214071308563419079087821090288459926655799414, output := 6012438996727017095432951270864302305525262916307474002589876788392909951867510 },
  { i := 124, acc := 4151640941284460420152006126508143401397035669967870478451433290074849380337680, output := 8890231461136011192632489425741708519596571479726553090410967076852836607666924 },
  { i := 125, acc := 5941054377218321492649163238176158466657151461998868211731227219670142681550526, output := 13041872402420471612784495552249851920993607149694423568862400366927685988004604 },
  { i := 126, acc := 8433715389011383150404212791884053403760142859445763605033885973981504015093762, output := 18982926779638793105433658790426010387650758611693291780593627586597828669555130 },
  { i := 127, acc := 11877193234686056438356009799165125145599402378953418487603773369419727372895532, output := 27416642168650176255837871582310063791410901471139055385627513560579332684648892 },
  { i := 128, acc := 16594933933201851990375555897062899777652731968494412963292896707615389920554492, output := 39293835403336232694193881381475188937010303850092473873231286929999060057544424 },
  { i := 129, acc := 23005463341282786441165512766794840538248203335330366532571366404067842318693534, output := 55888769336538084684569437278538088714663035818586886836524183637614449978098916 },
  { i := 130, acc := 31645116640268223655178305368944629511012602708838916404753588815605841248273098, output := 78894232677820871125734950045332929252911239153917253369095550041682292296792450 },
  { i := 131, acc := 43194532202174289095922040708976002068676139853900472362699451201641553871266995, output := 110539349318089094780913255414277558763923841862756169773849138857288133545065548 },
  { i := 132, acc := 58509031025418880146287151656408804545753890282774810207258104834169880249714763, output := 153733881520263383876835296123253560832599981716656642136548590058929687416332543 },
  { i := 133, acc := 78652838601835209937586783309894142647808143745363431093611228624974030121291717, output := 212242912545682264023122447779662365378353871999431452343806694893099567666047306 },
  { i := 134, acc := 104936889427475822170153494934518011123089594178622338488329378852809614836183578, output := 290895751147517473960709231089556508026162015744794883437417923518073597787339023 },
  { i := 135, acc := 138959682987988166275485014999187574351689703785891486066850296955232477736500175, output := 395832640574993296130862726024074519149251609923417221925747302370883212623522601 },
  { i := 136, acc := 182650334818529668974437100440883163320899731488549016835395223052973490009541233, output := 534792323562981462406347741023262093500941313709308707992597599326115690360022776 },
  { i := 137, acc := 238312592270528628131231802199555983054653381242077121223039022311371396838447776, output := 717442658381511131380784841464145256821841045197857724827992822379089180369564009 },
  { i := 138, acc := 308668172092021944952055378233875190553334967776669377304221818829293876832644817, output := 955755250652039759512016643663701239876494426439934846051031844690460577208011785 },
  { i := 139, acc := 396897341727327056721482859156210521280177274267281201051601408037783771829598010, output := 1264423422744061704464072021897576430429829394216604223355253663519754454040656602 },
  { i := 140, acc := 506674230272179430260061320583619972748847321250420723072128044285275186934125451, output := 1661320764471388761185554881053786951710006668483885424406855071557538225870254612 },
  { i := 141, acc := 642193946103216665299102564262494050233258253251540909941813089995264669396577336, output := 2167994994743568191445616201637406924458853989734306147478983115842813412804380063 },
  { i := 142, acc := 808188229429414458089777835315035861198781276562772688639327554023738859848814441, output := 2810188940846784856744718765899900974692112242985847057420796205838078082200957399 },
  { i := 143, acc := 1009926116506485038117588791393755506784583806777517916227815684506540423764671940, output := 3618377170276199314834496601214936835890893519548619746060123759861816942049771840 },
  { i := 144, acc := 1253195977271427986930366257086398530247110730312178540967422514794489596470084806, output := 4628303286782684352952085392608692342675477326326137662287939444368357365814443780 },
  { i := 145, acc := 1544265348588870746905926628150532991565659345980212771685635736243165030740759568, output := 5881499264054112339882451649695090872922588056638316203255361959162846962284528586 },
  { i := 146, acc := 1889815256654618274797404953329274972879825179300956540408165782026264515314733559, output := 7425764612642983086788378277845623864488247402618528974940997695406011993025288154 },
  { i := 147, acc := 2296846233075753004283959866219219355257423825958068871623322565262905644527488753, output := 9315579869297601361585783231174898837368072581919485515349163477432276508340021713 },
  { i := 148, acc := 2772553998085125523794625094479687479052184012573910847097078815014376381576685225, output := 11612426102373354365869743097394118192625496407877554386972486042695182152867510466 },
  { i := 149, acc := 3324173815815311683389821698034930385303576974810046041118064870883698980390197880, output := 14384980100458479889664368191873805671677680420451465234069564857709558534444195691 },
  { i := 150, acc := 3958793808369209700372882394664848979117438430894699017524083418939777152728519367, output := 17709153916273791573054189889908736056981257395261511275187629728593257514834393571 },
  { i := 151, acc := 4683139016478582399379911771096278366113000180924301840518895749690153156765086694, output := 21667947724643001273427072284573585036098695826156210292711713147533034667562912938 },
  { i := 152, acc := 5503329663768591843172550944538074664331086738309147955803480733301446770177822920, output := 26351086741121583672806984055669863402211696007080512133230608897223187824327999632 },
  { i := 153, acc := 6424618848362999071621318125460439176319234677730503218461614397139238406457367087, output := 31854416404890175515979535000207938066542782745389660089034089630524634594505822552 },
  { i := 154, acc := 7451116661423215003958217529163254304636193629569867008175547726484131908638582009, output := 38279035253253174587600853125668377242862017423120163307495704027663873000963189639 },
  { i := 155, acc := 8585509414822654331246107430127244187090890319737904209873069072265843178569043223, output := 45730151914676389591559070654831631547498211052690030315671251754148004909601771648 },
  { i := 156, acc := 9828784138312382124096714493763834747061796497100131354113449586203343079213287802, output := 54315661329499043922805178084958875734589101372427934525544320826413848088170814871 },
  { i := 157, acc := 11179969666849982963161599133711852909752190386345807678709684870638771746674875952, output := 64144445467811426046901892578722710481650897869528065879657770412617191167384102673 },
  { i := 158, acc := 12635906373334751579922279220561617092122472849703778675238355690785883517248605080, output := 75324415134661409010063491712434563391403088255873873558367455283255962914058978625 },
  { i := 159, acc := 14191056816577965789913446122183610755928805371127619894924479472689327325164229737, output := 87960321507996160589985770932996180483525561105577652233605810974041846431307583705 },
  { i := 160, acc := 15837369196466991297351527665534208254826436171166669579833532686214088401757015201, output := 102151378324574126379899217055179791239454366476705272128530290446731173756471813442 },
  { i := 161, acc := 17564204494612777738476036611326817686768238029170742809983579013821185141359233513, output := 117988747521041117677250744720713999494280802647871941708363823132945262158228828643 },
  { i := 162, acc := 19358336521021650193043265500466560274663166157450330984774028297251853709609239613, output := 135552952015653895415726781332040817181049040677042684518347402146766447299588062156 },
  { i := 163, acc := 21204031816192413034869492132636834828466119494303672732830774599249485755141942861, output := 154911288536675545608770046832507377455712206834493015503121430444018301009197301769 },
  { i := 164, acc := 23083213544547967644148827203138847427785826091443546181291929032781215258189351643, output := 176115320352867958643639538965144212284178326328796688235952205043267786764339244630 },
  { i := 165, acc := 24975710269200663161991023407588809736277013146991316248697384535301685989249480412, output := 199198533897415926287788366168283059711964152420240234417244134076049002022528596273 },
  { i := 166, acc := 26859586964155495312873177685079037515249163707170101230469153250554932063332424217, output := 224174244166616589449779389575871869448241165567231550665941518611350688011778076685 },
  { i := 167, acc := 28711551969915228410799840116096626596439870217700609746743391889736927096801753150, output := 251033831130772084762652567260950906963490329274401651896410671861905620075110500902 },
  { i := 168, acc := 30507430021509672690602519673696593457030291235061234030807109252935095829555928131, output := 279745383100687313173452407377047533559930199492102261643154063751642547171912254052 },
  { i := 169, acc := 32222688169965103098155006476240004672871362944576519099146621097387237254072347486, output := 310252813122196985864054927050744127016960490727163495673961173004577643001468182183 },
  { i := 170, acc := 33832998568765072267805239181577709669748313349868721457857706326232227818466519642, output := 342475501292162088962209933526984131689831853671740014773107794101964880255540529669 },
  { i := 171, acc := 35314819876867915368613433004958512652189110636220314864154362893250577815910461149, output := 376308499860927161230015172708561841359580167021608736230965500428197108074007049311 },
  { i := 172, acc := 36645977579908022671758901451355062098416662359471762957506630965129227575324182074, output := 411623319737795076598628605713520354011769277657829051095119863321447685889917510460 },
  { i := 173, acc := 37806222951566747352730335673154008078445681122160030570573727231468396212526500911, output := 448269297317703099270387507164875416110185940017300814052626494286576913465241692534 },
  { i := 174, acc := 38777750720273877838657422232524393833733597633013051637307612357915791583280631144, output := 486075520269269846623117842838029424188631621139460844623200221518045309677768193445 },
  { i := 175, acc := 39545656772915800405728914568598962866863710585751640020219721008120967766762582158, output := 524853270989543724461775265070553818022365218772473896260507833875961101261048824589 },
  { i := 176, acc := 40098319364850700946172662636847875533236538197375036170743652441942810544407395559, output := 564398927762459524867504179639152780889228929358225536280727554884082069027811406747 },
  { i := 177, acc := 40427690212109435456271362198175168946640967444928821979834871929595459885538448526, output := 604497247127310225813676842276000656422465467555600572451471207326024879572218802306 },
  { i := 178, acc := 40529485371337113632649434232744310836188316670681836921670381700266016078726667279, output := 644924937339419661269948204474175825369106435000529394431306079255620339457757250832 },
  { i := 179, acc := 40403269785397772335446965618894545332001986404006371765624168033194062709287209695, output := 685454422710756774902597638706920136205294751671211231352976460955886355536483918111 },
  { i := 180, acc := 40052433584050753838158334715392749491846046751636698772864946030277742251119838355, output := 725857692496154547238044604325814681537296738075217603118600628989080418245771127806 },
  { i := 181, acc := 39484062465744976847750230577798712066911665593250034963985809861672930452623090206, output := 765910126080205301076202939041207431029142784826854301891465575019358160496890966161 },
  { i := 182, acc := 38708708537210759263613709329728959401786698152169997262887620283817248669321156804, output := 805394188545950277923953169619006143096054450420104336855451384881031090949514056367 },
  { i := 183, acc := 37740071656506689145633987555472665703484349018529393494515022863251520714654873117, output := 844102897083161037187566878948735102497841148572274334118339005164848339618835213171 },
  { i := 184, acc := 36594604443643526563273218906351737682957171350890634268860359040121371051271746294, output := 881842968739667726333200866504207768201325497590803727612854028028099860333490086288 },
  { i := 185, acc := 35291056557934673699227327789713469122657620748799443848862162442881181815097184182, output := 918437573183311252896474085410559505884282668941694361881714387068221231384761832582 },
  { i := 186, acc := 33849975502260154690358356011936044163401276683907036226125564304631187026309276533, output := 953728629741245926595701413200272975006940289690493805730576549511102413199859016764 },
  { i := 187, acc := 32293182056702085819066754684550254737344545370057085626660255550539931330009382243, output := 987578605243506081286059769212209019170341566374400841956702113815733600226168293297 },
  { i := 188, acc := 30643238468810108560735764707088915159456966003194317780689261900910912052981784370, output := 1019871787300208167105126523896759273907686111744457927583362369366273531556177675540 },
  { i := 189, acc := 28922926779790749085088564653702046298255756353755705625310984650495747087135406812, output := 1050515025769018275665862288603848189067143077747652245364051631267184443609159459910 },
  { i := 190, acc := 27154753228044713753327277377223537725426564193416094689676643950527978550776428346, output := 1079437952548809024750950853257550235365398834101407950989362615917680190696294866722 },
  { i := 191, acc := 25360492657396123083624537443202712127622313556885582914742943476158191047321555877, output := 1106592705776853738504278130634773773090825398294824045679039259868208169247071295068 },
  { i := 192, acc := 23560784402862686805783790853646747114050742271465924924440256029987088822307031448, output := 1131953198434249861587902668077976485218447711851709628593782203344366360294392850945 },
  { i := 193, acc := 21774788380345395078699727884486635974074006178171563167676331370736193049623349399, output := 1155513982837112548393686458931623232332498454123175553518222459374353449116699882393 },
  { i := 194, acc := 20019907219775179310310053654724622951241541824987707719966978326687794009819336961, output := 1177288771217457943472386186816109868306572460301347116685898790745089642166323231792 },
  { i := 195, acc := 18311577399945848987498292188156995747747890739367552551814137103056703621054506132, output := 1197308678437233122782696240470834491257814002126334824405865769071777436176142568753 },
  { i := 196, acc := 16663129599972801093029253672495900649378481490671909249121049370164404980793378711, output := 1215620255837178971770194532658991487005561892865702376957679906174834139797197074885 },
  { i := 197, acc := 15085715989947422261650040669664850538898962795492097035854304965686594520317519708, output := 1232283385437151772863223786331487387654940374356374286206800955544998544777990453596 },
  { i := 198, acc := 13588300030865888808862354353460609357036629290867491257974019432303290956900612349, output := 1247369101427099195124873827001152238193839337151866383242655260510685139298307973304 },
  { i := 199, acc := 12177702603856053259695173166514518267769122732974351774656425367947155702696506488, output := 1260957401457965083933736181354612847550875966442733874500629279942988430255208585653 },
  { i := 200, acc := 10858696976666362641773993116814194553555447597795065312728633528467746852054726756, output := 1273135104061821137193431354521127365818645089175708226275285705310935585957905092141 },
  { i := 201, acc := 9634144250965540513078582521748064810828102513820782986097299362749235548909866713, output := 1283993801038487499835205347637941560372200536773503291588014338839403332809959818897 },
  { i := 202, acc := 8505160503478711516658670704026469801329535344931221557142428222031497111164450329, output := 1293627945289453040348283930159689625183028639287324074574111638202152568358869685610 },
  { i := 203, acc := 7471306803794258076393193230259148389261768476482648162179881828449861426760140229, output := 1302133105792931751864942600863716094984358174632255296131254066424184065470034135939 },
  { i := 204, acc := 6530793612759413884033046342264697055452470583016496877776543180719899444953314157, output := 1309604412596726009941335794093975243373619943108737944293433948252633926896794276168 },
  { i := 205, acc := 5680691677851096671036916097265031549855658535430775503389482542245958291000228507, output := 1316135206209485423825368840436239940429072413691754441171210491433353826341747590325 },
  { i := 206, acc := 4917142379707487642238354920365366877600921783829585303348353153771875872644263226, output := 1321815897887336520496405756533504971978928072227185216674599973975599784632747818832 },
  { i := 207, acc := 4235561479298722324935676858452297441070149805923488186960789478543491431234795570, output := 1326733040267044008138644111453870338856528994011014801977948327129371660505392082058 },
  { i := 208, acc := 3630831302242058746996133203950539805955013871799062754429483033333176024216907988, output := 1330968601746342730463579788312322636297599143816938290164909116607915151936626877628 },
  { i := 209, acc := 3097477515017853258289418964713076199478720569114363414727560841560729658345461226, output := 1334599433048584789210575921516273176103554157688737352919338599641248327960843785616 },
  { i := 210, acc := 2629827744449134672387204954168368391682066040921345343976209754709851026582016892, output := 1337696910563602642468865340480986252303032878257851716334066160482809057619189246842 },
  { i := 211, acc := 2222150323127447562361449736927005438952542405628452415479641197196654307969053844, output := 1340326738308051777141252545435154620694714944298773061678042370237518908645771263734 },
  { i := 212, acc := 1868772375893200875878664862993227855980596453505643953135698357724201391792188512, output := 1342548888631179224703613995172081626133667486704401514093522011434715562953740317578 },
  { i := 213, acc := 1564177272544894783079590686825098103782913920685811265501607035364968057743914866, output := 1344417661007072425579492660035074853989648083157907158046657709792439764345532506090 },
  { i := 214, acc := 1303082145854603828228461970616273882101206568904892185756033172867738123393825442, output := 1345981838279617320362572250721899952093430997078592969312159316827804732403276420956 },
  { i := 215, acc := 1080496706623902008857421475523678567160613640156753393674245113679056478749936597, output := 1347284920425471924190800712692516225975532203647497861497915350000672470526670246398 },
  { i := 216, acc := 891764981299415491287914770308420528998728443129536699548325472800043512238523986, output := 1348365417132095826199658134168039904542692817287654614891589595114351527005420182995 },
  { i := 217, acc := 732591860960211580889691742396558870895896593503025291871011346982474282232213581, output := 1349257182113395241690946048938348325071691545730784151591137920587151570517658706981 },
  { i := 218, acc := 599056496156105219620902147452510225109654142242082350100746645337119575260091021, output := 1349989773974355453271835740680744883942587442324287176883008931934134044799890920562 },
  { i := 219, acc := 487614615984791668481800205762191928996962025490203103784884187287394154342673053, output := 1350588830470511558491456642828197394167697096466529259233109678579471164375151011583 },
  { i := 220, acc := 395091809450181558947238046679082297197370123843329822916777996838644173646406492, output := 1351076445086496350159938443033959586096694058492019462336894562766758558529493684636 },
  { i := 221, acc := 318669700492135476724243728456260996081095670628612066625221392471423233564418702, output := 1351471536895946531718885681080638668393891428615862792159811340763597202703140091128 },
  { i := 222, acc := 255866792529877490022545249858497486035238339418117376913112869422124711883301802, output := 1351790206596438667195609924809094929389972524286491404226436562156068625936704509830 },
  { i := 223, acc := 204515570036844490773291038322117061162199726814064011501696423169323434419209148, output := 1352046073388968544685632470058953426876007762625909521603349675025490750648587811632 },
  { i := 224, acc := 162737237859729592595130011419097568400739320694293770263259410536785707466809281, output := 1352250588959005389176405761097275543937169962352723585614851371448660074083007020780 },
  { i := 225, acc := 128915265858963019976613043341725018334262310334194825442441873019447863379743056, output := 1352413326196865118769000891108694641505570701673417879385114630859196859790473830061 },
  { i := 226, acc := 101668696845234203006151311200769579009068574900634887800030794006654805717312608, output := 1352542241462724081788977504152036366523904963983752074210557072732216307653853573117 },
  { i := 227, acc := 79825977304891522901654884927449832282622408752825333237009829010373653552133926, output := 1352643910159569315991983655463237136102914032558652709098357103526222962459570885725 },
  { i := 228, acc := 62399888487785186253310102734078561817803849760878293061203160864561132782824569, output := 1352723736136874207514885310348164585935196654967405534431594113355233336113123019651 },
  { i := 229, acc := 48563993582974180984041514480385860808579376330620326457339673065462743729261778, output := 1352786136025361992701138620450898664497014458817166412724655316516097897245905844220 },
  { i := 230, acc := 37630876772970886307863901104173836598453640780214563126402473987926704727005194, output := 1352834700018944966882122661965379050357823038193497033051112656189163359989635105998 },
  { i := 231, acc := 29032332404407554143077521258963882795006107499509743543673978477420899325037147, output := 1352872330895717937768430525866483224194421491834277247614239058663151286694362111192 },
  { i := 232, acc := 22301566733192802505129137886963832064915619322607066942147592154486657178700129, output := 1352901363228122345322573603387742188077216497941776757357782732641628707593687148339 },
  { i := 233, acc := 17057399291109994915210091510918245116712636350604110247884851186769724354995409, output := 1352923664794855538125078732525629151909281413561099364424724880233783194250865848468 },
  { i := 234, acc := 12990393934748048203895310566150743087485358911436149789764691939819050820757272, output := 1352940722194146648119993942617140070154398126197449968534972765084969963975220843877 },
  { i := 235, acc := 9850808815358503903746395232816258497648751119537462818912230399679419684863316, output := 1352953712588081396168197837927706220897485611556361404684762529776909783026041601149 },
  { i := 236, acc := 7438227454407683198512657505395167280716010111071900165265775681569282134101873, output := 1352963563396896754672101584322939037155983260307480942147581442007309462445726464465 },
  { i := 237, acc := 5592717439836473004669681620176874228027571631980503786968685194588051688040932, output := 1352971001624351162355300096980444432323263976317592014047746707782991031727860566338 },
  { i := 238, acc := 4187356706771807559739371636131097822357936685369583224971195612957372649149415, output := 1352976594341790998828304766662064609197492003889223994551533676468185619779548607270 },
  { i := 239, acc := 3121967861374111279461301660274747584964096658186434963844993621692781775778888, output := 1352980781698497770635864506033700740295314361825909364134758647663798577152197756685 },
  { i := 240, acc := 2317906714268674144006562844683276398349592018861108416150473148746963563315009, output := 1352983903666359144747143967335361015042899325922567550569722492657420269933973535573 },
  { i := 241, acc := 1713760537869007448525383808846669196681988229868698635469752249050130136141417, output := 1352986221573073413421287973898205698319297675514586411678138643130569016897536850582 },
  { i := 242, acc := 1261823240833453117641636430572290098064906329622857011272007769711916582506205, output := 1352987935333611282428736499282014544988494357502816280376774112882818067027672991999 },
  { i := 243, acc := 925227606740524338852657939399929181463974996284548058454747914331220487133913, output := 1352989197156852115881854140918445117278592422409145903233785384890587778944255498204 },
  { i := 244, acc := 675628149117785751625957379269920733027600949546388741437974902077278618529629, output := 1352990122384458856406192993576384517207773886384142187781843839638502110164742632117 },
  { i := 245, acc := 491341373692656321711366621537727470445519715259299639938118535045569495989270, output := 1352990798012607974191944619533763787128506913985091734170585277613404187443361161746 },
  { i := 246, acc := 355862870689075648849157082993297241737786876284550258930826326495785531517374, output := 1352991289353981666848266330900385324855977359504806993470225215731939233012857151016 },
  { i := 247, acc := 256692392121333475799543325371133834669118798594162247152063756557828335107493, output := 1352991645216852355923915180057468318153219097291683278020484146558265728798388668390 },
  { i := 248, acc := 184408727237521747652676743832403711916012949747246470593892528179361770591294, output := 1352991901909244477257390979600793689287053766410481872182731298622022286626723775883 },
  { i := 249, acc := 131945692275206733971379289868363687666905114390913387815966318560434371498413, output := 1352992086317971714779138632277537521690765682423431619429201892514550465988494367177 },
  { i := 250, acc := 94028886992235305272779795643912937494476209383457600732849819343732794116632, output := 1352992218263663989985872603656827390054453349328546010342589708480869026422865865590 },
  { i := 251, acc := 66740078518632078784262987913179380066455209951252669373970834169199112050147, output := 1352992312292550982221177876436623033967390843804755393800190441330688370155659982222 },
  { i := 252, acc := 47182225102703103509250662879783259078298450202363751694110633016604793052071, output := 1352992379032629500853256660699610947146770910259965345052859815301522539354772032369 },
  { i := 253, acc := 33223341015124665884260041388862646758256103811242060474275289023214358423773, output := 1352992426214854603556360169950273826930029988558415547416611509412155555959565084440 },
  { i := 254, acc := 23301732335759449622751629582633186873243921592299344257890159698797515104494, output := 1352992459438195618681026054210315215792676746814519358658671983687444579173923508213 },
  { i := 255, acc := 16278707477444797660986944141551306405091016268688346841361586352414579955873, output := 1352992482739927954440475676961944798425863620058440950958016241577604277971438612707 },
  { i := 256, acc := 11327789371585485698221097450746989630314377943535927522570162565553373921364, output := 1352992499018635431885273337948888939977170025149457219646363082939190630386018568580 },
  { i := 257, acc := 7851825267119394274128146507552655032997265909224528805718831360593776288654, output := 1352992510346424803470759036169986390724159655463835163182290605509353195939392489944 },
  { i := 258, acc := 5421293619496322148164121291013122668518900540342792933531028140029780077395, output := 1352992518198250070590153310298132898276814688461101072406819411228184556533168778598 },
  { i := 259, acc := 3728624509427875615442877833605043732394503122226410358793618672093511003054, output := 1352992523619543690086475458462254189289937356980001612749612344759212696562948855993 },
  { i := 260, acc := 2554549440553517193544508170004129154066755652242685645209032208828837754720, output := 1352992527348168199514351073905132022894981089374504734976022703552831368656459859047 },
  { i := 261, acc := 1743437531395048617822214308239359872829243520977980448025553670387536174896, output := 1352992529902717640067868267449640192899110243441260387218708348761863577485297613767 },
  { i := 262, acc := 1185308257801588881216069515763372423300018102862477116889154874582907468319, output := 1352992531646155171462916885271854501138470116270503908196688796787417247872833788663 },
  { i := 263, acc := 802777968584035521453244485654488398069497193567877589911636550792533172757, output := 1352992532831463429264505766487924016901842539570522011059165913676572122455741256982 },
  { i := 264, acc := 541633008131463815464813060233691218321936410671033818301722433443185393423, output := 1352992533634241397848541287941168502556330937640019204627043503588208673248274429739 },
  { i := 265, acc := 364054683724661211650887986794388146548181302284869590076160750030350805611, output := 1352992534175874405980005103405981562790022155961955615298077321889931106691459823162 },
  { i := 266, acc := 243773321819769169211941938827861368642445090551543353546400595293100513794, output := 1352992534539929089704666315056869549584410302510136917582946911966091856721810628773 },
  { i := 267, acc := 162618505396019605889942048424314928916736894141228922792706787036115442342, output := 1352992534783702411524435484268811488412271671152582008134490265512492452014911142567 },
  { i := 268, acc := 108074722808432924130843734941526064698116020124396082196945819781058195661, output := 1352992534946320916920455090158753536836586600069318902275719188305199239051026584909 },
  { i := 269, acc := 71557434675314163465210060739259945050974461757671097010954989509883694739, output := 1352992535054395639728888014289597271778112664767434922400115270502145058832084780570 },
  { i := 270, acc := 47202816102181794527772203946269601061451483279593590080449694970869945263, output := 1352992535125953074404202177754807332517372609818409384157786367513100048341968475309 },
  { i := 271, acc := 31021984146963872135318553758249646620497449820116797355138715882470591719, output := 1352992535173155890506383972282579536463642210879860867437379957593549743312838420572 },
  { i := 272, acc := 20312608923815080568016712837543826391641549482588125335998349576674523324, output := 1352992535204177874653347844417898090221891857500358317257496754948688459195309012291 },
  { i := 273, acc := 13251414220568830752776227525968326335868626934545074175255876367210204908, output := 1352992535224490483577162924985914803059435683891999866740084880284686808771983535615 },
  { i := 274, acc := 8613209466866494456526094654773767428123203011691092427629917188442551712, output := 1352992535237741897797731755738691030585404010227868493674629954459942685139193740523 },
  { i := 275, acc := 5578017503509325377006938379196064788405564507166097037899413637877100233, output := 1352992535246355107264598250195217125240177777655991696686321046887572602327636292235 },
  { i := 276, acc := 3599254906664609161149101436440330237370250776107532762110575284638079789, output := 1352992535251933124768107575572224063619373842444397261193487143925472015965513392468 },
  { i := 277, acc := 2314029812293602763342977000647107883738239527060505826815391657694555358, output := 1352992535255532379674772184733373165055814172681767511969594676687582591250151472257 },
  { i := 278, acc := 1482363139306839747663809630195522184199188041523426501673474718581716639, output := 1352992535257846409487065787496716142056461280565505751496655182514397982907846027615 },
  { i := 279, acc := 946183211159098212997035621064625415629699870914497266356664627151660626, output := 1352992535259328772626372627244379951686656802749704939538178609016071457626427744254 },
  { i := 280, acc := 601778213890003818148956220023611299385125062394469981934044603996887344, output := 1352992535260274955837531725457376987307721428165334639409093106282428122253579404880 },
  { i := 281, acc := 381367654764449181116546831229441289616942838276783391208667375031682327, output := 1352992535260876734051421729275525943527745039464719764471487576264362166857576292224 },
  { i := 282, acc := 240825772851697093054228499658008324258621377103759538656010620218415694, output := 1352992535261258101706186178456642490358974480754336707309764359655570834232607974551 },
  { i := 283, acc := 151537207834952940758637118501707115557538915701685886130327942061529594, output := 1352992535261498927479037875549696718858632489078595328686868119194226844852826390245 },
  { i := 284, acc := 95016334374471553286057742511035851981026719310061624540672341494891418, output := 1352992535261650464686872828490455355977134196194152867602569805080357172794887919839 },
  { i := 285, acc := 59367034859713089742836273708745228683649220460395750397186595592532672, output := 1352992535261745481021247300043741413719645232046133894321879866704897845136382811257 },
  { i := 286, acc := 36962890413263216321207403552168913434964383150240196856940895165115212, output := 1352992535261804848056107013133484249993353977274817543542340262455295031731975343929 },
  { i := 287, acc := 22933234826356056150074102390903046338316586673519553072925359496164596, output := 1352992535261841810946520276349805457396906146188252507925490502652151972627140459141 },
  { i := 288, acc := 14179105953911934950391265470229861804677951729724439555341455032199050, output := 1352992535261864744181346632405955531499297049234590824512164022205224897986636623737 },
  { i := 289, acc := 8736184282314312390525317693756056647829203423460498408548448458761083, output := 1352992535261878923287300544340905922764767279096395502463893746644780239441668822787 },
  { i := 290, acc := 5364007423872927147612388512386908351255978524299480646100306985256678, output := 1352992535261887659471582858653296448082461035153043331667317207143188787890127583870 },
  { i := 291, acc := 3282137708945789233146930777776869030634987247580222660614660366030336, output := 1352992535261893023479006731580444060470973422061394587645841506623834888197112840548 },
  { i := 292, acc := 2001378529043175982597200206426653616044700189346357010800093871101295, output := 1352992535261896305616715677369677207401751198930425222633089086846495502857478870884 },
  { i := 293, acc := 1216219077289317802492974473607069160143830737951332144631558813607519, output := 1352992535261898306995244720545659804601957625584041267333278433203506302951349972179 },
  { i := 294, acc := 736562522522229294129105516978859298201709829750964713483176135449519, output := 1352992535261899523214322009863462297576431232653201411164016384535650934510163579698 },
  { i := 295, acc := 444557266666470625418454659184074015944536671188737223591014198353583, output := 1352992535261900259776844532092756426681948211512499612873846135500364417686299029217 },
  { i := 296, acc := 267405985475026336201136735115078468396398916398000230892622449038442, output := 1352992535261900704334111198563381845136607395586515557410517324237588008700497382800 },
  { i := 297, acc := 160304177253589445382373899168695826790754808311755052777158097708059, output := 1352992535261900971740096673589718046273342510664983953809433722237818901322946421242 },
  { i := 298, acc := 95775365194849040940041798518044256669560810556069554418334938581885, output := 1352992535261901132044273927179163428647241679360810744564242033992871678481044129301 },
  { i := 299, acc := 57029948452721616198282811266498176036426427206602907926399290344569, output := 1352992535261901227819639122028204368689040197405067414125052590062426096815982711186 },
  { i := 300, acc := 33845210318084202774518150752406857286562620395568356018157066996295, output := 1352992535261901284849587574749820566971851463903243450551479796665334023215273055755 },
  { i := 301, acc := 20018954337361290285568307402456258745541992886001731874114052648975, output := 1352992535261901318694797892834023341490002216310100737114100192233690041372340052050 },
  { i := 302, acc := 11801584487452648131868571575571087584519636240065635735362397649614, output := 1352992535261901338713752230195313627058309618766359482656093078235421915486392701025 },
  { i := 303, acc := 6934238953908538203503893812036450882514171777991031530531771220673, output := 1352992535261901350515336717647961758926881194337447067175729318301057650848790350639 },
  { i := 304, acc := 4060893513162353974324382584421030738376916238234600890692865831859, output := 1352992535261901357449575671556499962430775006373897949689901096292089181380561571312 },
  { i := 305, acc := 2370355275790628621654470636028007793447554572695611554534438163525, output := 1352992535261901361510469184718853936755157590794928688066817334526690072073427403171 },
  { i := 306, acc := 1379046884138704057169689265681692512247993956016444724207191280543, output := 1352992535261901363880824460509482558409628226822936481514371907222301626607865566696 },
  { i := 307, acc := 799692515448434933090843213558868712806103648363555708595524955092, output := 1352992535261901365259871344648186615579317492504628993762365863238746350815056847239 },
  { i := 308, acc := 462221435876699124346331233737429023206572599245894580969014081921, output := 1352992535261901366059563860096621548670160706063497706568469511602302059410581802331 },
  { i := 309, acc := 266296091564230921296597664162394770883822415510029266994048470342, output := 1352992535261901366521785295973320673016491939800926729775042110848196640379595884252 },
  { i := 310, acc := 152922623266179731506022921573252518927864760907360937514553373386, output := 1352992535261901366788081387537551594313089603963321500658864526358225907373644354594 },
  { i := 311, acc := 87533737447936561908382214332959558146490844594206297958034545226, output := 1352992535261901366941004010803731325819112525536574019586729287265586844888197727980 },
  { i := 312, acc := 49943676570034835223171461088074533770258720592040355796271180372, output := 1352992535261901367028537748251667887727494739869533577733220131859793142846232273206 },
  { i := 313, acc := 28404774245038433925480239536631235989273906245440281499084188079, output := 1352992535261901367078481424821702722950666200957608111503478852451833498642503453578 },
  { i := 314, acc := 16103209048313389342345315550381290728565332266647649536177394671, output := 1352992535261901367106886199066741156876146440494239347492752758697273780141587641657 },
  { i := 315, acc := 9100142840640470446565802999442367315470522888577122648101642575, output := 1352992535261901367122989408115054546218491756044620638221318090963921429677765036328 },
  { i := 316, acc := 5126288948396755725759121724832045832706654421346977903296335056, output := 1352992535261901367132089550955695016665057559044063005536788613852498552325866678903 },
  { i := 317, acc := 2878600694541836646559774683161289473751058651014413232645261473, output := 1352992535261901367137215839904091772390816680768895051369495268273845530229163013959 },
  { i := 318, acc := 1611341491236946745298972045853092747875407531881678598526967694, output := 1352992535261901367140094440598633609037376455452056340843246326924859943461808275432 },
  { i := 319, acc := 899137056110348316739800610732367314467821842869916056594262039, output := 1352992535261901367141705782089870555782675427497909433591121734456741622060335243126 },
  { i := 320, acc := 500150422515724498111859776754830704520099519009836322138718455, output := 1352992535261901367142604919145980904099415228108641800905589556299611538116929505165 },
  { i := 321, acc := 277342284256809314895325836908668264442880601611184143512085600, output := 1352992535261901367143105069568496628597527087885396631610109655818621374439068223620 },
  { i := 322, acc := 153312117582324199115856516781553581006707651072758796067090380, output := 1352992535261901367143382411852753437912422413722305299874552536420232558582580309220 },
  { i := 323, acc := 84486250596187388525254192511285236428711476946165764920000485, output := 1352992535261901367143535723970335762111538270239086853455559244071305317378647399600 },
  { i := 324, acc := 46413993937591416440198896130002930434775348076690746309821773, output := 1352992535261901367143620210220931949500063524431598138691987955548251483143567400085 },
  { i := 325, acc := 25419637764343147558382431493903570664613373291419209450922126, output := 1352992535261901367143666624214869540916503723327728141622422730896328173889877221858 },
  { i := 326, acc := 13878784198663256305889347827463015889084371790317372347677880, output := 1352992535261901367143692043852633884064062105759222045193087344269619593099328143984 },
  { i := 327, acc := 7554387348914334041373503707519089443371701489925165597679733, output := 1352992535261901367143705922636832547320367995107049508208976428641409910471675821864 },
  { i := 328, acc := 4099368156178414079295941656822104273723595329347321505095267, output := 1352992535261901367143713477024181461654409368610757027298419800342899835637273501597 },
  { i := 329, acc := 2217729155386201994309194341343166602301244376685192702001375, output := 1352992535261901367143717576392337640068488664552413849402693523938229182958778596864 },
  { i := 330, acc := 1196129040136347340703123305840033827076271972008122100405190, output := 1352992535261901367143719794121493026270482973746755192569295825182605868151480598239 },
  { i := 331, acc := 643175541908668371219184997954607822844842768897221016466740, output := 1352992535261901367143720990250533162617823676870061032603122901454577876273581003429 },
  { i := 332, acc := 344799759163252062506338065993605821256986651877896180607308, output := 1352992535261901367143721633426075071286194896055058987210945746297346773494597470169 },
  { i := 333, acc := 184286828714851540245402514468662638969175184304044852685391, output := 1352992535261901367143721978225834234538257402393124980816767003283998651390778077477 },
  { i := 334, acc := 98200904859505986228290098804048167973321645868834329058712, output := 1352992535261901367143722162512662949389797647795639449479405972459182955435630762868 },
  { i := 335, acc := 52171635239179189792684149212683154458697092876030808145782, output := 1352992535261901367143722260713567808895783876085738253527573945780828824269959821580 },
  { i := 336, acc := 27634720004967388540537356167356112739294966951636950829570, output := 1352992535261901367143722312885203048074973668769887466210728404477921700300767967362 },
  { i := 337, acc := 14594231057098653990700024333218256358637061189927884363776, output := 1352992535261901367143722340519923053042362209307243633566841143772888651937718796932 },
  { i := 338, acc := 7684519966795038210560760087106246888677519873392670356840, output := 1352992535261901367143722355114154110141016200007267966785097502409949841865603160708 },
  { i := 339, acc := 4034274726969570456910199959525174159035902107369519688636, output := 1352992535261901367143722362798674076936054410568028053891344391087469715258273517548 },
  { i := 340, acc := 2111695030293658121467643653860818633955178366063277338588, output := 1352992535261901367143722366832948803905624867478228013416518550123371822627793206184 },
  { i := 341, acc := 1102091638110746380261154980831395095006142535075272517210, output := 1352992535261901367143722368944643834199282988945871667277337184078550188691070544772 },
  { i := 342, acc := 573493836493640618656515221284170908617287122115272503606, output := 1352992535261901367143722370046735472310029369207026648108732279084692723766343061982 },
  { i := 343, acc := 297555563749704305577058397391361703429744491807441642288, output := 1352992535261901367143722370620229308803669987863541869392903187701979845881615565588 },
  { i := 344, acc := 153935710885360449498205771251473346115136691432918595043, output := 1352992535261901367143722370917784872553374293440600266784264891131724337689057207876 },
  { i := 345, acc := 79404728571501574906671059626325424739013791418493924463, output := 1352992535261901367143722371071720583438734742938806038035738237246861029121975802919 },
  { i := 346, acc := 40840654839156295973284484141864280695115287970886630020, output := 1352992535261901367143722371151125312010236317845477097662063661985874820540469727382 },
  { i := 347, acc := 20945080055133074238894023527929548373965339498377893923, output := 1352992535261901367143722371191965966849392613818761581803927942680990108511356357402 },
  { i := 348, acc := 10710702988126731923102604464943532924597585934143921691, output := 1352992535261901367143722371212911046904525688057655605331857491054955448009734251325 },
  { i := 349, acc := 5461402173897309069663176788566308247748046981698171967, output := 1352992535261901367143722371223621749892652419980758209796801023979553033943878173016 },
  { i := 350, acc := 2776797172127944174446687770432234277948905279672993713, output := 1352992535261901367143722371229083152066549729050421386585367332227301080925576344983 },
  { i := 351, acc := 1407801878962078373109522103864293602851244685692700874, output := 1352992535261901367143722371231859949238677673224868074355799566505249986205249338696 },
  { i := 352, acc := 711704727314562385998045456027834243944799023538188315, output := 1352992535261901367143722371233267751117639751597977596459663860108101230890942039570 },
  { i := 353, acc := 358775363832185366626700648286195459514909030788164136, output := 1352992535261901367143722371233979455844954313983975641915691694352046029914480227885 },
  { i := 354, acc := 180348832246727000652405907897118508733435774550262171, output := 1352992535261901367143722371234338231208786499350602342563977889811560938945268392021 },
  { i := 355, acc := 90401471366920085879848330216356607006522848147238590, output := 1352992535261901367143722371234518580041033226351254748471875008320294374719818654192 },
  { i := 356, acc := 45186902545474233930165912463213133986383788853168291, output := 1352992535261901367143722371234608981512400146437134596802091364927300897567965892782 },
  { i := 357, acc := 22523091492329019654613673770086374103243235761433558, output := 1352992535261901367143722371234654168414945620671064762714554578061287281356819061073 },
  { i := 358, acc := 11195028702176084812584749269415378928901889871798901, output := 1352992535261901367143722371234676691506437949690719376388324664435390524592580494631 },
  { i := 359, acc := 5548909109919395832290294320679926146800106635688096, output := 1352992535261901367143722371234687886535140125775531961137594079814319426482452293532 },
  { i := 360, acc := 2742701784648314013372854935964225600785950416164582, output := 1352992535261901367143722371234693435444250045171364251431914759740466226589087981628 },
  { i := 361, acc := 1351890495776110923916113909798713302345650308463672, output := 1352992535261901367143722371234696178146034693485377624286850723966067012539504146210 },
  { i := 362, acc := 664507274168301421291066197616490734294698886631666, output := 1352992535261901367143722371234697530036530469596301540400760522679369358189812609882 },
  { i := 363, acc := 325729127023756704873139333819101481241828728336123, output := 1352992535261901367143722371234698194543804637897722831466958139170103652888699241548 },
  { i := 364, acc := 159226517570880958672434871935286004846285365594458, output := 1352992535261901367143722371234698520272931661654427704606291958271584894717427577671 },
  { i := 365, acc := 77621036839350935155219320529202267834255798130548, output := 1352992535261901367143722371234698679499449232535386377041163893557589741002793172129 },
  { i := 366, acc := 37735664466482920462581461902461364311091641961727, output := 1352992535261901367143722371234698757120486071886321532260484422759857575258591302677 },
  { i := 367, acc := 18295165509190482664837392053059716684162010048114, output := 1352992535261901367143722371234698794856150538369241994841946325221221886350233264404 },
  { i := 368, acc := 8845771261329309032588520914914549482322510065569, output := 1352992535261901367143722371234698813151316047559724659679338378280938570512243312518 },
  { i := 369, acc := 4265336634023253936877718666479224762178578738401, output := 1352992535261901367143722371234698821997087308889033692267859293195488052834753378087 },
  { i := 370, acc := 2051126157425216674506925357398876003513777172235, output := 1352992535261901367143722371234698826262423942912287629145577959674712815013332116488 },
  { i := 371, acc := 983685060079026593642864467598707860185791954646, output := 1352992535261901367143722371234698828313550100337504303652503317073588818527109288723 },
  { i := 372, acc := 470486961437804518521371484744334184026297709024, output := 1352992535261901367143722371234698829297235160416530897295367784672296678712901243369 },
  { i := 373, acc := 224424403202317344752201934324207798447379961396, output := 1352992535261901367143722371234698829767722121854335415816739269416630862739198952393 },
  { i := 374, acc := 106764451601621737953655746467048525842931468170, output := 1352992535261901367143722371234698829992146525056652760568941203740838661186578913789 },
  { i := 375, acc := 50654787513286334409865630538479285383182743850, output := 1352992535261901367143722371234698830098910976658274498522596950207887187029510381959 },
  { i := 376, acc := 23969261674946939393589887748338234304550221776, output := 1352992535261901367143722371234698830149565764171560832932462580746366472412693125809 },
  { i := 377, acc := 11311813552209296871149495037523211560214580955, output := 1352992535261901367143722371234698830173535025846507772326052468494704706717243347585 },
  { i := 378, acc := 5324223947685355526017561757979542138369395589, output := 1352992535261901367143722371234698830184846839398717069197201963532227918277457928540 },
  { i := 379, acc := 2499366480629867061127528065372309009639153139, output := 1352992535261901367143722371234698830190171063346402424723219525290207460415827324129 },
  { i := 380, acc := 1170189394221399186767449151459228251380690750, output := 1352992535261901367143722371234698830192670429827032291784347053355579769425466477268 },
  { i := 381, acc := 546434344121850126183001634017650874744782508, output := 1352992535261901367143722371234698830193840619221253690971114502507038997676847168018 },
  { i := 382, acc := 254494521849723287634135549673463737489027619, output := 1352992535261901367143722371234698830194387053565375541097297504141056648551591950526 },
  { i := 383, acc := 118217154572158132697540749578323690135493974, output := 1352992535261901367143722371234698830194641548087225264384931639690730112289080978145 },
  { i := 384, acc := 54770556596979390738620922167147964475765862, output := 1352992535261901367143722371234698830194759765241797422517629180440308435979216472119 },
  { i := 385, acc := 25309371262445130114379252812873760404978655, output := 1352992535261901367143722371234698830194814535798394401908367801362475583943692237981 },
  { i := 386, acc := 11665035195702329017893198713727432870995677, output := 1352992535261901367143722371234698830194839845169656847038482180615288457704097216636 },
  { i := 387, acc := 5362461353336658532794896749374156620938833, output := 1352992535261901367143722371234698830194851510204852549367500073814002185136968212313 },
  { i := 388, acc := 2458774139688143964998548975182905561208184, output := 1352992535261901367143722371234698830194856872666205886026032868710751559293589151146 },
  { i := 389, acc := 1124481559120590380227719319671146316584229, output := 1352992535261901367143722371234698830194859331440345574169997867259726742199150359330 },
  { i := 390, acc := 512941884227294918779905533683398877561453, output := 1352992535261901367143722371234698830194860455921904694760378094979046413345466943559 },
  { i := 391, acc := 233382873235129800129425831512974459615450, output := 1352992535261901367143722371234698830194860968863788922055296874884580096744344505012 },
  { i := 392, acc := 105915044088674948887288882718587932036597, output := 1352992535261901367143722371234698830194861202246662157185097004310411609718804120462 },
  { i := 393, acc := 47944303157406815888556102403878646698304, output := 1352992535261901367143722371234698830194861308161706245860045891599294328306736157059 },
  { i := 394, acc := 21647606598284518529498986798803119520645, output := 1352992535261901367143722371234698830194861356106009403266861780155396732185382855363 },
  { i := 395, acc := 9749426994504466573157136409819947234148, output := 1352992535261901367143722371234698830194861377753616001551380309654383530988502376008 },
  { i := 396, acc := 4379730850176553001757529610148316199656, output := 1352992535261901367143722371234698830194861387503042996055846882811519940808449610156 },
  { i := 397, acc := 1962536139812664233947145950413494585396, output := 1352992535261901367143722371234698830194861391882773846232399884569049550956765809812 },
  { i := 398, acc := 877187799661717100123980348667221807467, output := 1352992535261901367143722371234698830194861393845309986045064118516195501370260395208 },
  { i := 399, acc := 391088402222073934584485675868560738844, output := 1352992535261901367143722371234698830194861394722497785706781218640175850037482202675 },
  { i := 400, acc := 173927184955569988415892998856974984691, output := 1352992535261901367143722371234698830194861395113586187928855153224661525906042941519 },
  { i := 401, acc := 77156568261689759831074351765736786116, output := 1352992535261901367143722371234698830194861395287513372884425141640554524763017926210 },
  { i := 402, acc := 34142392988694162841569801917104902427, output := 1352992535261901367143722371234698830194861395364669941146114901471628876528754712326 },
  { i := 403, acc := 15070696720810846255920293186324805211, output := 1352992535261901367143722371234698830194861395398812334134809064313198678445859614753 },
  { i := 404, acc := 6635806455785273347796728991719640232, output := 1352992535261901367143722371234698830194861395413883030855619910569118971632184419964 },
  { i := 405, acc := 2914592023365833288237734454843267711, output := 1352992535261901367143722371234698830194861395420518837311405183916915700623904060196 },
  { i := 406, acc := 1276991996240142893209368307103623402, output := 1352992535261901367143722371234698830194861395423433429334771017205153435078747327907 },
  { i := 407, acc := 558119977642647214751559638634353550, output := 1352992535261901367143722371234698830194861395424710421331011160098362803385850951309 },
  { i := 408, acc := 243331641255283205182674083685922243, output := 1352992535261901367143722371234698830194861395425268541308653807313114363024485304859 },
  { i := 409, acc := 105828794431361994642842627529334706, output := 1352992535261901367143722371234698830194861395425511872949909090518297037108171227102 },
  { i := 410, acc := 45914088529977263355907672919965726, output := 1352992535261901367143722371234698830194861395425617701744340452512939879735700561808 },
  { i := 411, acc := 19871357515903408123995822124343785, output := 1352992535261901367143722371234698830194861395425663615832870429776295787408620527534 },
  { i := 412, acc := 8579285918804407296804473933931254, output := 1352992535261901367143722371234698830194861395425683487190386333184419783230744871319 },
  { i := 413, acc := 3695041769335504199664531049699434, output := 1352992535261901367143722371234698830194861395425692066476305137591716587704678802573 },
  { i := 414, acc := 1587576738521503200813467256046664, output := 1352992535261901367143722371234698830194861395425695761518074473095916252235728502007 },
  { i := 415, acc := 680455630865923181368815288301639, output := 1352992535261901367143722371234698830194861395425697349094812994599117065702984548671 },
  { i := 416, acc := 290949183022072969402929535381572, output := 1352992535261901367143722371234698830194861395425698029550443860522298434518272850310 },
  { i := 417, acc := 124104988280119736393406050799746, output := 1352992535261901367143722371234698830194861395425698320499626882595267837447808231882 },
  { i := 418, acc := 52810296936487029141068331026182, output := 1352992535261901367143722371234698830194861395425698444604615162715004230853859031628 },
  { i := 419, acc := 22418562104617931630909006628229, output := 1352992535261901367143722371234698830194861395425698497414912099202033371922190057810 },
  { i := 420, acc := 9494217084904377070428321720981, output := 1352992535261901367143722371234698830194861395425698519833474203819965002831196686039 },
  { i := 421, acc := 4011209024544241908518139220355, output := 1352992535261901367143722371234698830194861395425698529327691288724342073259518407020 },
  { i := 422, acc := 1690669135529283648084591744617, output := 1352992535261901367143722371234698830194861395425698533338900313268583981777657627375 },
  { i := 423, acc := 710905050925116285693735964412, output := 1352992535261901367143722371234698830194861395425698535029569448797867629862249371992 },
  { i := 424, acc := 298219926594809750668684020818, output := 1352992535261901367143722371234698830194861395425698535740474499722983915555985336404 },
  { i := 425, acc := 124806219691858993229200966276, output := 1352992535261901367143722371234698830194861395425698536038694426317793666224669357222 },
  { i := 426, acc := 52108998367054084306071734558, output := 1352992535261901367143722371234698830194861395425698536163500646009652659453870323498 },
  { i := 427, acc := 21705437932875335632046773468, output := 1352992535261901367143722371234698830194861395425698536215609644376706743759942058056 },
  { i := 428, acc := 9019990998188994142430369879, output := 1352992535261901367143722371234698830194861395425698536237315082309582079391988831524 },
  { i := 429, acc := 3739622478262358229108742022, output := 1352992535261901367143722371234698830194861395425698536246335073307771073534419201403 },
  { i := 430, acc := 1546806170496104204693952213, output := 1352992535261901367143722371234698830194861395425698536250074695786033431763527943425 },
  { i := 431, acc := 638311790887491534340236520, output := 1352992535261901367143722371234698830194861395425698536251621501956529535968221895638 },
  { i := 432, acc := 262797375137191000848437157, output := 1352992535261901367143722371234698830194861395425698536252259813747417027502562132158 },
  { i := 433, acc := 107945042777236370022069351, output := 1352992535261901367143722371234698830194861395425698536252522611122554218503410569315 },
  { i := 434, acc := 44236446493972214894255367, output := 1352992535261901367143722371234698830194861395425698536252630556165331454873432638666 },
  { i := 435, acc := 18086558185578375874014103, output := 1352992535261901367143722371234698830194861395425698536252674792611825427088326894033 },
  { i := 436, acc := 7377888700865851658303085, output := 1352992535261901367143722371234698830194861395425698536252692879170011005464200908136 },
  { i := 437, acc := 3002693726497678625749200, output := 1352992535261901367143722371234698830194861395425698536252700257058711871315859211221 },
  { i := 438, acc := 1219256349992119181948449, output := 1352992535261901367143722371234698830194861395425698536252703259752438368994484960421 },
  { i := 439, acc := 493953812817041003561083, output := 1352992535261901367143722371234698830194861395425698536252704479008788361113666908870 },
  { i := 440, acc := 199658244535760176547390, output := 1352992535261901367143722371234698830194861395425698536252704972962601178154670469953 },
  { i := 441, acc := 80519301419508333583400, output := 1352992535261901367143722371234698830194861395425698536252705172620845713914847017343 },
  { i := 442, acc := 32398644114532716203337, output := 1352992535261901367143722371234698830194861395425698536252705253140147133423180600743 },
  { i := 443, acc := 13006785927718068757652, output := 1352992535261901367143722371234698830194861395425698536252705285538791247955896804080 },
  { i := 444, acc := 5209927654863911709393, output := 1352992535261901367143722371234698830194861395425698536252705298545577175673965561732 },
  { i := 445, acc := 2082160239806800766271, output := 1352992535261901367143722371234698830194861395425698536252705303755504830537877271125 },
  { i := 446, acc := 830270418038296237482, output := 1352992535261901367143722371234698830194861395425698536252705305837665070344678037396 },
  { i := 447, acc := 330331608698187473700, output := 1352992535261901367143722371234698830194861395425698536252705306667935488382974274878 },
  { i := 448, acc := 131131803938906974246, output := 1352992535261901367143722371234698830194861395425698536252705306998267097081161748578 },
  { i := 449, acc := 51939222975876850803, output := 1352992535261901367143722371234698830194861395425698536252705307129398901020068722824 },
  { i := 450, acc := 20526482516621974407, output := 1352992535261901367143722371234698830194861395425698536252705307181338123995945573627 },
  { i := 451, acc := 8094079139411497274, output := 1352992535261901367143722371234698830194861395425698536252705307201864606512567548034 },
  { i := 452, acc := 3184610560740258614, output := 1352992535261901367143722371234698830194861395425698536252705307209958685651979045308 },
  { i := 453, acc := 1250211019885253179, output := 1352992535261901367143722371234698830194861395425698536252705307213143296212719303922 },
  { i := 454, acc := 489723051675032045, output := 1352992535261901367143722371234698830194861395425698536252705307214393507232604557101 },
  { i := 455, acc := 191408015574319242, output := 1352992535261901367143722371234698830194861395425698536252705307214883230284279589146 },
  { i := 456, acc := 74647308023313141, output := 1352992535261901367143722371234698830194861395425698536252705307215074638299853908388 },
  { i := 457, acc := 29047899569084212, output := 1352992535261901367143722371234698830194861395425698536252705307215149285607877221529 },
  { i := 458, acc := 11278827661843293, output := 1352992535261901367143722371234698830194861395425698536252705307215178333507446305741 },
  { i := 459, acc := 4369823634471444, output := 1352992535261901367143722371234698830194861395425698536252705307215189612335108149034 },
  { i := 460, acc := 1689338385087621, output := 1352992535261901367143722371234698830194861395425698536252705307215193982158742620478 },
  { i := 461, acc := 651664772990576, output := 1352992535261901367143722371234698830194861395425698536252705307215195671497127708099 },
  { i := 462, acc := 250835352820797, output := 1352992535261901367143722371234698830194861395425698536252705307215196323161900698675 },
  { i := 463, acc := 96341232286381, output := 1352992535261901367143722371234698830194861395425698536252705307215196573997253519472 },
  { i := 464, acc := 36922970429331, output := 1352992535261901367143722371234698830194861395425698536252705307215196670338485805853 },
  { i := 465, acc := 14120305025242, output := 1352992535261901367143722371234698830194861395425698536252705307215196707261456235184 },
  { i := 466, acc := 5388359360506, output := 1352992535261901367143722371234698830194861395425698536252705307215196721381761260426 },
  { i := 467, acc := 2051804895938, output := 1352992535261901367143722371234698830194861395425698536252705307215196726770120620932 },
  { i := 468, acc := 779622936713, output := 1352992535261901367143722371234698830194861395425698536252705307215196728821925516870 },
  { i := 469, acc := 295599830775, output := 1352992535261901367143722371234698830194861395425698536252705307215196729601548453583 },
  { i := 470, acc := 111839898655, output := 1352992535261901367143722371234698830194861395425698536252705307215196729897148284358 },
  { i := 471, acc := 42224482287, output := 1352992535261901367143722371234698830194861395425698536252705307215196730008988183013 },
  { i := 472, acc := 15907753501, output := 1352992535261901367143722371234698830194861395425698536252705307215196730051212665300 },
  { i := 473, acc := 5980428198, output := 1352992535261901367143722371234698830194861395425698536252705307215196730067120418801 },
  { i := 474, acc := 2243554202, output := 1352992535261901367143722371234698830194861395425698536252705307215196730073100846999 },
  { i := 475, acc := 839892398, output := 1352992535261901367143722371234698830194861395425698536252705307215196730075344401201 },
  { i := 476, acc := 313758476, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076184293599 },
  { i := 477, acc := 116964465, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076498052075 },
  { i := 478, acc := 43511192, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076615016540 },
  { i := 479, acc := 16152453, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076658527732 },
  { i := 480, acc := 5983680, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076674680185 },
  { i := 481, acc := 2212037, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076680663865 },
  { i := 482, acc := 816042, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076682875902 },
  { i := 483, acc := 300421, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076683691944 },
  { i := 484, acc := 110369, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076683992365 },
  { i := 485, acc := 40463, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076684102734 },
  { i := 486, acc := 14804, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076684143197 },
  { i := 487, acc := 5405, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076684158001 },
  { i := 488, acc := 1969, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076684163406 },
  { i := 489, acc := 715, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076684165375 },
  { i := 490, acc := 259, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076684166090 },
  { i := 491, acc := 93, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076684166349 },
  { i := 492, acc := 33, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076684166442 },
  { i := 493, acc := 11, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076684166475 },
  { i := 494, acc := 3, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076684166486 },
  { i := 495, acc := 1, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076684166489 },
  { i := 496, acc := 0, output := 1352992535261901367143722371234698830194861395425698536252705307215196730076684166490 }
]

def taylorInitial : TaylorState :=
  { i := 1, acc := taylorDenominator, output := 0 }

-- Ten denominator units make the loop perform many nontrivial iterations.
#guard taylorExp384 (10 * taylorDenominator) |>.isSome

theorem taylorExp384_some_witness_10D :
    taylorExp384 (10 * taylorDenominator) =
      some (taylorExpNat 1 (10 * taylorDenominator) taylorDenominator) := by
  have h_trace :
      taylorTraceValidTo (10 * taylorDenominator) taylorDenominator
          taylorInitial taylorTrace10D := by
    norm_num [taylorTraceValidTo, taylorTraceStep, taylorInitial,
      taylorTrace10D, taylorDenominator]
  have h_aux :
      taylorNatAux (10 * taylorDenominator) taylorDenominator
          taylorInitial.i taylorInitial.acc taylorInitial.output =
        (taylorTraceFinal taylorInitial taylorTrace10D).output := by
    exact taylorNatAux_eq_trace (10 * taylorDenominator) taylorDenominator
      taylorInitial taylorTrace10D h_trace
  have h_result :
      taylorExpNat 1 (10 * taylorDenominator) taylorDenominator <
        taylorResultBound := by
    unfold taylorExpNat
    have h_aux' :
        taylorNatAux (10 * taylorDenominator) taylorDenominator 1
            (1 * taylorDenominator) 0 =
          (taylorTraceFinal taylorInitial taylorTrace10D).output := by
      simpa [taylorInitial] using h_aux
    rw [h_aux']
    norm_num [taylorTraceFinal, taylorTrace10D, taylorDenominator,
      taylorResultBound]; decide
  have h_num : 10 * taylorDenominator < taylorWord64Bound := by decide
  exact taylorExp384_some_of_lt (10 * taylorDenominator) h_num h_result

-- These are the measured boundary values from #12632.
#guard taylorExp384 2073394370 |>.isSome
#guard taylorExp384 2073394371 |>.isNone

theorem taylorExp384_none_witness_measured :
    taylorResultBound ≤ taylorExpNat 1 2073394371 taylorDenominator ∧
      taylorExp384 2073394371 = none := by
  have h_trace :
      taylorTraceValidTo 2073394371 taylorDenominator
          taylorInitial taylorTraceMeasured := by
    norm_num [taylorTraceValidTo, taylorTraceStep, taylorInitial,
      taylorTraceMeasured, taylorDenominator]
  have h_aux :
      taylorNatAux 2073394371 taylorDenominator
          taylorInitial.i taylorInitial.acc taylorInitial.output =
        (taylorTraceFinal taylorInitial taylorTraceMeasured).output := by
    exact taylorNatAux_eq_trace 2073394371 taylorDenominator
      taylorInitial taylorTraceMeasured h_trace
  have h_result :
      taylorResultBound ≤ taylorExpNat 1 2073394371 taylorDenominator := by
    unfold taylorExpNat
    have h_aux' :
        taylorNatAux 2073394371 taylorDenominator 1
            (1 * taylorDenominator) 0 =
          (taylorTraceFinal taylorInitial taylorTraceMeasured).output := by
      simpa [taylorInitial] using h_aux
    rw [h_aux']
    norm_num [taylorTraceFinal, taylorTraceMeasured, taylorDenominator,
      taylorResultBound]; decide
  exact ⟨h_result, taylorExp384_none_of_ge 2073394371 h_result⟩

theorem taylorExpNat_ge_result_bound_of_ge
    (numerator : Nat) (h_num : 2073394371 ≤ numerator) :
    taylorResultBound ≤ taylorExpNat 1 numerator taylorDenominator := by
  exact le_trans taylorExp384_none_witness_measured.1
    (taylorExpNat_mono_num h_num)

#print axioms taylorExp384_some_of_lt
#print axioms taylorExp384_none_of_ge
#print axioms taylorExp384_some_iff_lt
#print axioms taylorExp384_none_iff_ge
#print axioms taylorExp384_exact_iff_lt
#print axioms taylorNatAux_mono_num
#print axioms taylorExpNat_mono_num
#print axioms taylorExpNat_ge_result_bound_of_ge

end EvmAsm.Stateless.SpecRef
