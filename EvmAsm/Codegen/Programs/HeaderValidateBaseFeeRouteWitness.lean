/-
  EvmAsm.Codegen.Programs.HeaderValidateBaseFeeRouteWitness

  Closed K74 wrapper witnesses for the three K73 routes that
  `HeaderValidateBaseFeeCompositionEqualDecrease` composes at the caller's
  shape (#13164): the equal route, the nonzero-decrease route, and the
  zero-gas decrease route.  The increase route already has its closed
  wrapper witness (`header_validate_base_fee_spec_within_inhabited` in
  `HeaderValidateBaseFeeSpecRefWitness`); this module supplies the other
  three so every live K73 arm is claimed at the K74 seam by a theorem whose
  entire premise set is discharged by kernel computation.

  Each witness instantiates the corresponding parametric route theorem at a
  concrete, non-degenerate point (real 32-byte header/parent/scratch regions
  at the #12762 layout addresses, a code requirement carrying the wrapper,
  the whole K73 image and the equality callee) and closes every static gate
  by `decide`/`simp`/`rfl`.  As with the increase witness, the point is
  non-vacuity by construction: an unsatisfiable static premise cannot be
  discharged this way, so a route whose contract is inconsistent cannot be
  registered through these theorems.

  The three witnesses share one code requirement, `k74RouteWitnessCode`;
  the three code-monotonicity facts it needs are proved once from the
  pairwise range-disjointness lemmas in `HeaderValidateBaseFeeSpec`.
-/

import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompositionEqualDecrease

namespace EvmAsm.Codegen.HeaderValidateBaseFeeRouteWitness

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec
open EvmAsm.Codegen.HeaderValidateBaseFeeCompositionEqualDecrease
open EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute
open EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero
open EvmAsm.Codegen.U256DivU64BeSAsm
open EvmAsm.Codegen.U256SubBeSAsm

/-! ## §1  The shared code requirement -/

/-- The wrapper, the whole K73 image (K73 and its arithmetic callees), and
    the u256 equality callee, at their linked addresses. -/
def k74RouteWitnessCode : CodeReq :=
  hvbfCode.union (wholeCode.union u256EqCode)

private theorem k74RouteWitness_hvbf_u256eq_disjoint :
    hvbfCode.Disjoint u256EqCode := by
  unfold hvbfCode hvbfProg u256EqCode
  apply CodeReq.Disjoint.ofProg_ranges <;> decide

theorem k74RouteWitnessCode_hvbf :
    ∀ a i, hvbfCode a = some i → k74RouteWitnessCode a = some i :=
  CodeReq.union_mono_left

theorem k74RouteWitnessCode_whole :
    ∀ a i, wholeCode a = some i → k74RouteWitnessCode a = some i := by
  intro a i hwhole
  have hvnone : hvbfCode a = none := by
    cases hv : hvbfCode a with
    | none => exact rfl
    | some j => exact False.elim (k74_hvbf_whole_disjoint hv hwhole)
  exact CodeReq.union_skip hvnone (CodeReq.union_hit hwhole)

theorem k74RouteWitnessCode_u256eq :
    ∀ a i, u256EqCode a = some i → k74RouteWitnessCode a = some i := by
  intro a i h
  have hwhole : wholeCode a = none := by
    cases hw : wholeCode a with
    | none => exact rfl
    | some j => exact False.elim (k74_whole_u256eq_disjoint hw h)
  have hvnone : hvbfCode a = none := by
    cases hv : hvbfCode a with
    | none => exact rfl
    | some j =>
      rcases k74RouteWitness_hvbf_u256eq_disjoint a with hleft | hright
      · rw [hv] at hleft
        simp at hleft
      · rw [h] at hright
        simp at hright
  exact CodeReq.union_skip hvnone (CodeReq.union_skip hwhole h)

/-! ## §2  Equal route: `gas_used = gas_limit >>> 1`

Point: the equal-route adapter's own witness family (gas limit 100,000, gas
used 50,000, all-zero regions, K74 frame at `0x100000`).  The caller-owned
ambient is the K74 flat frame over an empty tail, on both sides of K73. -/

theorem header_validate_base_fee_equal_route_spec_within_inhabited :
    cpsTripleWithin
      (27 + 29 +
        (U256EqSAsm.u256EqBody (0x200000 : Word) Expected (List.replicate 32 0)
          (hvbfWrittenImage (100000 : Word) (50000 : Word) (List.replicate 32 0))).steps)
      H (H + 40) k74RouteWitnessCode
      (hvbfPre (0x100010 : Word) (0x100000 : Word) (0xFFFC8 : Word) (H + 40)
        (0x56780000 : Word) (0x200000 : Word) (100000 : Word) (50000 : Word)
        (0x200100 : Word) (1 : Word) (2 : Word) (3 : Word) (4 : Word)
        (List.replicate 32 0) (List.replicate 32 0) (List.replicate 32 0)
        (k74FlatFrame empAssertion))
      (hvbfFinalRouteB (0x100010 : Word) (0x100000 : Word) (0xFFFC8 : Word) (H + 40)
        (0x56780000 : Word) (0x200000 : Word) (1 : Word) (2 : Word)
        ((100000 : Word) >>> 1) (3 : Word) (4 : Word)
        (100000 : Word) (50000 : Word) (0x200100 : Word)
        (List.replicate 32 0) (List.replicate 32 0)
        (k74FlatFrame empAssertion)) :=
  header_validate_base_fee_equal_route_spec_within (cr := k74RouteWitnessCode)
    (0x100010 : Word) (0x100000 : Word) (0xFFFC8 : Word) (0x56780000 : Word)
    (0x200000 : Word) (100000 : Word) (50000 : Word) (0x200100 : Word)
    (1 : Word) (2 : Word) (3 : Word) (4 : Word)
    (List.replicate 32 0) (List.replicate 32 0) (List.replicate 32 0)
    empAssertion
    (hspH := by decide)
    (hspK := by decide)
    (hret := by unfold H; rfl)
    (hFtail := by pcf)
    (hHeaderWf := by decide)
    (hExpectedWf := by decide)
    (hHeaderLen := by simp)
    (hExpectedLen := by simp)
    (hDisj := by decide)
    k74RouteWitnessCode_hvbf k74RouteWitnessCode_whole k74RouteWitnessCode_u256eq
    (heqWord := rfl)
    (hsrc := by simp)
    (hout := by simp)

/-! ## §3  Nonzero-decrease route: `0 < gas_used < gas_limit >>> 1`

Point: the decrease adapter's own witness family (gas limit 10,000, gas used
2,500, target 5,000, zero parent fee, 40-byte zero accumulator window, K74
frame at `0xa0050038`).  The entry ambient is the caller-supplied multiply
frame and accumulator over the flat frame; the exit ambient is the route's
Route-B junk (`k73_decr_outj`). -/

theorem header_validate_base_fee_decrease_route_spec_within_inhabited :
    cpsTripleWithin
      (27 + k73_decr_route_steps (10000 : Word) (2500 : Word) (0x200100 : Word)
          (List.replicate 32 0) (List.replicate 32 0) +
        (U256EqSAsm.u256EqBody (0x200000 : Word) Expected (List.replicate 32 0)
          (hvbfWrittenImage (10000 : Word) (2500 : Word) (List.replicate 32 0))).steps)
      H (H + 40) k74RouteWitnessCode
      (hvbfPre (0xa0050048 : Word) (0xa0050038 : Word) (0xa0050000 : Word) (H + 40)
        (0 : Word) (0x200000 : Word) (10000 : Word) (2500 : Word) (0x200100 : Word)
        (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        (List.replicate 32 0) (List.replicate 32 0) (List.replicate 32 0)
        (k73_decr_env (0xa0050000 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
          (0 : Word) (0 : Word) (List.replicate 40 0) empAssertion))
      (hvbfFinalRouteB (0xa0050048 : Word) (0xa0050038 : Word) (0xa0050000 : Word) (H + 40)
        (0 : Word) (0x200000 : Word) (0 : Word) (0 : Word) ((10000 : Word) >>> 1)
        (0 : Word) (0 : Word) (10000 : Word) (2500 : Word) (0x200100 : Word)
        (List.replicate 32 0) (List.replicate 32 0)
        (k73_decr_outj (0xa0050000 : Word) (0x200000 : Word) (0x200100 : Word)
          (0 : Word) (0 : Word) (0 : Word) (0 : Word) (2500 : Word)
          ((10000 : Word) >>> 1) (List.replicate 32 0) empAssertion)) :=
  header_validate_base_fee_decrease_route_spec_within (cr := k74RouteWitnessCode)
    (0xa0050048 : Word) (0xa0050038 : Word) (0xa0050000 : Word) (0 : Word)
    (0x200000 : Word) (10000 : Word) (2500 : Word) (0x200100 : Word)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    (List.replicate 32 0) (List.replicate 32 0) (List.replicate 32 0)
    (List.replicate 40 0) empAssertion
    (hspH := by decide)
    (hspK := by decide)
    (hret := by unfold H; rfl)
    (hne := by decide)
    (hnotlt := by decide)
    (hnonzero := by decide)
    (hG := by pcf)
    (hHeaderWf := by decide)
    (hExpectedWf := by decide)
    (hHeaderLen := by simp)
    (hDisj := by decide)
    (htargetPos := by decide)
    (hleTarget := by decide)
    (hMulFit := by decide)
    (hlenP := by simp)
    (hExpectedLen := by simp)
    (hlenAcc := by simp)
    (halignA := by decide)
    (hoverA := by decide)
    (hvalidA := by intro j _; interval_cases j <;> decide)
    (halignOut := by decide)
    (hoverOut := by decide)
    (hvalidOut := by intro j _; interval_cases j <;> decide)
    (hdisj := by decide)
    (hrw := by decide)
    (hroBase := by
      refine ⟨?_, ?_, ?_⟩
      · decide
      · decide
      · intro k hk
        have hk32 : k < 32 := by simpa using hk
        interval_cases k <;> decide)
    (hszDiv1 := by simp only [k73_decr_img2, u256DivU64BeInPlaceFn]; decide)
    (hszDiv2 := by simp only [k73_decr_img2, u256DivU64BeInPlaceFn]; decide)
    (hszSub := by simp only [k73_decr_img2, u256SubBeInPlaceFn]; decide)
    k74RouteWitnessCode_hvbf k74RouteWitnessCode_whole k74RouteWitnessCode_u256eq

/-! ## §4  Zero-gas decrease route: `gas_used = 0 < gas_limit >>> 1`

Point: the zero-route adapter's own witness family (gas limit 10,000, gas
used 0, zero parent fee, K74 frame at `0xa0050038`).  There is no multiply
ambient on this route; the caller-owned ambient is the flat frame over an
empty tail on both sides. -/

theorem header_validate_base_fee_zero_decrease_route_spec_within_inhabited :
    cpsTripleWithin
      (27 + k73_zero_route_steps (0x200100 : Word) (List.replicate 32 0) (List.replicate 32 0) +
        (U256EqSAsm.u256EqBody (0x200000 : Word) Expected (List.replicate 32 0)
          (hvbfWrittenImage (10000 : Word) 0 (List.replicate 32 0))).steps)
      H (H + 40) k74RouteWitnessCode
      (hvbfPre (0xa0050048 : Word) (0xa0050038 : Word) (0xa0050000 : Word) (H + 40)
        (0 : Word) (0x200000 : Word) (10000 : Word) 0 (0x200100 : Word)
        (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        (List.replicate 32 0) (List.replicate 32 0) (List.replicate 32 0)
        (k73_zero_env empAssertion))
      (hvbfFinalRouteB (0xa0050048 : Word) (0xa0050038 : Word) (0xa0050000 : Word) (H + 40)
        (0 : Word) (0x200000 : Word) (0 : Word) (0 : Word) ((10000 : Word) >>> 1)
        (0 : Word) (0 : Word) (10000 : Word) 0 (0x200100 : Word)
        (List.replicate 32 0) (List.replicate 32 0)
        (k73_zero_outj empAssertion)) :=
  header_validate_base_fee_zero_decrease_route_spec_within (cr := k74RouteWitnessCode)
    (0xa0050048 : Word) (0xa0050038 : Word) (0xa0050000 : Word) (0 : Word)
    (0x200000 : Word) (10000 : Word) (0x200100 : Word)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    (List.replicate 32 0) (List.replicate 32 0) (List.replicate 32 0)
    empAssertion
    (hspH := by decide)
    (hspK := by decide)
    (hret := by unfold H; rfl)
    (htargetPos := by decide)
    (hFtail := by pcf)
    (hHeaderWf := by decide)
    (hExpectedWf := by decide)
    (hHeaderLen := by simp)
    (hExpectedLen := by simp)
    (hsrc := by simp)
    (hHeaderDisj := by decide)
    (hParentDisj := by decide)
    (hroBase := by
      refine ⟨?_, ?_, ?_⟩
      · decide
      · decide
      · intro k hk
        have hk32 : k < 32 := by simpa using hk
        interval_cases k <;> decide)
    (hrw := by decide)
    (hovBase := by decide)
    (hovExpected := by decide)
    (hszDiv := by simp only [u256DivU64BeFn]; decide)
    (hszSub := by simp only [u256SubBeInPlaceFn]; decide)
    k74RouteWitnessCode_hvbf k74RouteWitnessCode_whole k74RouteWitnessCode_u256eq

#print axioms header_validate_base_fee_equal_route_spec_within_inhabited
#print axioms header_validate_base_fee_decrease_route_spec_within_inhabited
#print axioms header_validate_base_fee_zero_decrease_route_spec_within_inhabited

end EvmAsm.Codegen.HeaderValidateBaseFeeRouteWitness
