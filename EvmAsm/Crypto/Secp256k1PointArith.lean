/-
  EvmAsm.Crypto.Secp256k1PointArith

  The PURE point-arithmetic bridge between the secp256k1 SpecRef group law
  (`EvmAsm.Stateless.SpecRef.Secp256k1.pointAdd`) and the accelerator
  semantics the guest triples are stated against
  (`EvmAsm.Rv64.Accel.curveDbl` / `Accel.curveAdd`).  This is the named
  residual `#12319` that the `secp256k1_point_double` registry row carried:
  `pointDouble_spec` produced `Accel.curveDbl Accel.secpP x y` (plus a
  zero-point branch), and nothing tied that to the reference group law.

  WHAT IS PROVED HERE (three legs, all unconditional or under stated,
  witnessed hypotheses):

  * `pointAdd_self_zero` — self-addition of a `y = 0` point is the
    identity.  `x₁ = x₂` takes the equal-abscissa branch and
    `(0 + 0) % p = 0` selects `none`.  This is the 2-torsion /
    self-inverse case, and it is exactly the machine's infinity branch
    (`a0 = 1`, 64-byte zero output).

  * `pointAdd_self_of_ne_zero` — for `0 < y < p`, self-addition IS the
    accelerator's affine tangent doubling.  The only content is the
    doubling gate `two_mul_mod_ne_zero`: `p` is an ODD modulus and
    `y < p`, so `0 < y + y < 2p` forces `y + y = p` in the divisible
    case, which an odd `p` refuses.  No primality is needed — oddness
    suffices, and it is kernel-checked (`secpP_odd`).

  * `pointAdd_of_fst_ne` — distinct abscissae take the chord rule, i.e.
    `Accel.curveAdd`.  Definitional; stated so the `secp256k1_point_add`
    lane can cite it without re-deriving the case split.

  `pointAdd_self` packages the first two as a single `if`-characterisation
  on the machine's domain (`y < p`), which is the form the whole-routine
  triple's disjunctive post consumes.

  NON-VACUITY (this file's hypotheses are load-bearing, not decoration):
  `pointAdd_self_gen` instantiates the `0 < y < p` bundle at the real
  generator and `pointAdd_self_gen_kat` pins the resulting value to the
  independently computed `2·G` (`decide +kernel`).  The two NEGATIVE
  CONTROLS `pointAdd_self_ne_curveDbl_of_zero` and
  `pointAdd_self_ne_curveDbl_at_p` exhibit inputs where each hypothesis is
  provably FALSE and the conclusion of `pointAdd_self_of_ne_zero`
  provably FAILS — so neither `hy0` nor `hylt` can be dropped, and
  neither theorem is vacuous.

  SCOPE: nothing here is a group law.  Associativity, on-curve closure,
  and the abelian-monoid `AddLaws` of `EvmAsm/Crypto/ScalarMul.lean` stay
  out of scope (they are FALSE on the raw `Option (Nat × Nat)` carrier);
  this file only resolves `pointAdd`'s software case split into the
  accelerator primitives.
-/

module

public import EvmAsm.Stateless.SpecRef.Secp256k1Recover

public section

namespace EvmAsm.Crypto.Secp256k1PointArith

open EvmAsm.Rv64
open EvmAsm.Stateless.SpecRef.Secp256k1

-- ============================================================================
-- The modulus: the SpecRef `p` IS the accelerator modulus
-- ============================================================================

/-- The SpecRef abbreviation `p` and the accelerator's `Accel.secpP` are
    the SAME constant (`p` is an `abbrev`, so this is `rfl`); recorded so
    a reader of a mixed statement does not have to check. -/
theorem p_eq_secpP : p = Accel.secpP := rfl

/-- `p` is odd.  This — NOT primality — is what the doubling gate below
    needs. -/
theorem secpP_odd : Accel.secpP % 2 = 1 := by decide

-- ============================================================================
-- The doubling gate
-- ============================================================================

/-- **The doubling gate.**  For a reduced, nonzero `y`, the SpecRef test
    `(y₁ + y₂) % p = 0` at `y₁ = y₂ = y` does NOT fire, so `pointAdd`
    takes its tangent branch.

    Proof: `p ∣ y + y` with `0 < y + y < p + p` forces `y + y = p`, and
    `p` is odd (`secpP_odd`).  Oddness is the whole content — primality
    is not used. -/
theorem two_mul_mod_ne_zero {y : Nat} (hy0 : y ≠ 0) (hylt : y < p) :
    (y + y) % p ≠ 0 := by
  have hodd : p % 2 = 1 := secpP_odd
  intro hmod
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · -- `k = 0` is refuted by `0 < y + y`; `k = 1` is the goal
      rcases Nat.lt_or_ge k 1 with h1 | h1
      · have hk0 : k = 0 := by omega
        subst hk0; omega
      · omega
    · -- `k ≥ 2` overshoots: `p * 2 ≤ p * k = y + y < p + p`
      have hle : p * 2 ≤ p * k := Nat.mul_le_mul (Nat.le_refl p) h2
      omega
  subst hk1
  omega

-- ============================================================================
-- The bridge legs
-- ============================================================================

/-- **The 2-torsion / infinity leg.**  Self-addition of a `y = 0` point
    is the identity `𝒪`.  Unconditional: `x = x` takes the
    equal-abscissa branch and `(0 + 0) % p = 0` selects `none`.

    This is the machine's `beBytesToNat yBE = 0` branch
    (`a0 = 1`, 64-byte zero output). -/
theorem pointAdd_self_zero (x : Nat) :
    pointAdd (some (x, 0)) (some (x, 0)) = none := by
  simp [pointAdd]

/-- **The tangent leg.**  For a reduced, nonzero `y`, self-addition in
    the SpecRef group law IS the accelerator's affine tangent doubling.

    This is the machine's generic branch (`a0 = 0`, output BE-encoding
    `Accel.curveDbl Accel.secpP x y`). -/
theorem pointAdd_self_of_ne_zero {x y : Nat} (hy0 : y ≠ 0) (hylt : y < p) :
    pointAdd (some (x, y)) (some (x, y)) = some (Accel.curveDbl p x y) := by
  simp [pointAdd, two_mul_mod_ne_zero hy0 hylt]

/-- **The doubling bridge, packaged.**  On the machine's domain
    (`y` reduced) `pointAdd P P` is decided entirely by `y = 0`: the
    identity there, the accelerator's tangent doubling otherwise.  This
    is the exact shape of `pointDouble_spec`'s disjunctive post. -/
theorem pointAdd_self {x y : Nat} (hylt : y < p) :
    pointAdd (some (x, y)) (some (x, y))
      = if y = 0 then none else some (Accel.curveDbl p x y) := by
  by_cases hy0 : y = 0
  · subst hy0; simpa using pointAdd_self_zero x
  · simpa [hy0] using pointAdd_self_of_ne_zero hy0 hylt

/-- **The chord leg.**  Distinct abscissae take the chord rule, i.e. the
    accelerator's `Accel.curveAdd`.  Definitional; stated so the
    `secp256k1_point_add` lane can cite the case split rather than
    re-derive it.  Note NO reducedness hypothesis is needed: the SpecRef
    case split is on `x₁ = x₂` alone. -/
theorem pointAdd_of_fst_ne {x1 y1 x2 y2 : Nat} (hx : x1 ≠ x2) :
    pointAdd (some (x1, y1)) (some (x2, y2))
      = some (Accel.curveAdd p x1 y1 x2 y2) := by
  simp [pointAdd, hx]

-- ============================================================================
-- Non-vacuity: the `0 < y < p` bundle is satisfiable, and load-bearing
-- ============================================================================

/-- **Satisfiability witness.**  The generator's ordinate satisfies the
    `hy0`/`hylt` bundle of `pointAdd_self_of_ne_zero`, so that theorem is
    not vacuous. -/
theorem pointAdd_self_gen :
    pointAdd (some (gx, gy)) (some (gx, gy))
      = some (Accel.curveDbl p gx gy) :=
  pointAdd_self_of_ne_zero (by decide) (by decide)

/-- **The witness computes the right point.**  Composing
    `pointAdd_self_gen` with the accelerator's own generator KAT
    (`Accel.secp_curveDbl_kat`), the reference group law doubles `G` to
    the independently computed `2·G` — so the bridge's conclusion carries
    real arithmetic content, not just a reshuffled definition. -/
theorem pointAdd_self_gen_kat :
    pointAdd (some (gx, gy)) (some (gx, gy))
      = some (0xC6047F9441ED7D6D3045406E95C07CD85C778E4B8CEF3CA7ABAC09B95C709EE5,
              0x1AE168FEA63DC339A3C58419466CEAEEF7F632653266D0E1236431A950CFE52A)
    := by decide +kernel

/-- **Negative control for `hy0`.**  At `y = 0` the hypothesis of
    `pointAdd_self_of_ne_zero` is provably false AND its conclusion
    provably fails: the group law returns `𝒪` while the raw accelerator
    formula returns a point.  So `hy0` cannot be dropped. -/
theorem pointAdd_self_ne_curveDbl_of_zero (x : Nat) :
    pointAdd (some (x, 0)) (some (x, 0)) ≠ some (Accel.curveDbl p x 0) := by
  simp [pointAdd_self_zero]

/-- The doubling gate is FALSE at the unreduced `y = p` (the negative
    control's arithmetic core, isolated): `two_mul_mod_ne_zero` really
    does need `hylt`, and not merely for representability. -/
theorem two_mul_mod_eq_zero_at_p : (p + p) % p = 0 := by
  have h := Nat.mul_mod_right p 2
  have h2 : p * 2 = p + p := by omega
  rwa [h2] at h

/-- At the unreduced `y = p` the doubling gate FIRES (that is exactly
    `two_mul_mod_eq_zero_at_p`), so the group law returns `𝒪` — the same
    outcome as the genuine 2-torsion case. -/
theorem pointAdd_self_at_p (x : Nat) :
    pointAdd (some (x, p)) (some (x, p)) = none := by
  simp [pointAdd]

/-- **Negative control for `hylt`.**  At the unreduced `y = p` the
    reducedness hypothesis is provably false AND the conclusion provably
    fails, for the same reason as the `y = 0` control. -/
theorem pointAdd_self_ne_curveDbl_at_p (x : Nat) :
    pointAdd (some (x, p)) (some (x, p)) ≠ some (Accel.curveDbl p x p) := by
  simp [pointAdd_self_at_p]

end EvmAsm.Crypto.Secp256k1PointArith
