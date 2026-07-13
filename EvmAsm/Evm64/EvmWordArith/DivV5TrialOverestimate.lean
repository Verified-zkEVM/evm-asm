/-
  EvmAsm.Evm64.EvmWordArith.DivV5TrialOverestimate

  v5 analog of `DivV4TrialOverestimate` — but DISCHARGED, not just named.

  The v4 frontier `DivKTrialCallV4QHatLeFloorPlusOne` (bead `9iqmw.7.1.4.1`)
  was the open obstruction gating `evm_div_stack_spec_unconditional`:
    `divKTrialCallV4QHat uHi uLo vTop ≤ (uHi·2^64 + uLo)/vTop + 1`
  under the call regime + normalisation. Under v4 it is FALSE in general
  (PR #7080's `+2` counterexample), which is precisely why bead `7.1.4.1`
  was impossible.

  Under v5 the capped Knuth-D quotient `div128Quot_v5` satisfies this bound
  unconditionally (V5.4.5, `div128Quot_v5_le_q_true_plus_one`), and
  `divKTrialCallV5QHat = div128Quot_v5`
  (`divKTrialCallV5QHat_eq_div128Quot_v5`). So the v5 frontier discharges
  directly. This is the core payoff of the V5 repair: the obstruction that
  was impossible under v4 holds under v5. The companion lower bound
  (`≥ floor`, from V5.5.3) is included for the BLT-path bridges.

  Bead `evm-asm-wbc4i.4.7`.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainD
import EvmAsm.Evm64.EvmWordArith.DivV4TrialVal256Composition
import EvmAsm.Evm64.EvmWordArith.DivKnuthATopWindowFits

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The v5 call-trial Knuth-A `+1` upper bound at `(uHi, uLo, vTop)`, the v5
    analog of `DivKTrialCallV4QHatLeFloorPlusOne`. Mirror predicate so
    downstream beads/PRs have a single attackable (now discharged) target. -/
def DivKTrialCallV5QHatLeFloorPlusOne (uHi uLo vTop : Word) : Prop :=
  (divKTrialCallV5QHat uHi uLo vTop).toNat ≤
    (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1

theorem DivKTrialCallV5QHatLeFloorPlusOne_unfold (uHi uLo vTop : Word) :
    DivKTrialCallV5QHatLeFloorPlusOne uHi uLo vTop ↔
      (divKTrialCallV5QHat uHi uLo vTop).toNat ≤
        (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1 :=
  Iff.rfl

/-- **The V5 payoff** (v5 analog of the impossible v4 bead `7.1.4.1`):
    `divKTrialCallV5QHat ≤ (uHi·2^64 + uLo)/vTop + 1` discharged
    unconditionally from V5.4.5, under just the call regime
    (`uHi < vTop`) + normalisation (`vTop ≥ 2^63`). -/
theorem divKTrialCallV5QHat_le_floor_plus_one
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5QHat uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1 := by
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  exact div128Quot_v5_le_q_true_plus_one uHi uLo vTop hvTop_ge huHi_lt_vTop

/-- Named-predicate form of `divKTrialCallV5QHat_le_floor_plus_one`. -/
theorem DivKTrialCallV5QHatLeFloorPlusOne_of_norm
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    DivKTrialCallV5QHatLeFloorPlusOne uHi uLo vTop :=
  divKTrialCallV5QHat_le_floor_plus_one uHi uLo vTop hvTop_ge huHi_lt_vTop

/-- Companion lower bound (from V5.5.3): `(uHi·2^64+uLo)/vTop ≤
    divKTrialCallV5QHat`. Together with the `+1` upper bound this pins the
    v5 trial quotient to within 1 of the floor — the input to the BLT-path
    `Carry2Nz` bridges. -/
theorem divKTrialCallV5QHat_ge_floor
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat ≤
      (divKTrialCallV5QHat uHi uLo vTop).toNat := by
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  exact div128Quot_v5_ge_q_true uHi uLo vTop hvTop_ge huHi_lt_vTop

/-- **v5 val256 composition** (mirror of `divKTrialCallV4QHat_le_val256_div_plus_two`):
    from the v5 frontier `+1` bound and the version-agnostic Knuth Theorem A
    top-window bridge `Knuth128_64TopWindowLeVal256DivPlusOne`, derive the
    val256-level `+2` overestimate consumed by the BLT-path bridges
    (`loopBodyN{2,3}CallAddbackCarry2Nz*_of_overestimate_c3`).

    The `Knuth128_64TopWindowLeVal256DivPlusOne` bridge is version-agnostic
    (a pure floor-division fact), so it is reused directly from the v4 file. -/
theorem divKTrialCallV5QHat_le_val256_div_plus_two
    (uHi uLo vTop : Word) (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (h_v5 : DivKTrialCallV5QHatLeFloorPlusOne uHi uLo vTop)
    (h_knuth : Knuth128_64TopWindowLeVal256DivPlusOne uHi uLo vTop
      v0 v1 v2 v3 u0 u1 u2 u3) :
    (divKTrialCallV5QHat uHi uLo vTop).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2 := by
  unfold DivKTrialCallV5QHatLeFloorPlusOne at h_v5
  unfold Knuth128_64TopWindowLeVal256DivPlusOne at h_knuth
  omega

/-- The val256 `+2` overestimate discharged under the call regime +
    normalisation (the v5 frontier is unconditional), leaving only the
    version-agnostic Knuth top-window bridge as a hypothesis. -/
theorem divKTrialCallV5QHat_le_val256_div_plus_two_of_norm
    (uHi uLo vTop : Word) (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_knuth : Knuth128_64TopWindowLeVal256DivPlusOne uHi uLo vTop
      v0 v1 v2 v3 u0 u1 u2 u3) :
    (divKTrialCallV5QHat uHi uLo vTop).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2 :=
  divKTrialCallV5QHat_le_val256_div_plus_two uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3
    (DivKTrialCallV5QHatLeFloorPlusOne_of_norm uHi uLo vTop hvTop_ge huHi_lt_vTop)
    h_knuth

/-- **End-to-end v5 `+2` val256 overestimate** under purely structural
    conditions — the v5 analog of
    `divKTrialCallV4QHat_le_val256_div_plus_two_of_exact_and_top_window_fits_v_eq_vTop`,
    but STRICTLY WEAKER PREMISES: the v4 version needs `h_exact`
    (`divKTrialCallV4QHat = exact floor`, hard to establish); the v5 version
    needs only normalisation (`vTop ≥ 2^63`, `uHi < vTop`) because the v5
    frontier is unconditional. The remaining conditions
    (`val256(v) = vTop`, top-window-fits-`val256(u)`) are the version-agnostic
    Knuth-A structural conditions, discharged by
    `Knuth128_64TopWindowLeVal256DivPlusOne_of_top_window_fits_val256_and_v_eq_vTop`.

    This is the val256 overestimate consumed by the BLT-path
    `loopBodyN{2,3}CallAddbackCarry2Nz*_of_overestimate_c3` bridges. -/
theorem divKTrialCallV5QHat_le_val256_div_plus_two_of_norm_and_top_window_fits_v_eq_vTop
    (uHi uLo vTop : Word) (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_v_eq : val256 v0 v1 v2 v3 = vTop.toNat)
    (h_u_fits : (uHi.toNat * 2^64 + uLo.toNat) * 2^128 ≤ val256 u0 u1 u2 u3) :
    (divKTrialCallV5QHat uHi uLo vTop).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2 :=
  divKTrialCallV5QHat_le_val256_div_plus_two_of_norm uHi uLo vTop
    v0 v1 v2 v3 u0 u1 u2 u3 hvTop_ge huHi_lt_vTop
    (Knuth128_64TopWindowLeVal256DivPlusOne_of_top_window_fits_val256_and_v_eq_vTop
      uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 h_v_eq h_u_fits)

/-- **GENERAL multi-limb n4 `+2` overestimate** (no single-limb / top-window-fits
    restriction): from `isCallTrialN4` alone, `divKTrialCallV5QHat ≤
    val256(a)/val256(b) + 2`, on the actual clz-normalized algorithm limbs.

    This is the bound the n4 addback carry bridge
    (`isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero`) consumes — and
    the genuine `+2` (not the `+3` of `…_plus_three_of_call`), now achievable
    because `div128Quot_v5 = floor` EXACTLY (`div128Quot_v5_eq_q_true`): the v5
    trial equals the raw 128/64 floor, so it inherits the floor's `+2` Knuth-B
    bound (`knuth_theorem_b_from_clz`) directly with no `+1` correction slack. -/
theorem divKTrialCallV5QHat_le_val256_div_plus_two_of_call
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    (divKTrialCallV5QHat
        (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))
        ((a3 <<< ((clzResult b3).1.toNat % 64)) |||
          (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
        ((b3 <<< ((clzResult b3).1.toNat % 64)) |||
          (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))).toNat ≤
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 + 2 := by
  have hb3prime := b3_prime_ge_pow63 b3 b2 hb3nz
    (signExtend12 (0 : BitVec 12) - (clzResult b3).1)
  have hu4_lt := isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_eq :
      (divKTrialCallV5QHat
        (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))
        ((a3 <<< ((clzResult b3).1.toNat % 64)) |||
          (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
        ((b3 <<< ((clzResult b3).1.toNat % 64)) |||
          (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))).toNat =
      ((a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)).toNat * 2^64 +
        ((a3 <<< ((clzResult b3).1.toNat % 64)) |||
          (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))).toNat) /
      ((b3 <<< ((clzResult b3).1.toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))).toNat := by
    rw [divKTrialCallV5QHat_eq_div128Quot_v5]
    exact div128Quot_v5_eq_q_true _ _ _ hb3prime hu4_lt
  rw [h_eq]
  exact knuth_theorem_b_from_clz a0 a1 a2 a3 b0 b1 b2 b3 hb3nz hshift_nz hcall

/-- **The v5 trial is the exact floor**: `divKTrialCallV5QHat = (uHi·2^64+uLo)/vTop`
    under the call regime + normalisation. The QHat-level statement of
    `div128Quot_v5_eq_q_true` (via `divKTrialCallV5QHat_eq_div128Quot_v5`);
    strengthens `divKTrialCallV5QHat_eq_floor_or_succ` (`∈ {floor, floor+1}`) to
    exact equality. Downstream dispatcher reasoning can treat the trial as the
    exact 128/64 quotient. -/
theorem divKTrialCallV5QHat_eq_floor
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5QHat uHi uLo vTop).toNat =
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat := by
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  exact div128Quot_v5_eq_q_true uHi uLo vTop hvTop_ge huHi_lt_vTop

/-- **Honest GENERAL multi-limb n4 trial bound** (no single-limb / top-window-fits
    restriction): from `isCallTrialN4` alone, `divKTrialCallV5QHat ≤
    val256(a)/val256(b) + 3`, on the actual clz-normalized algorithm limbs
    (`U4 = a3>>>(64-shift)`, `U3' / B3'` the funnel-shifted top limbs).

    Composes the v5 frontier `div128Quot_v5 ≤ floor + 1` (V5.4.5, via
    `divKTrialCallV5QHat_le_floor_plus_one`) with the version-agnostic
    multi-limb Knuth-B `(U4·2^64+U3')/B3' ≤ val256(a)/val256(b) + 2`
    (`knuth_theorem_b_from_clz`, KnuthTheoremB.lean).

    NOTE: this is `+3`, not `+2`. The consumable `+2` form
    (`divKTrialCallV5QHat_le_val256_div_plus_two`) requires the **+1**
    top-window bridge `Knuth128_64TopWindowLeVal256DivPlusOne`, which holds
    only when the divisor is single-limb-dominated (`val256(v) = vTop`). For a
    genuinely multi-limb divisor, Knuth-B yields only `floor ≤ +2`, so the
    naive `floor+1` chain gives `+3`. Closing the gap to `+2` for multi-limb n4
    requires `div128Quot_v5 = floor` EXACTLY (dropping the `+1` of V5.4.5),
    which ties into the mulsub/addback-level correction analysis rather than
    the trial bound. This lemma records the honest available bound. Bead
    `evm-asm-wbc4i.8.2.2.3`. -/
theorem divKTrialCallV5QHat_le_val256_div_plus_three_of_call
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    (divKTrialCallV5QHat
        (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))
        ((a3 <<< ((clzResult b3).1.toNat % 64)) |||
          (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
        ((b3 <<< ((clzResult b3).1.toNat % 64)) |||
          (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))).toNat ≤
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 + 3 := by
  have hb3prime := b3_prime_ge_pow63 b3 b2 hb3nz
    (signExtend12 (0 : BitVec 12) - (clzResult b3).1)
  have hu4_lt := isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_v5 := divKTrialCallV5QHat_le_floor_plus_one
    (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))
    ((a3 <<< ((clzResult b3).1.toNat % 64)) |||
      (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
    ((b3 <<< ((clzResult b3).1.toNat % 64)) |||
      (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
    hb3prime hu4_lt
  have h_knuth := knuth_theorem_b_from_clz a0 a1 a2 a3 b0 b1 b2 b3 hb3nz hshift_nz hcall
  omega

/-- **The v5 trial is within 1 of the exact floor**: `divKTrialCallV5QHat ∈
    {floor, floor+1}` under the call regime + normalisation. Combines the `+1`
    upper bound (V5.4.5, `divKTrialCallV5QHat_le_floor_plus_one`) with the
    `≥ floor` lower bound (V5.5.3, `divKTrialCallV5QHat_ge_floor`).

    This is the precise input to the loop-body mulsub/addback correction: the
    per-digit trial overshoots the true digit by at most 1, so a single
    add-back suffices to correct it.

    NOTE: whether `div128Quot_v5 = floor` EXACTLY — which would tighten the
    val256 bound from `+3` (`…_plus_three_of_call`) to `+2` purely at the trial
    level — is NOT established. `div128Quot_phase2b_q0'` does at most one
    decrement while the pre-correction half-quotient `Q0c` can be `q_true_0+2`,
    so the residual `+1` is corrected at the LOOP level (the iteration applies a
    second phase-2b pass), not inside the subroutine. (Empirically `= floor`
    over 1600+ scanned cases incl. targeted Knuth max-overshoot, but unproven.) -/
theorem divKTrialCallV5QHat_eq_floor_or_succ
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5QHat uHi uLo vTop).toNat
        = (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat ∨
      (divKTrialCallV5QHat uHi uLo vTop).toNat
        = (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1 := by
  have hle := divKTrialCallV5QHat_le_floor_plus_one uHi uLo vTop hvTop_ge huHi_lt_vTop
  have hge := divKTrialCallV5QHat_ge_floor uHi uLo vTop hvTop_ge huHi_lt_vTop
  omega

end EvmAsm.Evm64
