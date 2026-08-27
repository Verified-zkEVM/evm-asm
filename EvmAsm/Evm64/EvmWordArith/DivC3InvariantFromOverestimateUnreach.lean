/-
  EvmAsm.Evm64.EvmWordArith.DivC3InvariantFromOverestimateUnreach

  Compose the c3 ≤ 1 bound (mulsubN4_c3_le_one, from a `+1` trial
  overestimate) with the unreachability-frontier discharges
  (`MulsubMaxC3OneOfCarryZero_of_unreachable_carry0_c30` and BLT analog)
  to reduce each named c3 invariant to two named frontiers:
    1. A `+1` val256-level trial overestimate (for c3 ≤ 1),
    2. The Knuth-B unreachability of `(carry = 0 ∧ c3 = 0)`.

  The BLT side directly uses `divKTrialCallV4QHat`'s +1 bound (frontier:
  `DivKTrialCallV4QHatLeFloorPlusOne` composed with `Knuth128_64TopWindowLeVal256DivPlusOne`).

  The MAX side needs a +1 (not +2) bound on the saturated trial — that
  holds under stronger MAX-specific conditions; see the per-shape
  N{2,3}MaxOverestimate / DivN4Overestimate for the +2 forms.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivC3InvariantUnifiedCase
public import EvmAsm.Evm64.EvmWordArith.DivBltC3InvariantUnifiedCase
public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- MAX-side `MulsubMaxC3OneOfCarryZero` from a `+1` (tight) overestimate
    on the saturated trial plus the unreachability of `(carry = 0 ∧
    c3 = 0)`.

    Note: the `+1` overestimate is tighter than the `+2` provided by
    `max_trial_local_overestimate_n{2,3}_of_not_ult`.  This lemma applies
    only where a `+1` bound is known (typically n=4 with the saturated
    trial under runtime invariants), making it complementary to the n=2/n=3
    MAX bridges that use `+2`. -/
theorem MulsubMaxC3OneOfCarryZero_of_overestimate_plus_one_and_unreach
    (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : (signExtend12 (4095 : BitVec 12) : Word).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 1)
    (h_unreach : MulsubMaxC3UnreachableCarryZeroC3Zero v0 v1 v2 v3 u0 u1 u2 u3) :
    MulsubMaxC3OneOfCarryZero v0 v1 v2 v3 u0 u1 u2 u3 :=
  MulsubMaxC3OneOfCarryZero_of_unreachable_carry0_c30
    v0 v1 v2 v3 u0 u1 u2 u3 h_unreach
    (mulsubN4_c3_le_one hbnz hq_over)

/-- BLT-side `MulsubBltC3OneOfCarryZero` from a `+1` val256-level
    overestimate on `divKTrialCallV4QHat` (the natural form from
    Knuth-A v4 + Knuth Theorem A) plus the unreachability of `(carry = 0
    ∧ c3 = 0)`. -/
theorem MulsubBltC3OneOfCarryZero_of_overestimate_plus_one_and_unreach
    (uHi uLo vTop : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : (divKTrialCallV4QHat uHi uLo vTop).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 1)
    (h_unreach : MulsubBltC3UnreachableCarryZeroC3Zero uHi uLo vTop
      v0 v1 v2 v3 u0 u1 u2 u3) :
    MulsubBltC3OneOfCarryZero uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 :=
  MulsubBltC3OneOfCarryZero_of_unreachable_carry0_c30
    uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 h_unreach
    (mulsubN4_c3_le_one hbnz hq_over)

end EvmAsm.Evm64
