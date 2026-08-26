/-
  EvmAsm.Evm64.EvmWordArith.DivBltC3Invariant

  BLT-path analog of `MulsubMaxC3OneOfCarryZero` (see
  `DivMaxC3Invariant`).

  In the SELECTED BLT path, the per-iteration trial is
  `divKTrialCallV4QHat uHi uLo vTop` (a 128/64 Knuth quotient with the v4
  2-correction).  The carry-2-nz obligation expanded at this trial has the
  same shape as MAX, but parametrised by the local `(uHi, uLo, vTop)`.

  Closing this single predicate from selected-path reachability simultaneously
  discharges the BLT-side carry obligations of:
    • N2 j=2 BLT (bead `7.1.6.2.3.2.1.1.1`)
    • N2 j=1 BLT (bead `7.1.6.2.3.2.1.2.1`)
    • N2 j=0 BLT (bead `7.1.6.2.3.2.1.3.1`)
    • N3 j=1 BLT (bead `7.1.6.3.16.1`)
    • N3 j=0 BLT (bead `7.1.6.3.16.3`)
    • N1 call-path leaves analogous to the if-borrow consumers

  Like the MAX predicate, this is not derivable from shape facts alone — the
  per-iteration v4 spec (`div128_v4_spec` / Algorithm-A correctness for
  `divKTrialCallV4QHat`) provides the structural facts needed.

  This file names the predicate so future work has a single attackable
  target for the BLT side, paralleling `MulsubMaxC3OneOfCarryZero` on the
  MAX side.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Algorithm

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The unified BLT-path c3 reachability invariant: at the v4 trial
    `qHat = divKTrialCallV4QHat uHi uLo vTop`, a zero first-addback carry
    forces the mulsub carry `c3` to be one.

    Parametrised by the local `(uHi, uLo, vTop)` triple at which the v4
    trial is evaluated.  At each outer iteration of the N1/N2/N3 BLT path,
    this triple equals `(u_top, u_top_minus_1, v_pivot)` for the appropriate
    pivot limb (`v0` for N1, `v1` for N2, `v2` for N3).

    Specialises to the third hypothesis of
    `isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero` when `q` there
    is `divKTrialCallV4QHat uHi uLo vTop`. -/
def MulsubBltC3OneOfCarryZero (uHi uLo vTop : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 : Word) : Prop :=
  let qHat := divKTrialCallV4QHat uHi uLo vTop
  addbackN4_carry
      (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).1
      (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.1
      (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
      (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
      v0 v1 v2 v3 = 0 →
    (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1

theorem MulsubBltC3OneOfCarryZero_unfold (uHi uLo vTop : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 : Word) :
    MulsubBltC3OneOfCarryZero uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 ↔
      (let qHat := divKTrialCallV4QHat uHi uLo vTop
       addbackN4_carry
           (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).1
           (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.1
           (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
           (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
           v0 v1 v2 v3 = 0 →
       (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1) :=
  Iff.rfl

end EvmAsm.Evm64
