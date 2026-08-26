/-
  EvmAsm.Evm64.EvmWordArith.DivMaxC3Invariant

  Named frontier predicate for the unified MAX-path c3 reachability invariant.

  The N{1,2,3}Max bridges in `DivN4Overestimate`, `DivN2MaxOverestimate`, and
  `DivN3MaxOverestimate` each reduce their `isAddbackCarry2N{1,2,3}Max`
  obligation to the same shape:

      addbackN4_carry (mulsubN4 (signExtend12 4095) v u).{1..4} v = 0 →
      (mulsubN4 (signExtend12 4095) v u).c3 = 1

  Closing this single predicate from selected-path reachability simultaneously
  discharges:
    • N2 j=2 MAX (bead `7.1.6.2.3.2.1.1.2`)
    • N2 j=1 MAX (bead `7.1.6.2.3.2.1.2.2`)
    • N3 j=1 MAX (bead `7.1.6.3.16.2`)
    • N3 j=0 MAX (bead `7.1.6.3.16.4`)
    • N1 max-path leaves under the if-borrow path (consumers of
      `isAddbackCarry2NzN1Max_of_not_ult_c3_one_of_carry_zero`)

  The predicate is FALSE in general from shape facts alone — see
  `Counterexamples.ceN1MaxLocal_c3_one_of_carry_zero_false`.  It requires the
  selected/reachable-path invariant carried by the per-iteration v4 spec
  (`div128_v4_spec`) along with the structural fact that, after normalisation,
  the saturated trial `qHat = 2^64 − 1` overshoots the true local quotient by
  at most 2 (the Knuth-B bound supplied by the per-shape `_overestimate`
  lemmas).

  This file does not prove the invariant; it only names the predicate and
  proves two things about it:
    • `MulsubMaxC3OneOfCarryZero_of_isAddbackCarry2Nz_input`: the invariant
      shape EQUALS the third hypothesis of
      `isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero` (rfl).
    • `MulsubMaxC3OneOfCarryZero_iff_n4_form`: stable iff with the same
      shape for n=4 callers (used by `DivN4Overestimate`).

  Future work: discharging `MulsubMaxC3OneOfCarryZero` from selected-path
  reachability is the single remaining MAX-path frontier — six bead leaves
  collapse to it.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The unified MAX-path c3 reachability invariant: at the saturated trial
    `qHat = 2^64 − 1`, a zero first-addback carry forces the mulsub carry
    `c3` to be one.

    Specialises to the third hypothesis of
    `isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero` when `q` there
    is `signExtend12 4095`. -/
def MulsubMaxC3OneOfCarryZero (v0 v1 v2 v3 u0 u1 u2 u3 : Word) : Prop :=
  addbackN4_carry
      (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).1
      (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.1
      (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
      (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
      v0 v1 v2 v3 = 0 →
    (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1

theorem MulsubMaxC3OneOfCarryZero_unfold (v0 v1 v2 v3 u0 u1 u2 u3 : Word) :
    MulsubMaxC3OneOfCarryZero v0 v1 v2 v3 u0 u1 u2 u3 ↔
      (addbackN4_carry
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 = 0 →
      (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1) :=
  Iff.rfl

end EvmAsm.Evm64
