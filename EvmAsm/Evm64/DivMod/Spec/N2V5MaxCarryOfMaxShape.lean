/-
  EvmAsm.Evm64.DivMod.Spec.N2V5MaxCarryOfMaxShape

  The per-digit MAX-carry discharge for the n=2 lane: from the max regime
  (`¬ u2 < v1`, i.e. `bltu = false`) + the normalized top divisor limb
  (`v1 ≥ 2^63`) + the runtime borrow, derive `isAddbackCarry2NzN2Max` on a
  `v2=v3=0`, `u3=0` window.  Max analog of the call discharge (#7454): the
  saturated trial `2^64-1` can overestimate the capped digit by 1, so the max
  digit genuinely can borrow; in the borrow case the n=2 small-divisor `c3 ≤ 1`
  bound (#7430) forces `c3 = 1` and the generic
  `isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero` (q = `signExtend12
  4095`) closes it, using the max `+2` overestimate
  `max_trial_local_overestimate_n2_of_not_ult`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5C3LeOne
import EvmAsm.Evm64.DivMod.Spec.N2V5ShapeBoundShared
import EvmAsm.Evm64.EvmWordArith.DivN2MaxOverestimate

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- `isAddbackCarry2NzN2Max` on a `v2=v3=0`, `u3=0` window, from the max regime,
    the normalized top divisor limb, and the runtime borrow. -/
theorem isAddbackCarry2NzN2Max_of_borrow_of_max_shape
    (v0 v1 u0 u1 u2 uTop : Word)
    (hv1_norm : v1.toNat ≥ 2 ^ 63)
    (hbltu : ¬ BitVec.ult u2 v1)
    (hborrow : BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 0 0 u0 u1 u2 0) = true) :
    isAddbackCarry2NzN2Max v0 v1 0 0 u0 u1 u2 0 uTop := by
  unfold isAddbackCarry2NzN2Max
  have hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hv1z : v1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hv1z] at hv1_norm
    simp at hv1_norm
  have hq_over : (signExtend12 (4095 : BitVec 12) : Word).toNat ≤
      val256 u0 u1 u2 0 / val256 v0 v1 0 0 + 2 :=
    max_trial_local_overestimate_n2_of_not_ult v0 v1 u0 u1 u2 hv1_norm hbltu
  have hle1 := mulsubN4_c3_le_one_of_plus_two_of_v_lt hbnz hq_over
    (n2_two_val256_v_lt_pow256 v0 v1)
  have hne0 : (mulsubN4 (signExtend12 4095 : Word) v0 v1 0 0 u0 u1 u2 0).2.2.2.2 ≠ 0 := by
    intro h0
    unfold mulsubN4_c3 at hborrow
    rw [h0] at hborrow
    have : ¬ BitVec.ult uTop (0 : Word) := by rw [BitVec.ult_eq_decide]; simp
    exact this hborrow
  have hne0' :
      (mulsubN4 (signExtend12 4095 : Word) v0 v1 0 0 u0 u1 u2 0).2.2.2.2.toNat ≠ 0 := by
    intro hz
    exact hne0 (BitVec.eq_of_toNat_eq (by rw [hz]; rfl))
  have hc3eq : (mulsubN4 (signExtend12 4095 : Word) v0 v1 0 0 u0 u1 u2 0).2.2.2.2 = 1 := by
    apply BitVec.eq_of_toNat_eq
    show (mulsubN4 (signExtend12 4095 : Word) v0 v1 0 0 u0 u1 u2 0).2.2.2.2.toNat = 1
    omega
  exact isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero
    (signExtend12 4095 : Word) v0 v1 0 0 u0 u1 u2 0 uTop hbnz hq_over (fun _ => hc3eq)

end EvmAsm.Evm64
