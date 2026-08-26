/-
  EvmAsm.Evm64.DivMod.Spec.N3V5MaxCarryOfMaxShape

  `isAddbackCarry2NzN3Max_of_borrow_of_max_shape`: the n=3 max-regime second-addback
  carry obligation on a `v3=0` three-limb divisor / four-limb window, from the
  normalized top divisor limb (`v2 ≥ 2^63`), the max regime (`¬ ult u3 v2`), and
  the runtime borrow.  n3 mirror of `isAddbackCarry2NzN2Max_of_borrow_of_max_shape`,
  reusing the n3 max trial overestimate (`max_trial_local_overestimate_n3_of_not_ult`)
  + the generic c3≤1 / carry-from-overestimate lemmas.  This is the max branch the
  n=3 carry-from-shape (bead 9.3.3.3) feeds to the `selectedCarry` dispatch (#7520).
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN3MaxOverestimate
public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate
public import EvmAsm.Evm64.DivMod.Spec.N2V5C3LeOne
public import EvmAsm.Evm64.DivMod.Spec.N3V5HvSmall

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- `isAddbackCarry2NzN3Max` on a `v3=0` three-limb divisor / four-limb window,
    from the max regime, the normalized top divisor limb, and the runtime borrow. -/
theorem isAddbackCarry2NzN3Max_of_borrow_of_max_shape
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (hv2_norm : v2.toNat ≥ 2 ^ 63)
    (hbltu : ¬ BitVec.ult u3 v2)
    (hborrow : BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 0 u0 u1 u2 u3) = true) :
    isAddbackCarry2NzN3Max v0 v1 v2 0 u0 u1 u2 u3 uTop := by
  unfold isAddbackCarry2NzN3Max
  have hbnz : v0 ||| v1 ||| v2 ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have hv2z : v2 = 0 := (BitVec.or_eq_zero_iff.mp h2).2
    rw [hv2z] at hv2_norm
    simp at hv2_norm
  have hq_over : (signExtend12 (4095 : BitVec 12) : Word).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 0 + 2 :=
    max_trial_local_overestimate_n3_of_not_ult v0 v1 v2 u0 u1 u2 u3 hv2_norm hbltu
  have hle1 := mulsubN4_c3_le_one_of_plus_two_of_v_lt hbnz hq_over
    (n3_two_val256_v_lt_pow256 v0 v1 v2)
  have hne0 : (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 ≠ 0 := by
    intro h0
    unfold mulsubN4_c3 at hborrow
    rw [h0] at hborrow
    have : ¬ BitVec.ult uTop (0 : Word) := by rw [BitVec.ult_eq_decide]; simp
    exact this hborrow
  have hne0' :
      (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2.toNat ≠ 0 := by
    intro hz
    exact hne0 (BitVec.eq_of_toNat_eq (by rw [hz]; rfl))
  have hc3eq : (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 = 1 := by
    apply BitVec.eq_of_toNat_eq
    show (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2.toNat = 1
    omega
  exact isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero
    (signExtend12 4095 : Word) v0 v1 v2 0 u0 u1 u2 u3 uTop hbnz hq_over (fun _ => hc3eq)

end EvmAsm.Evm64
