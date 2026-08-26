/-
  EvmAsm.Evm64.DivMod.Spec.N3V5CallCarryOfCallShape

  `n3_call_addback_carry2_nz_of_borrow_of_call_shape`: the n=3 call-regime
  second-addback carry obligation on a `v3=0` three-limb divisor / four-limb
  window, from the normalized top divisor limb (`v2 ≥ 2^63`), the call regime
  (`ult u3 v2`), and the runtime borrow.  Concludes the generic
  `isAddbackCarry2Nz (divKTrialCallV5QHat u3 u2 v2) …` form — which is
  definitionally `loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 0 u0 u1 u2 u3 uTop`
  (the form the n3 `selectedCarry` dispatch (#7520) consumes; the from-shape
  assembly bridges it by defeq).  n3 mirror of
  `callAddbackCarry2NzV5_of_borrow_of_call_shape`, reusing the n3 call trial
  overestimate (`n3_window_div_le_val256_div_plus_two_v5`, #7485) + the generic
  c3≤1 / carry-from-overestimate lemmas.  Call branch of bead 9.3.3.3.
-/

module

public import EvmAsm.Evm64.EvmWordArith.KnuthAFloorWindowN3
public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate
public import EvmAsm.Evm64.DivMod.Spec.N2V5C3LeOne
public import EvmAsm.Evm64.DivMod.Spec.N3V5HvSmall

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- `isAddbackCarry2Nz (divKTrialCallV5QHat u3 u2 v2) …` (= `loopBodyN3CallAddbackCarry2NzV5`)
    on a `v3=0` three-limb divisor / four-limb window, from the call regime, the
    normalized top divisor limb, and the runtime borrow. -/
theorem n3_call_addback_carry2_nz_of_borrow_of_call_shape
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (hv2_norm : v2.toNat ≥ 2 ^ 63)
    (hcall : BitVec.ult u3 v2)
    (hborrow : BitVec.ult uTop
      (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3) = true) :
    isAddbackCarry2Nz (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 uTop := by
  have hcallNat : u3.toNat < v2.toNat := by
    rw [BitVec.ult] at hcall; exact of_decide_eq_true hcall
  have hbnz : v0 ||| v1 ||| v2 ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have hv2z : v2 = 0 := (BitVec.or_eq_zero_iff.mp h2).2
    rw [hv2z] at hv2_norm
    simp at hv2_norm
  have hq_over : (divKTrialCallV5QHat u3 u2 v2).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 0 + 2 :=
    n3_window_div_le_val256_div_plus_two_v5 v0 v1 v2 u0 u1 u2 u3 hv2_norm hcallNat
  have hle1 := mulsubN4_c3_le_one_of_plus_two_of_v_lt hbnz hq_over
    (n3_two_val256_v_lt_pow256 v0 v1 v2)
  have hne0 : (mulsubN4 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 ≠ 0 := by
    intro h0
    unfold mulsubN4_c3 at hborrow
    rw [h0] at hborrow
    have : ¬ BitVec.ult uTop (0 : Word) := by rw [BitVec.ult_eq_decide]; simp
    exact this hborrow
  have hne0' :
      (mulsubN4 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2.toNat ≠ 0 := by
    intro hz
    exact hne0 (BitVec.eq_of_toNat_eq (by rw [hz]; rfl))
  have hc3eq : (mulsubN4 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 = 1 := by
    apply BitVec.eq_of_toNat_eq
    show (mulsubN4 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2.toNat = 1
    omega
  exact isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero
    (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 uTop hbnz hq_over (fun _ => hc3eq)

end EvmAsm.Evm64
