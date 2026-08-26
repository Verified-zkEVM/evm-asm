/-
  EvmAsm.Evm64.EvmWordArith.DivMulsubC3LeTwo

  `mulsubN4_c3_le_two`: the analog of the existing `mulsubN4_c3_le_one`
  (from `DivN4Overestimate`) under a `+2` (rather than `+1`) val256-level
  trial overestimate.

  This is the natural bound for the saturated trial `signExtend12 4095`
  under the n=2/n=3 MAX path conditions (where the existing
  `max_trial_local_overestimate_n{2,3}_of_not_ult` lemmas provide `+2`).
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- When the trial quotient overestimates by at most 2 (q ≤ ⌊u/v⌋ + 2),
    the mulsub borrow `c3` is at most 2.

    Proof structure mirrors `mulsubN4_c3_le_one`: from
    `mulsubN4_val256_eq`, `c3 * 2^256 = val256(un) + q*val256(v) - val256(u)`.
    With `q*val256(v) ≤ val256(u) + 2*val256(v)`, we get
    `c3 * 2^256 ≤ val256(un) + 2*val256(v) < 2^256 + 2*2^256 = 3*2^256`,
    hence `c3 ≤ 2`. -/
theorem mulsubN4_c3_le_two {q v0 v1 v2 v3 u0 u1 u2 u3 : Word}
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : q.toNat ≤ val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2) :
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat ≤ 2 := by
  let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  have hmulsub := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only [] at hmulsub
  have := val256_bound u0 u1 u2 u3
  have := val256_bound ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
  have := val256_bound v0 v1 v2 v3
  have := val256_pos_of_or_ne_zero hbnz
  have hdiv_mul_le : val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 *
      val256 v0 v1 v2 v3 ≤ val256 u0 u1 u2 u3 :=
    Nat.div_mul_le_self _ _
  have hqv_le : q.toNat * val256 v0 v1 v2 v3 ≤
      val256 u0 u1 u2 u3 + 2 * val256 v0 v1 v2 v3 := by
    calc q.toNat * val256 v0 v1 v2 v3
        ≤ (val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2) * val256 v0 v1 v2 v3 :=
          Nat.mul_le_mul_right _ hq_over
      _ = val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 * val256 v0 v1 v2 v3 +
          2 * val256 v0 v1 v2 v3 := by ring
      _ ≤ val256 u0 u1 u2 u3 + 2 * val256 v0 v1 v2 v3 :=
          Nat.add_le_add_right hdiv_mul_le _
  have hc3_bound : c3.toNat * 2^256 < 3 * 2^256 := by
    nlinarith
  show c3.toNat ≤ 2
  have h256_pos : (0 : Nat) < 2^256 := by positivity
  have : c3.toNat < 3 := (Nat.mul_lt_mul_right h256_pos).mp hc3_bound
  omega

end EvmAsm.Evm64
