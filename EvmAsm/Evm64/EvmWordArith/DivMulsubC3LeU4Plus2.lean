/-
  EvmAsm.Evm64.EvmWordArith.DivMulsubC3LeU4Plus2

  `mulsubN4_c3_le_u4_plus_two`: the U4-general version of `mulsubN4_c3_le_two`.

  The n=4 single-digit Knuth division operates on a FIVE-limb normalized dividend
  `U4·2^256 + val256 u0..u3`, but the inner `mulsubN4` is a four-limb mul-sub
  (over `u0..u3`); the overflow limb `U4` is reconciled against the four-limb
  borrow `c3` afterwards (the skip/addback branch test is `u4 < c3`).

  Under the val256 `+2` overestimate against the FULL five-limb dividend
  (`q ≤ (U4·2^256 + val256 u)/val256 v + 2`, the unconditional n=4 trial bound
  `divKTrialCallV5QHat_le_val256_div_plus_two_of_call`, #7219), the four-limb borrow
  satisfies `c3 ≤ U4 + 2` — NOT `c3 ≤ 2`.  The special case `U4 = 0` recovers
  `mulsubN4_c3_le_two`.

  Consequence (used by the addback semantic): on the addback branch `u4 < c3`,
  the number of corrective addbacks is `c3 - u4 ≤ 2`, so the double-addback
  (carry2) path corrects the trial for ANY `U4`, not only `U4 = 0`.
  Bead `evm-asm-wbc4i.8.2.2.4`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivMulsubC3LeTwo

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- When the trial quotient overestimates the FULL five-limb dividend
    `U4·2^256 + val256 u` by at most 2, the four-limb `mulsubN4` borrow `c3`
    is at most `U4 + 2`.

    From `mulsubN4_val256_eq`, `val256 u + c3·2^256 = val256 result + q·val256 v`,
    hence `c3·2^256 = val256 result + q·val256 v - val256 u`.  With
    `q·val256 v ≤ (U4·2^256 + val256 u) + 2·val256 v` and the four-limb bounds
    `val256 result, val256 v < 2^256`, this gives
    `c3·2^256 < 2^256 + U4·2^256 + 2·2^256 = (U4 + 3)·2^256`, so `c3 ≤ U4 + 2`. -/
theorem mulsubN4_c3_le_u4_plus_two {q v0 v1 v2 v3 u0 u1 u2 u3 : Word} (u4 : Nat)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : q.toNat ≤
      (u4 * 2 ^ 256 + val256 u0 u1 u2 u3) / val256 v0 v1 v2 v3 + 2) :
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat ≤ u4 + 2 := by
  let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  have hmulsub := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only [] at hmulsub
  have := val256_bound u0 u1 u2 u3
  have := val256_bound ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
  have := val256_bound v0 v1 v2 v3
  have := val256_pos_of_or_ne_zero hbnz
  have hdiv_mul_le :
      (u4 * 2 ^ 256 + val256 u0 u1 u2 u3) / val256 v0 v1 v2 v3 *
        val256 v0 v1 v2 v3 ≤ u4 * 2 ^ 256 + val256 u0 u1 u2 u3 :=
    Nat.div_mul_le_self _ _
  have hqv_le : q.toNat * val256 v0 v1 v2 v3 ≤
      (u4 * 2 ^ 256 + val256 u0 u1 u2 u3) + 2 * val256 v0 v1 v2 v3 := by
    calc q.toNat * val256 v0 v1 v2 v3
        ≤ ((u4 * 2 ^ 256 + val256 u0 u1 u2 u3) / val256 v0 v1 v2 v3 + 2) *
            val256 v0 v1 v2 v3 :=
          Nat.mul_le_mul_right _ hq_over
      _ = (u4 * 2 ^ 256 + val256 u0 u1 u2 u3) / val256 v0 v1 v2 v3 *
            val256 v0 v1 v2 v3 + 2 * val256 v0 v1 v2 v3 := by ring
      _ ≤ (u4 * 2 ^ 256 + val256 u0 u1 u2 u3) + 2 * val256 v0 v1 v2 v3 :=
          Nat.add_le_add_right hdiv_mul_le _
  have hc3_bound : c3.toNat * 2 ^ 256 < (u4 + 3) * 2 ^ 256 := by
    nlinarith
  show c3.toNat ≤ u4 + 2
  have h256_pos : (0 : Nat) < 2 ^ 256 := by positivity
  have : c3.toNat < u4 + 3 := (Nat.mul_lt_mul_right h256_pos).mp hc3_bound
  omega

end EvmAsm.Evm64
