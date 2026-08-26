/-
  EvmAsm.Evm64.DivMod.Spec.N2V5C3LeOne

  `mulsubN4_c3_le_one_of_plus_two_of_v_lt`: under a `+2` trial overestimate AND a
  small divisor (`2 * val256 v < 2^256`, e.g. the n=2 normalized divisor where
  `v2 = v3 = 0` so `val256 v < 2^128`), the mulsub borrow `c3 ≤ 1`.

  Mirror of `mulsubN4_c3_le_two` (DivMulsubC3LeTwo) tightened by the small-divisor
  bound: `c3 * 2^256 ≤ val256(ms) + 2*val256 v < 2^256 + 2^256 = 2*2^256`.

  Combined with the borrow fact (`c3 ≠ 0`) this gives `c3 = 1` for the n=2
  addback branch, which discharges `callAddbackCarry2NzV5` via
  `callAddbackCarry2NzV5_of_c3_eq_one` (#7428) — letting the loop's call body drop
  the over-strong unconditional carry2nz hypothesis.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivMulsubC3LeTwo

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Under a `+2` overestimate and a small divisor (`2 * val256 v < 2^256`), the
    mulsub borrow `c3` is at most `1`. -/
theorem mulsubN4_c3_le_one_of_plus_two_of_v_lt {q v0 v1 v2 v3 u0 u1 u2 u3 : Word}
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : q.toNat ≤ val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2)
    (hv_small : 2 * val256 v0 v1 v2 v3 < 2 ^ 256) :
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat ≤ 1 := by
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
  have hc3_bound : c3.toNat * 2 ^ 256 < 2 * 2 ^ 256 := by nlinarith
  show c3.toNat ≤ 1
  have h256_pos : (0 : Nat) < 2 ^ 256 := by positivity
  have : c3.toNat < 2 := (Nat.mul_lt_mul_right h256_pos).mp hc3_bound
  omega

end EvmAsm.Evm64
