/-
  EvmAsm.Evm64.EvmWordArith.DivN4SecondCarryGen

  U4-general second-addback carry: under the val256 `+2` overestimate against the
  FULL five-limb dividend `uTop·2^256 + val256 u`, the borrow `c3 = uTop + 1`, and a
  zero first-addback carry, the SECOND addback carry is `1`.

  U4-general counterpart of `addbackN4_second_carry_one` (DivN4Overestimate),
  which is `c3 = 1` / `U4 = 0`-specific.  Same clean val256 bookkeeping:
  from `mulsubN4_val256_eq` (with `c3 = uTop + 1`) and `q·v ≤ (uTop·2^256 +
  val256 u) + 2·v`, one gets `val256(ms.result) + 2·v ≥ 2^256`, hence the first
  addback (carry = 0) leaves `val256(ab.result) + v ≥ 2^256`, so the second
  addback overflows (`carry2 = 1`).

  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- U4-general: second-addback carry is `1`, under the full-dividend `+2`
    overestimate, `c3 = uTop + 1`, and a zero first-addback carry. -/
theorem addbackN4_second_carry_one_gen (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : q.toNat ≤
      (uTop.toNat * 2 ^ 256 + val256 u0 u1 u2 u3) / val256 v0 v1 v2 v3 + 2)
    (hc3 : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = uTop.toNat + 1)
    (hcarry_zero : (addbackN4_carry
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
      v0 v1 v2 v3) = 0) :
    let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 v0 v1 v2 v3
    (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3).toNat = 1 := by
  intro ms ab
  have hmulsub := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only [] at hmulsub
  rw [hc3] at hmulsub
  have hab1 := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 v0 v1 v2 v3
  simp only [] at hab1
  have hc1_val : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3).toNat = 0 := by
    rw [hcarry_zero]; decide
  rw [hc1_val] at hab1
  have hab' := addbackN4_val256_eq ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3
  simp only [] at hab'
  have hvpos := val256_pos_of_or_ne_zero hbnz
  have hmsb := val256_bound ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
  have habb := val256_bound ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1
  have habrb := val256_bound
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).1
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).2.1
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).2.2.1
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).2.2.2.1
  have hdiv_mul_le :
      (uTop.toNat * 2 ^ 256 + val256 u0 u1 u2 u3) / val256 v0 v1 v2 v3 * val256 v0 v1 v2 v3 ≤
        uTop.toNat * 2 ^ 256 + val256 u0 u1 u2 u3 := Nat.div_mul_le_self _ _
  have hqv_le : q.toNat * val256 v0 v1 v2 v3 ≤
      (uTop.toNat * 2 ^ 256 + val256 u0 u1 u2 u3) + 2 * val256 v0 v1 v2 v3 := by
    calc q.toNat * val256 v0 v1 v2 v3
        ≤ ((uTop.toNat * 2 ^ 256 + val256 u0 u1 u2 u3) / val256 v0 v1 v2 v3 + 2) *
            val256 v0 v1 v2 v3 := Nat.mul_le_mul_right _ hq_over
      _ = (uTop.toNat * 2 ^ 256 + val256 u0 u1 u2 u3) / val256 v0 v1 v2 v3 * val256 v0 v1 v2 v3 +
            2 * val256 v0 v1 v2 v3 := by ring
      _ ≤ (uTop.toNat * 2 ^ 256 + val256 u0 u1 u2 u3) + 2 * val256 v0 v1 v2 v3 :=
          Nat.add_le_add_right hdiv_mul_le _
  -- val256(ms.result) + 2v ≥ 2^256.
  have h_ge : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 + 2 * val256 v0 v1 v2 v3 ≥ 2 ^ 256 := by
    nlinarith [hmulsub, hqv_le]
  -- val256(ab.result) + v ≥ 2^256.
  have h_ab1_v_ge : val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 + val256 v0 v1 v2 v3 ≥ 2 ^ 256 := by
    nlinarith [hab1, h_ge]
  set carry2 := (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3).toNat with hc2def
  have hc2_lt : carry2 * 2 ^ 256 < 2 * 2 ^ 256 := by nlinarith [hab', habb, hvpos]
  have hc2_ge : carry2 ≥ 1 := by
    by_contra h
    have hc2_zero : carry2 = 0 := by omega
    rw [hc2_zero] at hab'
    nlinarith [hab', h_ab1_v_ge, habrb]
  have h256_pos : (0 : Nat) < 2 ^ 256 := by positivity
  have hlt2 : carry2 < 2 := (Nat.mul_lt_mul_right h256_pos).mp hc2_lt
  omega

end EvmAsm.Evm64
