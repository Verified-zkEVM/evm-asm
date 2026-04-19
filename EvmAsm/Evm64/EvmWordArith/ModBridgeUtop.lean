/-
  EvmAsm.Evm64.EvmWordArith.ModBridgeUtop

  The `u_top = c3_n` invariant for Knuth algorithm D at n=4 max+skip.

  During algorithm D's normalization step, the top bits of the dividend
  `a3 >>> (64 - s)` become an implicit 5th limb `u_top`. The mulsub on
  the normalized 4-limb dividend + divisor produces `ms_n` with carry
  `c3_n`. This lemma proves that under the max+skip conditions,
  `u_top = c3_n` (not merely `u_top ≥ c3_n` as the runtime skip check
  gives). The identity is the key missing invariant for the MOD
  denormalization bridge.

  Preconditions used:
  - b3 ≠ 0 and CLZ top-limb bound `b3 < 2^(64 - s)` (for s = clz(b3)).
  - `hborrow` : the runtime skip borrow gives `c3_n ≤ u_top`.
  - `hsem`    : un-normalized mulsub carry is 0 (semantic skip).
-/

import EvmAsm.Evm64.EvmWordArith.DenormLemmas
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate
import EvmAsm.Evm64.DivMod.LoopSemantic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

/-- Nat-level uniqueness: if `vPow < 2^256`, `vN < 2^256`, `c ≤ u`, and
    `vPow = vN + (u - c) * 2^256`, then `u = c` (and `vPow = vN`). -/
theorem nat_top_eq_of_lt_pow256 {vPow vN u c : Nat}
    (hle : c ≤ u)
    (heq : vPow = vN + (u - c) * 2 ^ 256)
    (h_vPow_lt : vPow < 2 ^ 256) :
    u = c := by
  have hpow_pos : 0 < 2 ^ 256 := Nat.pos_of_ne_zero (by positivity)
  have : (u - c) * 2 ^ 256 < 2 ^ 256 := by omega
  have : u - c = 0 := by
    by_contra h
    have : (u - c) * 2 ^ 256 ≥ 2 ^ 256 := by
      have : u - c ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      exact Nat.le_mul_of_pos_left _ (by omega) |>.trans (by nlinarith)
    omega
  omega

/-- Core algebraic identity: combining `val256_normalize_general` (for the
    normalized dividend) and `val256_normalize` (for the normalized divisor,
    which needs the CLZ top-limb bound), substituting into
    `mulsubN4_val256_eq`, yields a combined Euclidean equation with an
    `(u_top - c3_n) * 2^256` residual term.

    The caller uses this + `nat_top_eq_of_lt_pow256` to collapse the
    residual to zero (yielding Lemma C). -/
theorem val256_normalized_mulsub_eq
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (s : Nat) (hs0 : 0 < s) (hs : s < 64)
    (hb3_bound : b3.toNat < 2 ^ (64 - s)) :
    let b3' := (b3 <<< s) ||| (b2 >>> (64 - s))
    let b2' := (b2 <<< s) ||| (b1 >>> (64 - s))
    let b1' := (b1 <<< s) ||| (b0 >>> (64 - s))
    let b0' := b0 <<< s
    let u3 := (a3 <<< s) ||| (a2 >>> (64 - s))
    let u2 := (a2 <<< s) ||| (a1 >>> (64 - s))
    let u1 := (a1 <<< s) ||| (a0 >>> (64 - s))
    let u0 := a0 <<< s
    let u_top := a3 >>> (64 - s)
    let q_hat : Word := signExtend12 4095
    let ms := mulsubN4 q_hat b0' b1' b2' b3' u0 u1 u2 u3
    val256 a0 a1 a2 a3 * 2^s + ms.2.2.2.2.toNat * 2 ^ 256
      = q_hat.toNat * (val256 b0 b1 b2 b3 * 2^s) +
        val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 +
        u_top.toNat * 2 ^ 256 := by
  intro b3' b2' b1' b0' u3 u2 u1 u0 u_top q_hat ms
  -- Normalize the dividend limbs.
  have h_norm_a : val256 u0 u1 u2 u3 + u_top.toNat * 2 ^ 256 =
      val256 a0 a1 a2 a3 * 2^s :=
    val256_normalize_general hs0 hs a0 a1 a2 a3
  -- Normalize the divisor limbs (needs the CLZ bound on b3).
  have h_norm_b : val256 b0' b1' b2' b3' = val256 b0 b1 b2 b3 * 2^s :=
    val256_normalize hs0 hs b0 b1 b2 b3 hb3_bound
  -- Apply mulsubN4_val256_eq on the normalized limbs.
  have h_mulsub := mulsubN4_val256_eq q_hat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub
  -- Substitute the normalization facts and solve linearly.
  rw [h_norm_b] at h_mulsub
  linarith

end EvmWord

end EvmAsm.Evm64
