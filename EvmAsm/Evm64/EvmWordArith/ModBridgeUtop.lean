/-
  EvmAsm.Evm64.EvmWordArith.ModBridgeUtop

  The `uTop = c3_n` invariant for Knuth algorithm D at n=4 max+skip.

  During algorithm D's normalization step, the top bits of the dividend
  `a3 >>> (64 - s)` become an implicit 5th limb `uTop`. The mulsub on
  the normalized 4-limb dividend + divisor produces `msN` with carry
  `c3_n`. This lemma proves that under the max+skip conditions,
  `uTop = c3_n` (not merely `uTop ≥ c3_n` as the runtime skip check
  gives). The identity is the key missing invariant for the MOD
  denormalization bridge.

  Preconditions used:
  - b3 ≠ 0 and CLZ top-limb bound `b3 < 2^(64 - s)` (for s = clz(b3)).
  - `hborrow` : the runtime skip borrow gives `c3_n ≤ uTop`.
  - `hsem`    : un-normalized mulsub carry is 0 (semantic skip).
-/

import EvmAsm.Evm64.EvmWordArith.DenormLemmas
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate
import EvmAsm.Evm64.EvmWordArith.Val256ModBridge
import EvmAsm.Evm64.DivMod.LoopSemantic

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_toNat_0)

namespace EvmWord

/-- Nat-level uniqueness: if `vPow < 2^256`, `vN < 2^256`, `c ≤ u`, and
    `vPow = vN + (u - c) * 2^256`, then `u = c` (and `vPow = vN`). -/
theorem nat_top_eq_of_lt_pow256 {vPow vN u c : Nat}
    (hle : c ≤ u)
    (heq : vPow = vN + (u - c) * 2 ^ 256)
    (h_vPow_lt : vPow < 2 ^ 256) :
    u = c := by
  have : 0 < 2 ^ 256 := Nat.pos_of_ne_zero (by positivity)
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
    `(uTop - c3_n) * 2^256` residual term.

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
    let uTop := a3 >>> (64 - s)
    let qHat : Word := signExtend12 4095
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    val256 a0 a1 a2 a3 * 2^s + ms.2.2.2.2.toNat * 2 ^ 256
      = qHat.toNat * (val256 b0 b1 b2 b3 * 2^s) +
        val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 +
        uTop.toNat * 2 ^ 256 := by
  intro b3' b2' b1' b0' u3 u2 u1 u0 uTop qHat ms
  -- Normalize the dividend limbs.
  have : val256 u0 u1 u2 u3 + uTop.toNat * 2 ^ 256 =
      val256 a0 a1 a2 a3 * 2^s :=
    val256_normalize_general hs0 hs a0 a1 a2 a3
  -- Normalize the divisor limbs (needs the CLZ bound on b3).
  have h_norm_b : val256 b0' b1' b2' b3' = val256 b0 b1 b2 b3 * 2^s :=
    val256_normalize hs0 hs b0 b1 b2 b3 hb3_bound
  -- Apply mulsubN4_val256_eq on the normalized limbs.
  have h_mulsub := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub
  -- Substitute the normalization facts and solve linearly.
  rw [h_norm_b] at h_mulsub
  linarith

/-- Under the CLZ top-limb bound `b3 < 2^(64 - s)`, the full 256-bit value
    satisfies `val256(b) < 2^(256 - s)`, which is what bounds `val256(b) * 2^s`
    within 2^256. Elementary expansion + `nlinarith`. -/
theorem val256_lt_of_b3_bound (b0 b1 b2 b3 : Word) {s : Nat} (hs : s ≤ 64)
    (hb3_bound : b3.toNat < 2 ^ (64 - s)) :
    val256 b0 b1 b2 b3 < 2 ^ (256 - s) := by
  unfold val256
  have h0 := b0.isLt
  have h1 := b1.isLt
  have h2 := b2.isLt
  -- val256 b ≤ (2^64 - 1)(1 + 2^64 + 2^128) + (2^(64-s) - 1) * 2^192 = 2^(256-s) - 1.
  have hpow : (2 : Nat) ^ (256 - s) = 2 ^ (64 - s) * 2 ^ 192 := by
    rw [← pow_add, show (64 - s) + 192 = 256 - s from by omega]
  rw [hpow]
  nlinarith [h0, h1, h2, hb3_bound,
             (show 0 < 2 ^ (64 - s) from by positivity)]

/-- Fully abstract Nat-level `uTop = c3_n` lemma. Takes all relevant
    Euclidean equations and bounds as plain Nat facts — lets the caller
    plug in `val256(ms_un)`, `val256(a) * 2^s`, etc. without forcing
    the elaborator to unfold `mulsubN4` or `val256_normalized_mulsub_eq`
    internals. Composes the un-normalized Euclidean equation with the
    normalization identity and the 2^256 pigeonhole to collapse
    `uTop - c3_n = 0`. -/
theorem u_top_eq_c3_nat_form
    {Va Vb Vms_un Vms_n Vu Vbn : Nat}
    {uTop c3_n Q : Nat}
    (s : Nat)
    (h_Va : Va = Vms_un + Q * Vb)
    (h_norm_u : Vu + uTop * 2 ^ 256 = Va * 2 ^ s)
    (h_norm_b : Vbn = Vb * 2 ^ s)
    (h_Vn : Vu + c3_n * 2 ^ 256 = Vms_n + Q * Vbn)
    (h_Vms_un_lt_Vb : Vms_un < Vb)
    (h_Vb_bound : Vb < 2 ^ (256 - s))
    (hs_le : s ≤ 256)
    (hs_pos : 0 < 2 ^ s)
    (h_c3_le : c3_n ≤ uTop) :
    uTop = c3_n := by
  -- Scale un-normalized Euclidean by 2^s.
  have h_Va_scaled : Va * 2 ^ s = Vms_un * 2 ^ s + Q * Vb * 2 ^ s := by
    rw [h_Va]; ring
  -- Merge the two Euclidean equations (via Va*2^s pivot).
  have h_n_combined : Vu + c3_n * 2 ^ 256 = Vms_n + Q * (Vb * 2 ^ s) := by
    rw [h_norm_b] at h_Vn; exact h_Vn
  -- Va * 2^s + c3_n * 2^256 = Vms_n + Q * Vb * 2^s + uTop * 2^256
  have : Va * 2 ^ s + c3_n * 2 ^ 256 =
      Vms_n + Q * Vb * 2 ^ s + uTop * 2 ^ 256 := by
    have hqa : Q * (Vb * 2 ^ s) = Q * Vb * 2 ^ s := by ring
    linarith [h_norm_u, h_n_combined, hqa]
  -- Substitute h_Va_scaled and cancel Q * Vb * 2^s:
  have h_cancel : Vms_un * 2 ^ s + c3_n * 2 ^ 256 = Vms_n + uTop * 2 ^ 256 := by
    linarith
  -- Bound Vms_un * 2^s < 2^256.
  have hpow : (2 : Nat) ^ (256 - s) * 2 ^ s = 2 ^ 256 := by
    rw [← pow_add, show (256 - s) + s = 256 from by omega]
  have h_bound : Vms_un * 2 ^ s < 2 ^ 256 := by
    calc Vms_un * 2 ^ s
        < Vb * 2 ^ s := Nat.mul_lt_mul_right hs_pos |>.mpr h_Vms_un_lt_Vb
      _ < 2 ^ (256 - s) * 2 ^ s := Nat.mul_lt_mul_right hs_pos |>.mpr h_Vb_bound
      _ = 2 ^ 256 := hpow
  -- Pigeonhole: from h_cancel + h_bound + h_c3_le → uTop = c3_n.
  have h_eq_form : Vms_un * 2 ^ s =
      Vms_n + (uTop - c3_n) * 2 ^ 256 := by omega
  exact nat_top_eq_of_lt_pow256 h_c3_le h_eq_form h_bound

/-- Word-level wrapper: `uTop = c3_n` for the n=4 max+skip path.
    Specializes `u_top_eq_c3_nat_form` to the concrete normalized limbs
    `a_i <<< s | a_{i-1} >>> (64-s)` etc. Takes the CLZ top-limb bound on
    `b3` and the un-normalized / normalized skip conditions, and concludes
    that the normalization overflow `a3 >>> (64-s)` equals the normalized
    mulsub carry. -/
theorem u_top_eq_c3_n_max_skip
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    {s : Nat} (hs0 : 0 < s) (hs : s < 64)
    (hb3_bound : b3.toNat < 2 ^ (64 - s))
    (hc3_un_zero : (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 0)
    (hc3_n_le_u_top :
        (mulsubN4 (signExtend12 4095)
          (b0 <<< s)
          ((b1 <<< s) ||| (b0 >>> (64 - s)))
          ((b2 <<< s) ||| (b1 >>> (64 - s)))
          ((b3 <<< s) ||| (b2 >>> (64 - s)))
          (a0 <<< s)
          ((a1 <<< s) ||| (a0 >>> (64 - s)))
          ((a2 <<< s) ||| (a1 >>> (64 - s)))
          ((a3 <<< s) ||| (a2 >>> (64 - s)))).2.2.2.2.toNat ≤
        (a3 >>> (64 - s)).toNat) :
    (a3 >>> (64 - s)).toNat =
    (mulsubN4 (signExtend12 4095)
      (b0 <<< s)
      ((b1 <<< s) ||| (b0 >>> (64 - s)))
      ((b2 <<< s) ||| (b1 >>> (64 - s)))
      ((b3 <<< s) ||| (b2 >>> (64 - s)))
      (a0 <<< s)
      ((a1 <<< s) ||| (a0 >>> (64 - s)))
      ((a2 <<< s) ||| (a1 >>> (64 - s)))
      ((a3 <<< s) ||| (a2 >>> (64 - s)))).2.2.2.2.toNat := by
  -- Derive the 4 Euclidean-style hypotheses at Nat level.
  have h_un_raw := mulsubN4_val256_eq (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at h_un_raw
  rw [hc3_un_zero, word_toNat_0,
      Nat.zero_mul, Nat.add_zero] at h_un_raw
  -- h_un_raw : val256(a) = val256(ms_un) + qHat * val256(b)
  have h_n_raw := mulsubN4_val256_eq (signExtend12 4095)
    (b0 <<< s)
    ((b1 <<< s) ||| (b0 >>> (64 - s)))
    ((b2 <<< s) ||| (b1 >>> (64 - s)))
    ((b3 <<< s) ||| (b2 >>> (64 - s)))
    (a0 <<< s)
    ((a1 <<< s) ||| (a0 >>> (64 - s)))
    ((a2 <<< s) ||| (a1 >>> (64 - s)))
    ((a3 <<< s) ||| (a2 >>> (64 - s)))
  simp only [] at h_n_raw
  -- h_n_raw : val256(u) + c3_n * 2^256 = val256(msN) + qHat * val256(b_norm)
  have h_norm_u := val256_normalize_general hs0 hs a0 a1 a2 a3
  have h_norm_b := val256_normalize hs0 hs b0 b1 b2 b3 hb3_bound
  have h_ms_un_lt_b :=
    val256_ms_un_lt_val256_b_max_skip hbnz hb3nz hc3_un_zero
  simp only [] at h_ms_un_lt_b
  have h_b_lt_pow := val256_lt_of_b3_bound b0 b1 b2 b3 (by omega) hb3_bound
  have hs_pos : 0 < 2 ^ s := by positivity
  exact u_top_eq_c3_nat_form (Q := (signExtend12 (4095 : BitVec 12)).toNat) s
    h_un_raw h_norm_u h_norm_b h_n_raw h_ms_un_lt_b h_b_lt_pow (by omega) hs_pos
    hc3_n_le_u_top

end EvmWord

end EvmAsm.Evm64
