/-
  EvmAsm.Evm64.EvmWordArith.DivN4C3LeUTopPlusOne

  The U4-general TIGHT mulsub borrow bound `c3 ≤ uTop + 1`.

  For the n=4 single-digit Knuth division, the inner four-limb `mulsubN4` borrow
  `c3` is at most `uTop + 1` whenever the trial quotient satisfies the top-window
  floor bound `q · v3 ≤ uTop·2^64 + u3` (which the v5 trial does, since it IS the
  floor of the top window).  This is TIGHTER than `mulsubN4_c3_le_u4_plus_two`
  (c3 ≤ uTop + 2) and is exactly what the U4-general `iterWithDoubleAddback`
  conservation needs to discharge `c3 = uTop + 1` on the borrow branch (`uTop < c3`
  rules out smaller, this bound rules out larger).

  Key cancellation: `q·val256 v = q·(val256 v0 v1 v2 0) + q·v3·2^192`, with
  `q·v3·2^192 ≤ uTop·2^256 + u3·2^192` (top-window floor) and `val256 u ≥ u3·2^192`;
  the `u3·2^192` terms cancel, leaving `c3·2^256 < (uTop+2)·2^256`.

  All powers are kept symbolic (related via `pow_add`) so no 256-bit literal is
  ever evaluated; the combines use `nlinarith` / `linarith` (powers as atoms).
  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The four-limb `mulsubN4` borrow is at most `uTop + 1` under the top-window
    floor bound `q·v3 ≤ uTop·2^64 + u3`. -/
theorem mulsubN4_c3_le_uTop_plus_one
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hqB3 : q.toNat * v3.toNat ≤ uTop.toNat * 2 ^ 64 + u3.toNat) :
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat ≤ uTop.toNat + 1 := by
  have hms := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only [] at hms
  set c3 := (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 with hc3_def
  set MR := val256 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 with hMR_def
  -- scale relations (symbolic; no literal evaluated).
  have e6419 : (2 : Nat) ^ 64 * 2 ^ 192 = 2 ^ 256 := by rw [← pow_add]
  -- top-window floor: q·v3·2^192 ≤ uTop·2^256 + u3·2^192.
  have hqv3 : q.toNat * v3.toNat * 2 ^ 192 ≤ uTop.toNat * 2 ^ 256 + u3.toNat * 2 ^ 192 := by
    calc q.toNat * v3.toNat * 2 ^ 192
        ≤ (uTop.toNat * 2 ^ 64 + u3.toNat) * 2 ^ 192 := Nat.mul_le_mul_right _ hqB3
      _ = uTop.toNat * (2 ^ 64 * 2 ^ 192) + u3.toNat * 2 ^ 192 := by ring
      _ = uTop.toNat * 2 ^ 256 + u3.toNat * 2 ^ 192 := by rw [e6419]
  -- low three limbs: q·(val256 v0 v1 v2 0) < 2^256.
  have hvlow_lt : val256 v0 v1 v2 0 < 2 ^ 192 := val256_lt_pow192 v0 v1 v2
  have hqvlow : q.toNat * val256 v0 v1 v2 0 < 2 ^ 256 := by
    have h1 : q.toNat + 1 ≤ 2 ^ 64 := q.isLt
    have h2 : val256 v0 v1 v2 0 + 1 ≤ 2 ^ 192 := hvlow_lt
    have hkey : q.toNat * val256 v0 v1 v2 0 < 2 ^ 64 * 2 ^ 192 := by
      nlinarith [h1, h2, Nat.zero_le q.toNat, Nat.zero_le (val256 v0 v1 v2 0)]
    rwa [e6419] at hkey
  -- q·val256 v split.
  have hqsplit : q.toNat * val256 v0 v1 v2 v3 =
      q.toNat * val256 v0 v1 v2 0 + q.toNat * v3.toNat * 2 ^ 192 := by
    have hvsplit : val256 v0 v1 v2 v3 = val256 v0 v1 v2 0 + v3.toNat * 2 ^ 192 := by
      unfold val256
      rw [show (0 : Word).toNat = 0 from by decide]
      ring
    rw [hvsplit, Nat.mul_add, Nat.mul_assoc]
  -- val256 u ≥ u3·2^192 ; MR < 2^256.
  have hVU : u3.toNat * 2 ^ 192 ≤ val256 u0 u1 u2 u3 := by
    show u3.toNat * 2 ^ 192 ≤ u0.toNat + u1.toNat * 2 ^ 64 + u2.toNat * 2 ^ 128 + u3.toNat * 2 ^ 192
    exact Nat.le_add_left _ _
  have hMR_lt : MR < 2 ^ 256 := val256_bound _ _ _ _
  -- c3·2^256 < (uTop+2)·2^256, then divide.
  have hC3lt : c3.toNat * 2 ^ 256 < (uTop.toNat + 2) * 2 ^ 256 := by
    have hexp : (uTop.toNat + 2) * 2 ^ 256 = uTop.toNat * 2 ^ 256 + 2 * 2 ^ 256 := by ring
    rw [hexp]
    linarith [hms, hqsplit, hqv3, hqvlow, hVU, hMR_lt]
  have hpow : (0 : Nat) < 2 ^ 256 := by positivity
  have hlt := Nat.lt_of_mul_lt_mul_right hC3lt
  omega

end EvmAsm.Evm64
