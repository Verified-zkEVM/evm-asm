/-
  EvmAsm.Evm64.EvmWordArith.ModBridgeAssemble

  Assembly of the MOD denormalization bridge (Lemmas D-F from
  `project_mod_denorm_bridge_blocker.md`). Composes:

  - `u_top_eq_c3_n_max_skip` (Lemma C)
  - `val256_ms_un_eq_val256_mod_max_skip` (Val256ModBridge)
  - `val256_ms_un_lt_val256_b_max_skip` (Val256ModBridge)
  - `val256_denormalize` (Lemma A)
  - `val256_normalize_general` + `val256_normalize` (Lemma B)
  - `mulsubN4_val256_eq`

  to conclude at val256 level:
    `val256 u' = val256 a % val256 b`

  where `u'` are the denormalized remainder limbs. Together with
  `mod_of_val256_eq_mod`, this gives `fromLimbs u' = EvmWord.mod a b`,
  and downstream `getLimbN` decomposition yields the per-limb equalities
  needed by the MOD stack spec.

  The CLZ top-limb bound `b3 < 2^(64 - s)` remains a hypothesis
  (to be supplied by a future CLZ correctness lemma).
-/

import EvmAsm.Evm64.EvmWordArith.ModBridgeUtop
import EvmAsm.Evm64.EvmWordArith.Val256ModBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

/-- Assembly theorem: under max+skip conditions + CLZ bound, the
    denormalized remainder limbs equal `val256(a) % val256(b)` at val256
    level. Combines Lemmas A, C, and the un-normalized modulus extraction. -/
theorem val256_denorm_eq_val256_mod_max_skip
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (s : Nat) (hs0 : 0 < s) (hs : s < 64)
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
    let b0' := b0 <<< s
    let b1' := (b1 <<< s) ||| (b0 >>> (64 - s))
    let b2' := (b2 <<< s) ||| (b1 >>> (64 - s))
    let b3' := (b3 <<< s) ||| (b2 >>> (64 - s))
    let u0 := a0 <<< s
    let u1 := (a1 <<< s) ||| (a0 >>> (64 - s))
    let u2 := (a2 <<< s) ||| (a1 >>> (64 - s))
    let u3 := (a3 <<< s) ||| (a2 >>> (64 - s))
    let ms_n := mulsubN4 (signExtend12 4095) b0' b1' b2' b3' u0 u1 u2 u3
    val256 ((ms_n.1 >>> s) ||| (ms_n.2.1 <<< (64 - s)))
           ((ms_n.2.1 >>> s) ||| (ms_n.2.2.1 <<< (64 - s)))
           ((ms_n.2.2.1 >>> s) ||| (ms_n.2.2.2.1 <<< (64 - s)))
           (ms_n.2.2.2.1 >>> s) =
    val256 a0 a1 a2 a3 % val256 b0 b1 b2 b3 := by
  intro b0' b1' b2' b3' u0 u1 u2 u3 ms_n
  -- Step 1: Apply Lemma A (val256_denormalize).
  have h_denorm := val256_denormalize hs0 hs ms_n.1 ms_n.2.1 ms_n.2.2.1 ms_n.2.2.2.1
  -- h_denorm : val256(u') = val256(ms_n) / 2^s
  -- Step 2: Use Lemma C (u_top = c3_n) to derive val256(ms_n) = val256(ms_un) * 2^s.
  have h_utop_eq := u_top_eq_c3_n_max_skip a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb3nz s hs0 hs hb3_bound hc3_un_zero hc3_n_le_u_top
  -- Step 3: Derive val256(ms_n) = val256(ms_un) * 2^s from Lemma C + Euclidean equations.
  -- Using mulsubN4_val256_eq (normalized) + val256_normalize_general + val256_normalize.
  have h_un_raw := mulsubN4_val256_eq (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at h_un_raw
  rw [hc3_un_zero, show (0 : Word).toNat = 0 from by decide,
      Nat.zero_mul, Nat.add_zero] at h_un_raw
  have h_n_raw := mulsubN4_val256_eq (signExtend12 4095) b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_n_raw
  have h_norm_u := val256_normalize_general hs0 hs a0 a1 a2 a3
  have h_norm_b := val256_normalize hs0 hs b0 b1 b2 b3 hb3_bound
  -- Massage h_n_raw to use Vb * 2^s for the divisor.
  rw [h_norm_b] at h_n_raw
  -- Now combine:
  --   h_un_raw : val256 a = val256 ms_un + q_hat * val256 b
  --   h_norm_u : val256 u + u_top * 2^256 = val256 a * 2^s
  --   h_n_raw : val256 u + c3_n * 2^256 = val256 ms_n + q_hat * (val256 b * 2^s)
  --   h_utop_eq : u_top.toNat = c3_n.toNat
  -- Derive: val256(ms_n) = val256(ms_un) * 2^s.
  have h_ms_n_scaled :
      val256 ms_n.1 ms_n.2.1 ms_n.2.2.1 ms_n.2.2.2.1 =
      val256 (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).1
             (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.1
             (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
             (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1 * 2^s := by
    -- Abbreviate all val256 terms to Nat variables so linarith can see through.
    set Vu : Nat := val256 (a0 <<< s) ((a1 <<< s) ||| (a0 >>> (64 - s)))
         ((a2 <<< s) ||| (a1 >>> (64 - s))) ((a3 <<< s) ||| (a2 >>> (64 - s)))
    set Vms_n : Nat := val256 ms_n.1 ms_n.2.1 ms_n.2.2.1 ms_n.2.2.2.1
    set Vms_un : Nat := val256 (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).1
         (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.1
         (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
         (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
    set Va : Nat := val256 a0 a1 a2 a3
    set Vb : Nat := val256 b0 b1 b2 b3
    set Q : Nat := (signExtend12 (4095 : BitVec 12)).toNat
    have hqa : Q * (Vb * 2 ^ s) = Q * Vb * 2 ^ s := by ring
    -- Substitute u_top = c3_n via h_utop_eq into h_norm_u.
    rw [h_utop_eq] at h_norm_u
    -- Now:
    --   h_norm_u : Vu + c3_n * 2^256 = Va * 2^s
    --   h_n_raw  : Vu + c3_n * 2^256 = Vms_n + Q * (Vb * 2^s)
    --   h_un_raw : Va = Vms_un + Q * Vb
    -- Chain: Va * 2^s = Vms_n + Q * Vb * 2^s (from h_norm_u, h_n_raw, hqa).
    -- Then Va * 2^s = (Vms_un + Q*Vb)*2^s (from h_un_raw), so Vms_n = Vms_un * 2^s.
    have h_scaled : Va * 2 ^ s = Vms_n + Q * Vb * 2 ^ s := by linarith
    have h_un_scaled : Va * 2 ^ s = (Vms_un + Q * Vb) * 2 ^ s := by
      rw [h_un_raw]
    linarith [h_scaled, h_un_scaled, (show (Vms_un + Q * Vb) * 2 ^ s = Vms_un * 2^s + Q * Vb * 2^s from by ring)]
  -- Apply Lemma A's result to get val256(u') = val256(ms_un) * 2^s / 2^s = val256(ms_un).
  have h_ms_un_lt_b :=
    val256_ms_un_lt_val256_b_max_skip a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb3nz hc3_un_zero
  simp only [] at h_ms_un_lt_b
  have h_ms_un_eq_mod :=
    val256_ms_un_eq_val256_mod_max_skip a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb3nz hc3_un_zero
  simp only [] at h_ms_un_eq_mod
  -- Chain: val256(u') = val256(ms_n)/2^s = val256(ms_un)*2^s/2^s = val256(ms_un) = val256(a)%val256(b).
  rw [h_denorm, h_ms_n_scaled, Nat.mul_div_cancel _ (by positivity : 0 < 2^s)]
  exact h_ms_un_eq_mod

end EvmWord

end EvmAsm.Evm64
