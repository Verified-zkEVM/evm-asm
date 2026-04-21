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
open EvmAsm.Rv64.AddrNorm (word_toNat_0)

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
    let msN := mulsubN4 (signExtend12 4095) b0' b1' b2' b3' u0 u1 u2 u3
    val256 ((msN.1 >>> s) ||| (msN.2.1 <<< (64 - s)))
           ((msN.2.1 >>> s) ||| (msN.2.2.1 <<< (64 - s)))
           ((msN.2.2.1 >>> s) ||| (msN.2.2.2.1 <<< (64 - s)))
           (msN.2.2.2.1 >>> s) =
    val256 a0 a1 a2 a3 % val256 b0 b1 b2 b3 := by
  intro b0' b1' b2' b3' u0 u1 u2 u3 msN
  -- Step 1: Apply Lemma A (val256_denormalize).
  have h_denorm := val256_denormalize hs0 hs msN.1 msN.2.1 msN.2.2.1 msN.2.2.2.1
  -- h_denorm : val256(u') = val256(msN) / 2^s
  -- Step 2: Use Lemma C (uTop = c3_n) to derive val256(msN) = val256(ms_un) * 2^s.
  have h_utop_eq := u_top_eq_c3_n_max_skip a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb3nz s hs0 hs hb3_bound hc3_un_zero hc3_n_le_u_top
  -- Step 3: Derive val256(msN) = val256(ms_un) * 2^s from Lemma C + Euclidean equations.
  -- Using mulsubN4_val256_eq (normalized) + val256_normalize_general + val256_normalize.
  have h_un_raw := mulsubN4_val256_eq (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at h_un_raw
  rw [hc3_un_zero, word_toNat_0,
      Nat.zero_mul, Nat.add_zero] at h_un_raw
  have h_n_raw := mulsubN4_val256_eq (signExtend12 4095) b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_n_raw
  have h_norm_u := val256_normalize_general hs0 hs a0 a1 a2 a3
  have h_norm_b := val256_normalize hs0 hs b0 b1 b2 b3 hb3_bound
  -- Massage h_n_raw to use Vb * 2^s for the divisor.
  rw [h_norm_b] at h_n_raw
  -- Now combine:
  --   h_un_raw : val256 a = val256 ms_un + qHat * val256 b
  --   h_norm_u : val256 u + uTop * 2^256 = val256 a * 2^s
  --   h_n_raw : val256 u + c3_n * 2^256 = val256 msN + qHat * (val256 b * 2^s)
  --   h_utop_eq : uTop.toNat = c3_n.toNat
  -- Derive: val256(msN) = val256(ms_un) * 2^s.
  have h_ms_n_scaled :
      val256 msN.1 msN.2.1 msN.2.2.1 msN.2.2.2.1 =
      val256 (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).1
             (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.1
             (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
             (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1 * 2^s := by
    -- Abbreviate all val256 terms to Nat variables so linarith can see through.
    set Vu : Nat := val256 (a0 <<< s) ((a1 <<< s) ||| (a0 >>> (64 - s)))
         ((a2 <<< s) ||| (a1 >>> (64 - s))) ((a3 <<< s) ||| (a2 >>> (64 - s)))
    set Vms_n : Nat := val256 msN.1 msN.2.1 msN.2.2.1 msN.2.2.2.1
    set Vms_un : Nat := val256 (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).1
         (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.1
         (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
         (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
    set Va : Nat := val256 a0 a1 a2 a3
    set Vb : Nat := val256 b0 b1 b2 b3
    set Q : Nat := (signExtend12 (4095 : BitVec 12)).toNat
    have hqa : Q * (Vb * 2 ^ s) = Q * Vb * 2 ^ s := by ring
    -- Substitute uTop = c3_n via h_utop_eq into h_norm_u.
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
  -- Chain: val256(u') = val256(msN)/2^s = val256(ms_un)*2^s/2^s = val256(ms_un) = val256(a)%val256(b).
  rw [h_denorm, h_ms_n_scaled, Nat.mul_div_cancel _ (by positivity : 0 < 2^s)]
  exact h_ms_un_eq_mod

/-- Lemma F — lift from val256-level to `EvmWord.mod a b`: under the
    max+skip conditions + CLZ top-limb bound, the denormalized remainder
    limbs `u0', u1', u2', u3'` assembled via `fromLimbs` equal
    `EvmWord.mod a b`. -/
theorem denorm_limbs_eq_evmWord_mod_max_skip
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
    let msN := mulsubN4 (signExtend12 4095) b0' b1' b2' b3' u0 u1 u2 u3
    let u0' := (msN.1 >>> s) ||| (msN.2.1 <<< (64 - s))
    let u1' := (msN.2.1 >>> s) ||| (msN.2.2.1 <<< (64 - s))
    let u2' := (msN.2.2.1 >>> s) ||| (msN.2.2.2.1 <<< (64 - s))
    let u3' := msN.2.2.2.1 >>> s
    let a := fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    let r := fromLimbs fun i : Fin 4 =>
      match i with | 0 => u0' | 1 => u1' | 2 => u2' | 3 => u3'
    r = EvmWord.mod a b :=
  mod_of_val256_eq_mod hbnz
    (val256_denorm_eq_val256_mod_max_skip a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb3nz s hs0 hs hb3_bound hc3_un_zero hc3_n_le_u_top)

/-- Per-limb form of Lemma F: each of the four denormalized remainder limbs
    equals the corresponding limb of `EvmWord.mod a b`. Specializes
    `denorm_limbs_eq_evmWord_mod_max_skip` via `getLimbN_fromLimbs_k`. -/
theorem denorm_limbN_eq_mod_max_skip
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
    let msN := mulsubN4 (signExtend12 4095) b0' b1' b2' b3' u0 u1 u2 u3
    let a := fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    (EvmWord.mod a b).getLimbN 0 = ((msN.1 >>> s) ||| (msN.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 1 = ((msN.2.1 >>> s) ||| (msN.2.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 2 = ((msN.2.2.1 >>> s) ||| (msN.2.2.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 3 = (msN.2.2.2.1 >>> s) := by
  intro b0' b1' b2' b3' u0 u1 u2 u3 msN a b
  have hr := denorm_limbs_eq_evmWord_mod_max_skip a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb3nz s hs0 hs hb3_bound hc3_un_zero hc3_n_le_u_top
  simp only [] at hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hr]; exact getLimbN_fromLimbs_0
  · rw [← hr]; exact getLimbN_fromLimbs_1
  · rw [← hr]; exact getLimbN_fromLimbs_2
  · rw [← hr]; exact getLimbN_fromLimbs_3

/-- EvmWord-level form of `denorm_limbN_eq_mod_max_skip`. Mirrors the
    structure of `n4_max_skip_div_mod_getLimbN`: applies the Word-level
    lemma with `a.getLimbN k` / `b.getLimbN k` inputs, then folds the
    resulting `fromLimbs` lets back to `a` / `b` via
    `EvmWord.fromLimbs_match_getLimbN_id`. -/
theorem denorm_limbN_eq_mod_max_skip_getLimbN (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (s : Nat) (hs0 : 0 < s) (hs : s < 64)
    (hb3_bound : (b.getLimbN 3).toNat < 2 ^ (64 - s))
    (hc3_un_zero : (mulsubN4 (signExtend12 4095)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = 0)
    (hc3_n_le_u_top :
        (mulsubN4 (signExtend12 4095)
          (b.getLimbN 0 <<< s)
          ((b.getLimbN 1 <<< s) ||| (b.getLimbN 0 >>> (64 - s)))
          ((b.getLimbN 2 <<< s) ||| (b.getLimbN 1 >>> (64 - s)))
          ((b.getLimbN 3 <<< s) ||| (b.getLimbN 2 >>> (64 - s)))
          (a.getLimbN 0 <<< s)
          ((a.getLimbN 1 <<< s) ||| (a.getLimbN 0 >>> (64 - s)))
          ((a.getLimbN 2 <<< s) ||| (a.getLimbN 1 >>> (64 - s)))
          ((a.getLimbN 3 <<< s) ||| (a.getLimbN 2 >>> (64 - s)))).2.2.2.2.toNat ≤
        (a.getLimbN 3 >>> (64 - s)).toNat) :
    let msN := mulsubN4 (signExtend12 4095)
        (b.getLimbN 0 <<< s)
        ((b.getLimbN 1 <<< s) ||| (b.getLimbN 0 >>> (64 - s)))
        ((b.getLimbN 2 <<< s) ||| (b.getLimbN 1 >>> (64 - s)))
        ((b.getLimbN 3 <<< s) ||| (b.getLimbN 2 >>> (64 - s)))
        (a.getLimbN 0 <<< s)
        ((a.getLimbN 1 <<< s) ||| (a.getLimbN 0 >>> (64 - s)))
        ((a.getLimbN 2 <<< s) ||| (a.getLimbN 1 >>> (64 - s)))
        ((a.getLimbN 3 <<< s) ||| (a.getLimbN 2 >>> (64 - s)))
    (EvmWord.mod a b).getLimbN 0 = (msN.1 >>> s) ||| (msN.2.1 <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 1 = (msN.2.1 >>> s) ||| (msN.2.2.1 <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 2 = (msN.2.2.1 >>> s) ||| (msN.2.2.2.1 <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 3 = msN.2.2.2.1 >>> s := by
  intro msN
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hraw := denorm_limbN_eq_mod_max_skip
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hbnz' hb3nz s hs0 hs hb3_bound hc3_un_zero hc3_n_le_u_top
  -- Plain `rw` fails to unify the `fromLimbs` pattern despite apparent syntactic
  -- equality — work around by constructing the rewrite equations explicitly.
  simp only [show (fromLimbs fun i : Fin 4 => match i with
                   | 0 => a.getLimbN 0 | 1 => a.getLimbN 1
                   | 2 => a.getLimbN 2 | 3 => a.getLimbN 3) = a
               from EvmWord.fromLimbs_match_getLimbN_id a,
             show (fromLimbs fun i : Fin 4 => match i with
                   | 0 => b.getLimbN 0 | 1 => b.getLimbN 1
                   | 2 => b.getLimbN 2 | 3 => b.getLimbN 3) = b
               from EvmWord.fromLimbs_match_getLimbN_id b] at hraw
  exact hraw

/-- Lemma G — stack-spec adapter for the MOD denorm bridge. The four
    denormalized output slots at `sp+32..sp+56` fold into
    `evmWordIs (sp+32) (EvmWord.mod a b)`. Mirror of
    `output_slot_to_evmWordIs_mod_n4_max_skip` for the denorm path. -/
theorem output_slot_to_evmWordIs_mod_n4_max_skip_denorm
    (sp : Word) (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (s : Nat) (hs0 : 0 < s) (hs : s < 64)
    (hb3_bound : (b.getLimbN 3).toNat < 2 ^ (64 - s))
    (hc3_un_zero : (mulsubN4 (signExtend12 4095)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = 0)
    (hc3_n_le_u_top :
        (mulsubN4 (signExtend12 4095)
          (b.getLimbN 0 <<< s)
          ((b.getLimbN 1 <<< s) ||| (b.getLimbN 0 >>> (64 - s)))
          ((b.getLimbN 2 <<< s) ||| (b.getLimbN 1 >>> (64 - s)))
          ((b.getLimbN 3 <<< s) ||| (b.getLimbN 2 >>> (64 - s)))
          (a.getLimbN 0 <<< s)
          ((a.getLimbN 1 <<< s) ||| (a.getLimbN 0 >>> (64 - s)))
          ((a.getLimbN 2 <<< s) ||| (a.getLimbN 1 >>> (64 - s)))
          ((a.getLimbN 3 <<< s) ||| (a.getLimbN 2 >>> (64 - s)))).2.2.2.2.toNat ≤
        (a.getLimbN 3 >>> (64 - s)).toNat) :
    let msN := mulsubN4 (signExtend12 4095)
        (b.getLimbN 0 <<< s)
        ((b.getLimbN 1 <<< s) ||| (b.getLimbN 0 >>> (64 - s)))
        ((b.getLimbN 2 <<< s) ||| (b.getLimbN 1 >>> (64 - s)))
        ((b.getLimbN 3 <<< s) ||| (b.getLimbN 2 >>> (64 - s)))
        (a.getLimbN 0 <<< s)
        ((a.getLimbN 1 <<< s) ||| (a.getLimbN 0 >>> (64 - s)))
        ((a.getLimbN 2 <<< s) ||| (a.getLimbN 1 >>> (64 - s)))
        ((a.getLimbN 3 <<< s) ||| (a.getLimbN 2 >>> (64 - s)))
    (((sp + 32) ↦ₘ ((msN.1 >>> s) ||| (msN.2.1 <<< (64 - s)))) **
     ((sp + 40) ↦ₘ ((msN.2.1 >>> s) ||| (msN.2.2.1 <<< (64 - s)))) **
     ((sp + 48) ↦ₘ ((msN.2.2.1 >>> s) ||| (msN.2.2.2.1 <<< (64 - s)))) **
     ((sp + 56) ↦ₘ (msN.2.2.2.1 >>> s))) =
    evmWordIs (sp + 32) (EvmWord.mod a b) := by
  obtain ⟨h0, h1, h2, h3⟩ :=
    denorm_limbN_eq_mod_max_skip_getLimbN a b hb3nz s hs0 hs hb3_bound
      hc3_un_zero hc3_n_le_u_top
  intro _
  rw [evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _ h0 h1 h2 h3]

end EvmWord

end EvmAsm.Evm64
