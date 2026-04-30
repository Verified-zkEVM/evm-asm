-- Auto-extracted from EvmAsm.Evm64.DivMod.Spec.CallSkip (PR for issue #1078).
/-
  EvmAsm.Evm64.DivMod.Spec.CallSkipOverestimateBridge

  Generic mulsub/denormalize bridge lemmas parameterized over a trial
  quotient `qHat`. These are downstream of the un-normalized bound
  `qHat * val256(b) ≤ val256(a)` plus the overestimate
  `val256(a) / val256(b) ≤ qHat.toNat`, so they are usable for both
  the max-skip path (`qHat = signExtend12 4095`) and the call-skip path
  (`qHat = div128Quot u4 u3 b3'`).

  Originally lived in `Spec.CallSkip`; extracted to keep that file under
  the 1500-line cap (file-size-exception cleanup, GH #1078).

  Theorems exported:
    - c3_un_zero_of_qHat_mul_le
    - val256_ms_un_eq_val256_mod_of_overestimate
    - u_top_eq_c3_n_of_overestimate
    - val256_denorm_eq_val256_mod_of_overestimate
    - denorm_limbN_eq_mod_of_overestimate
    - denorm_4limb_eq_mod_of_val256_eq_amod_pow_s
    - denorm_4limb_to_evmWordIs_eq
    - denorm_limbN_eq_mod_of_overestimate_getLimbN
-/

import EvmAsm.Evm64.DivMod.Spec.Base
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- **Generic: `c3_un = 0` follows from `qHat * val256(b) ≤ val256(a)`.**

    Takes only the un-normalized bound from T3 (or equivalent). Works for
    any `qHat`, so it's usable by both max-skip (where the bound comes
    from `isSkipBorrowN4Max`) and call-skip (where T3 supplies it via
    `div128Quot_call_skip_mul_val256_b_le_val256_a`).

    Proof: from `mulsubN4_val256_eq`,
    `val256(a) + c3.toNat * 2^256 = val256(ms) + qHat.toNat * val256(b)`.
    Combined with the hypothesis `qHat * val256(b) ≤ val256(a)` and the
    bound `val256(ms) < 2^256`, we get `c3.toNat * 2^256 < 2^256`, i.e.
    `c3.toNat = 0`. -/
theorem c3_un_zero_of_qHat_mul_le
    {a0 a1 a2 a3 b0 b1 b2 b3 qHat : Word}
    (h : qHat.toNat * val256 b0 b1 b2 b3 ≤ val256 a0 a1 a2 a3) :
    (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 0 := by
  have heuc := mulsubN4_val256_eq qHat b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at heuc
  have hms_lt : val256 (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).1
                       (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.1
                       (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
                       (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1 < 2^256 :=
    EvmWord.val256_bound ..
  have hc3_lt : (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2.toNat < 2^64 :=
    (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2.isLt
  apply BitVec.eq_of_toNat_eq
  rw [show (0 : Word).toNat = 0 from rfl]
  -- c3.toNat * 2^256 + val256(a) = val256(ms) + qHat.toNat * val256(b) ≤ val256(ms) + val256(a)
  -- → c3.toNat * 2^256 ≤ val256(ms) < 2^256
  -- → c3.toNat = 0
  have h_pow : (2:Nat)^256 > 0 := by positivity
  omega

/-- **Generic: `val256(ms_un) = val256(a) % val256(b)` under c3_un=0 + overestimate.**

    Takes the overestimate bound `val256(a)/val256(b) ≤ qHat.toNat` (supplied
    by `n4CallSkipSemanticHolds` for call-skip, or `max_trial_overestimate_n4`
    for max-skip) plus `c3_un = 0`, and concludes that the 4 un-normalized
    mulsub output limbs at the val256 level equal `val256(a) mod val256(b)`.

    Parameterizes `EvmWord.val256_ms_un_eq_val256_mod_max_skip`
    (Val256ModBridge.lean:30) over the trial quotient `qHat`. Proof is the
    same shape: Euclidean equation + `remainder_lt_of_ge_floor`. -/
theorem val256_ms_un_eq_val256_mod_of_overestimate
    {a0 a1 a2 a3 b0 b1 b2 b3 qHat : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hqHat_ge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ qHat.toNat)
    (hc3_zero : (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 0) :
    let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
    val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 =
    val256 a0 a1 a2 a3 % val256 b0 b1 b2 b3 := by
  intro ms
  have hmulsub_raw := mulsubN4_val256_eq qHat b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at hmulsub_raw
  rw [show ms.2.2.2.2 = (0 : Word) from hc3_zero] at hmulsub_raw
  rw [show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]
    at hmulsub_raw
  have hmulsub : val256 a0 a1 a2 a3 =
      qHat.toNat * val256 b0 b1 b2 b3 +
      val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 := by linarith
  have hv := EvmWord.val256_pos_of_or_ne_zero hbnz
  have ⟨hq, _hr_lt⟩ := EvmWord.remainder_lt_of_ge_floor hv hmulsub hqHat_ge
  rw [hq] at hmulsub
  have := Nat.div_add_mod (val256 a0 a1 a2 a3) (val256 b0 b1 b2 b3)
  have : val256 b0 b1 b2 b3 * (val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3) =
      (val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3) * val256 b0 b1 b2 b3 := Nat.mul_comm _ _
  omega

/-- **Generic `uTop = c3_n` invariant under the overestimate + skip-borrow bounds.**

    Parameterized analog of `EvmWord.u_top_eq_c3_n_max_skip` (ModBridgeUtop.lean:159).
    Takes the T3-shape bound `qHat * val256(b) ≤ val256(a)` (for c3_un = 0),
    the overestimate `val256(a)/val256(b) ≤ qHat.toNat` (for val256(ms_un) <
    val256(b)), and the skip-borrow-derived `c3_n ≤ a3 >>> (64 - s)`
    (= u_top in max-skip / = u4 in call-skip — same thing since
    `antiShift = 64 - s` for `0 < s < 64`).

    Delegates to the already-parameterized `u_top_eq_c3_nat_form`
    (ModBridgeUtop.lean:112), so the whole proof is short. Usable for
    both max-skip (with qHat = signExtend12 4095 + appropriate bounds)
    and call-skip (with qHat = div128Quot u4 u3 b3' + T3 + hsem). -/
theorem u_top_eq_c3_n_of_overestimate
    {a0 a1 a2 a3 b0 b1 b2 b3 qHat : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    {s : Nat} (hs0 : 0 < s) (hs : s < 64)
    (hb3_bound : b3.toNat < 2 ^ (64 - s))
    (hqHat_mul_le : qHat.toNat * val256 b0 b1 b2 b3 ≤ val256 a0 a1 a2 a3)
    (hqHat_ge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ qHat.toNat)
    (hc3_n_le_u_top :
        (mulsubN4 qHat
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
    (mulsubN4 qHat
      (b0 <<< s)
      ((b1 <<< s) ||| (b0 >>> (64 - s)))
      ((b2 <<< s) ||| (b1 >>> (64 - s)))
      ((b3 <<< s) ||| (b2 >>> (64 - s)))
      (a0 <<< s)
      ((a1 <<< s) ||| (a0 >>> (64 - s)))
      ((a2 <<< s) ||| (a1 >>> (64 - s)))
      ((a3 <<< s) ||| (a2 >>> (64 - s)))).2.2.2.2.toNat := by
  have hc3_un_zero : (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 0 :=
    c3_un_zero_of_qHat_mul_le hqHat_mul_le
  have h_un_raw := mulsubN4_val256_eq qHat b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at h_un_raw
  rw [hc3_un_zero, show (0 : Word).toNat = 0 from rfl,
      Nat.zero_mul, Nat.add_zero] at h_un_raw
  have h_n_raw := mulsubN4_val256_eq qHat
    (b0 <<< s)
    ((b1 <<< s) ||| (b0 >>> (64 - s)))
    ((b2 <<< s) ||| (b1 >>> (64 - s)))
    ((b3 <<< s) ||| (b2 >>> (64 - s)))
    (a0 <<< s)
    ((a1 <<< s) ||| (a0 >>> (64 - s)))
    ((a2 <<< s) ||| (a1 >>> (64 - s)))
    ((a3 <<< s) ||| (a2 >>> (64 - s)))
  simp only [] at h_n_raw
  have h_norm_u := EvmWord.val256_normalize_general hs0 hs a0 a1 a2 a3
  have h_norm_b := EvmWord.val256_normalize hs0 hs b0 b1 b2 b3 hb3_bound
  have h_ms_un_eq_mod :=
    val256_ms_un_eq_val256_mod_of_overestimate hbnz hqHat_ge hc3_un_zero
  simp only [] at h_ms_un_eq_mod
  have h_ms_un_lt_b : val256 (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).1
                             (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.1
                             (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
                             (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1 <
                     val256 b0 b1 b2 b3 := by
    rw [h_ms_un_eq_mod]
    exact Nat.mod_lt _ (EvmWord.val256_pos_of_or_ne_zero hbnz)
  have h_b_lt_pow := EvmWord.val256_lt_of_b3_bound b0 b1 b2 b3 (by omega) hb3_bound
  have hs_pos : 0 < 2 ^ s := by positivity
  exact EvmWord.u_top_eq_c3_nat_form (Q := qHat.toNat) s
    h_un_raw h_norm_u h_norm_b h_n_raw h_ms_un_lt_b h_b_lt_pow (by omega) hs_pos
    hc3_n_le_u_top

/-- **Generic: `val256(denormalized) = val256(a) % val256(b)` under the
    overestimate + skip-borrow bounds.**

    Parameterized analog of `EvmWord.val256_denorm_eq_val256_mod_max_skip`
    (ModBridgeAssemble.lean:39). Takes the T3 bound, the overestimate, and
    the skip-borrow c3_n bound, and concludes that the denormalized 4-limb
    value equals `val256(a) mod val256(b)`. Usable for both max-skip and
    call-skip paths. -/
theorem val256_denorm_eq_val256_mod_of_overestimate
    {a0 a1 a2 a3 b0 b1 b2 b3 qHat : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    {s : Nat} (hs0 : 0 < s) (hs : s < 64)
    (hb3_bound : b3.toNat < 2 ^ (64 - s))
    (hqHat_mul_le : qHat.toNat * val256 b0 b1 b2 b3 ≤ val256 a0 a1 a2 a3)
    (hqHat_ge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ qHat.toNat)
    (hc3_n_le_u_top :
        (mulsubN4 qHat
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
    let msN := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    val256 ((msN.1 >>> s) ||| (msN.2.1 <<< (64 - s)))
           ((msN.2.1 >>> s) ||| (msN.2.2.1 <<< (64 - s)))
           ((msN.2.2.1 >>> s) ||| (msN.2.2.2.1 <<< (64 - s)))
           (msN.2.2.2.1 >>> s) =
    val256 a0 a1 a2 a3 % val256 b0 b1 b2 b3 := by
  intro b0' b1' b2' b3' u0 u1 u2 u3 msN
  have hc3_un_zero : (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 0 :=
    c3_un_zero_of_qHat_mul_le hqHat_mul_le
  have h_denorm := EvmWord.val256_denormalize hs0 hs msN.1 msN.2.1 msN.2.2.1 msN.2.2.2.1
  have h_utop_eq := u_top_eq_c3_n_of_overestimate hbnz hs0 hs hb3_bound
    hqHat_mul_le hqHat_ge hc3_n_le_u_top
  have h_un_raw := mulsubN4_val256_eq qHat b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at h_un_raw
  rw [hc3_un_zero, show (0 : Word).toNat = 0 from rfl,
      Nat.zero_mul, Nat.add_zero] at h_un_raw
  have h_n_raw := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_n_raw
  have h_norm_u := EvmWord.val256_normalize_general hs0 hs a0 a1 a2 a3
  have h_norm_b := EvmWord.val256_normalize hs0 hs b0 b1 b2 b3 hb3_bound
  rw [h_norm_b] at h_n_raw
  have h_ms_n_scaled :
      val256 msN.1 msN.2.1 msN.2.2.1 msN.2.2.2.1 =
      val256 (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).1
             (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.1
             (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
             (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1 * 2^s := by
    set Vu : Nat := val256 u0 u1 u2 u3
    set Vms_n : Nat := val256 msN.1 msN.2.1 msN.2.2.1 msN.2.2.2.1
    set Vms_un : Nat := val256 (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).1
         (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.1
         (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
         (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
    set Va : Nat := val256 a0 a1 a2 a3
    set Vb : Nat := val256 b0 b1 b2 b3
    set Q : Nat := qHat.toNat
    have hqa : Q * (Vb * 2 ^ s) = Q * Vb * 2 ^ s := by ring
    rw [h_utop_eq] at h_norm_u
    have h_scaled : Va * 2 ^ s = Vms_n + Q * Vb * 2 ^ s := by linarith
    have h_un_scaled : Va * 2 ^ s = (Vms_un + Q * Vb) * 2 ^ s := by
      rw [h_un_raw]
    linarith [h_scaled, h_un_scaled,
      (show (Vms_un + Q * Vb) * 2 ^ s = Vms_un * 2^s + Q * Vb * 2^s from by ring)]
  have h_ms_un_eq_mod :=
    val256_ms_un_eq_val256_mod_of_overestimate hbnz hqHat_ge hc3_un_zero
  simp only [] at h_ms_un_eq_mod
  rw [h_denorm, h_ms_n_scaled, Nat.mul_div_cancel _ (by positivity : 0 < 2^s)]
  exact h_ms_un_eq_mod

/-- **Generic per-limb denorm→mod bridge (Word-inputs form).**

    Parameterized analog of `denorm_limbN_eq_mod_max_skip`
    (ModBridgeAssemble.lean:184). -/
theorem denorm_limbN_eq_mod_of_overestimate
    (a0 a1 a2 a3 b0 b1 b2 b3 qHat : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (s : Nat) (hs0 : 0 < s) (hs : s < 64)
    (hb3_bound : b3.toNat < 2 ^ (64 - s))
    (hqHat_mul_le : qHat.toNat * val256 b0 b1 b2 b3 ≤ val256 a0 a1 a2 a3)
    (hqHat_ge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ qHat.toNat)
    (hc3_n_le_u_top :
        (mulsubN4 qHat
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
    let msN := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let a := EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    (EvmWord.mod a b).getLimbN 0 = ((msN.1 >>> s) ||| (msN.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 1 = ((msN.2.1 >>> s) ||| (msN.2.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 2 = ((msN.2.2.1 >>> s) ||| (msN.2.2.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 3 = (msN.2.2.2.1 >>> s) := by
  intro b0' b1' b2' b3' u0 u1 u2 u3 msN a_ b_
  have h_val_eq := val256_denorm_eq_val256_mod_of_overestimate (qHat := qHat)
    hbnz hs0 hs hb3_bound hqHat_mul_le hqHat_ge hc3_n_le_u_top
  simp only [] at h_val_eq
  have hr : EvmWord.fromLimbs (fun i : Fin 4 =>
      match i with
      | 0 => (msN.1 >>> s) ||| (msN.2.1 <<< (64 - s))
      | 1 => (msN.2.1 >>> s) ||| (msN.2.2.1 <<< (64 - s))
      | 2 => (msN.2.2.1 >>> s) ||| (msN.2.2.2.1 <<< (64 - s))
      | 3 => msN.2.2.2.1 >>> s) = EvmWord.mod a_ b_ :=
    EvmWord.mod_of_val256_eq_mod hbnz h_val_eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_3

/-- **Generic 4-limb denorm bridge from `val256 = a%b * 2^s`** (CLOSED).

    Given any 4 limbs `X1..X4` whose val256 equals `val256(a)%val256(b) * 2^s`,
    extract per-limb equations relating `(EvmWord.mod a b).getLimbN i` to
    the funnel-shift-right denorm pattern over `X1..X4`.

    Useful for the call+addback BEQ MOD adapter's single-addback branch
    (with `X = post1` limbs) — and dual-purpose for any other path that
    establishes the val256 = a%b * 2^s fact at normalized limbs. -/
theorem denorm_4limb_eq_mod_of_val256_eq_amod_pow_s
    {a b : EvmWord} {X1 X2 X3 X4 : Word}
    {s : Nat} (hs0 : 0 < s) (hs : s < 64)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (h_val_eq : val256 X1 X2 X3 X4 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) * 2 ^ s) :
    (EvmWord.mod a b).getLimbN 0 = ((X1 >>> s) ||| (X2 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 1 = ((X2 >>> s) ||| (X3 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 2 = ((X3 >>> s) ||| (X4 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 3 = (X4 >>> s) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have h_denorm := EvmWord.val256_denormalize hs0 hs X1 X2 X3 X4
  have hspos : 0 < (2 : Nat) ^ s := Nat.pos_of_ne_zero (by positivity)
  have h_div : val256 X1 X2 X3 X4 / 2 ^ s =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
    rw [h_val_eq, Nat.mul_div_cancel _ hspos]
  rw [h_div] at h_denorm
  -- h_denorm: val256(denorm of X1..X4) = val256(a) % val256(b)
  -- Provide an explicit type for `hr` so Lean unifies `mod_of_val256_eq_mod`'s
  -- let-chain output with the explicit `EvmWord.fromLimbs` form, avoiding the
  -- annotation-stripping issue from `simp only [] at ...`.
  have hr : EvmWord.fromLimbs (fun i : Fin 4 => match i with
      | 0 => (X1 >>> s) ||| (X2 <<< (64 - s))
      | 1 => (X2 >>> s) ||| (X3 <<< (64 - s))
      | 2 => (X3 >>> s) ||| (X4 <<< (64 - s))
      | 3 => X4 >>> s) =
      EvmWord.mod
        (EvmWord.fromLimbs (fun i : Fin 4 => match i with
          | 0 => a.getLimbN 0 | 1 => a.getLimbN 1
          | 2 => a.getLimbN 2 | 3 => a.getLimbN 3))
        (EvmWord.fromLimbs (fun i : Fin 4 => match i with
          | 0 => b.getLimbN 0 | 1 => b.getLimbN 1
          | 2 => b.getLimbN 2 | 3 => b.getLimbN 3)) :=
    EvmWord.mod_of_val256_eq_mod hbnz' h_denorm
  -- Fold fromLimbs(... a.getLimbN ...) = a (and similarly for b) inside hr.
  have ha_fold : (EvmWord.fromLimbs (fun i : Fin 4 => match i with
        | 0 => a.getLimbN 0 | 1 => a.getLimbN 1
        | 2 => a.getLimbN 2 | 3 => a.getLimbN 3)) = a :=
    EvmWord.fromLimbs_match_getLimbN_id a
  have hb_fold : (EvmWord.fromLimbs (fun i : Fin 4 => match i with
        | 0 => b.getLimbN 0 | 1 => b.getLimbN 1
        | 2 => b.getLimbN 2 | 3 => b.getLimbN 3)) = b :=
    EvmWord.fromLimbs_match_getLimbN_id b
  rw [ha_fold, hb_fold] at hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_3

/-- **Memory-equation form of the val256-denormalize fold** (CLOSED).

    Direct drop-in helper for adapter parents needing to fold the four
    `↦ₘ` limb writes at `sp+32..sp+56` into `evmWordIs (sp+32) (EvmWord.mod a b)`.
    Composes `denorm_4limb_eq_mod_of_val256_eq_amod_pow_s` with
    `evmWordIs_sp32_limbs_eq.symm` internally — bypasses the form-
    mismatch issues that arise when adapter callers try to chain these
    manually. -/
theorem denorm_4limb_to_evmWordIs_eq
    {a b : EvmWord} (sp : Word) {X1 X2 X3 X4 : Word}
    {s : Nat} (hs0 : 0 < s) (hs : s < 64)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (h_val_eq : val256 X1 X2 X3 X4 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) * 2 ^ s) :
    (((sp + 32) ↦ₘ ((X1 >>> s) ||| (X2 <<< (64 - s)))) **
     ((sp + 40) ↦ₘ ((X2 >>> s) ||| (X3 <<< (64 - s)))) **
     ((sp + 48) ↦ₘ ((X3 >>> s) ||| (X4 <<< (64 - s)))) **
     ((sp + 56) ↦ₘ (X4 >>> s))) =
    evmWordIs (sp + 32) (EvmWord.mod a b) := by
  have h_denorm := denorm_4limb_eq_mod_of_val256_eq_amod_pow_s
    (a := a) (b := b) (X1 := X1) (X2 := X2) (X3 := X3) (X4 := X4)
    hs0 hs hb3nz h_val_eq
  exact (evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b)
    ((X1 >>> s) ||| (X2 <<< (64 - s)))
    ((X2 >>> s) ||| (X3 <<< (64 - s)))
    ((X3 >>> s) ||| (X4 <<< (64 - s)))
    (X4 >>> s)
    h_denorm.1 h_denorm.2.1 h_denorm.2.2.1 h_denorm.2.2.2).symm

/-- **Generic per-limb denorm→mod bridge at EvmWord level.**

    EvmWord wrapper over `denorm_limbN_eq_mod_of_overestimate`, taking
    `a b : EvmWord` rather than 8 Word arguments. Parameterized analog
    of `denorm_limbN_eq_mod_max_skip_getLimbN` (ModBridgeAssemble.lean:233). -/
theorem denorm_limbN_eq_mod_of_overestimate_getLimbN
    {a b : EvmWord} {qHat : Word}
    {s : Nat} (hs0 : 0 < s) (hs : s < 64)
    (hb3_bound : (b.getLimbN 3).toNat < 2 ^ (64 - s))
    (hqHat_mul_le : qHat.toNat * val256 (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3) ≤
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3))
    (hqHat_ge : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
        qHat.toNat)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hc3_n_le_u_top :
        (mulsubN4 qHat
          (b.getLimbN 0 <<< s)
          ((b.getLimbN 1 <<< s) ||| (b.getLimbN 0 >>> (64 - s)))
          ((b.getLimbN 2 <<< s) ||| (b.getLimbN 1 >>> (64 - s)))
          ((b.getLimbN 3 <<< s) ||| (b.getLimbN 2 >>> (64 - s)))
          (a.getLimbN 0 <<< s)
          ((a.getLimbN 1 <<< s) ||| (a.getLimbN 0 >>> (64 - s)))
          ((a.getLimbN 2 <<< s) ||| (a.getLimbN 1 >>> (64 - s)))
          ((a.getLimbN 3 <<< s) ||| (a.getLimbN 2 >>> (64 - s)))).2.2.2.2.toNat ≤
        (a.getLimbN 3 >>> (64 - s)).toNat) :
    let msN := mulsubN4 qHat
        (b.getLimbN 0 <<< s)
        ((b.getLimbN 1 <<< s) ||| (b.getLimbN 0 >>> (64 - s)))
        ((b.getLimbN 2 <<< s) ||| (b.getLimbN 1 >>> (64 - s)))
        ((b.getLimbN 3 <<< s) ||| (b.getLimbN 2 >>> (64 - s)))
        (a.getLimbN 0 <<< s)
        ((a.getLimbN 1 <<< s) ||| (a.getLimbN 0 >>> (64 - s)))
        ((a.getLimbN 2 <<< s) ||| (a.getLimbN 1 >>> (64 - s)))
        ((a.getLimbN 3 <<< s) ||| (a.getLimbN 2 >>> (64 - s)))
    (EvmWord.mod a b).getLimbN 0 = ((msN.1 >>> s) ||| (msN.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 1 = ((msN.2.1 >>> s) ||| (msN.2.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 2 = ((msN.2.2.1 >>> s) ||| (msN.2.2.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 3 = (msN.2.2.2.1 >>> s) := by
  intro msN
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hraw := denorm_limbN_eq_mod_of_overestimate
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    qHat hbnz' s hs0 hs hb3_bound hqHat_mul_le hqHat_ge hc3_n_le_u_top
  simp only [show (EvmWord.fromLimbs fun i : Fin 4 => match i with
                   | 0 => a.getLimbN 0 | 1 => a.getLimbN 1
                   | 2 => a.getLimbN 2 | 3 => a.getLimbN 3) = a
               from EvmWord.fromLimbs_match_getLimbN_id a,
             show (EvmWord.fromLimbs fun i : Fin 4 => match i with
                   | 0 => b.getLimbN 0 | 1 => b.getLimbN 1
                   | 2 => b.getLimbN 2 | 3 => b.getLimbN 3) = b
               from EvmWord.fromLimbs_match_getLimbN_id b] at hraw
  exact hraw

end EvmAsm.Evm64
