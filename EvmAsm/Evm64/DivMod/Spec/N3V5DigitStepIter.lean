/-
  EvmAsm.Evm64.DivMod.Spec.N3V5DigitStepIter

  The v5 n=3 per-digit Euclidean step, stated on the **irreducible** `iterN3V5`
  (call path).  `iterN3V5 true …` computes the v5 trial INTERNALLY (its args are
  plain `Word`s), so `set out := iterN3V5 true …` is kernel-cheap — unlike
  `iterWithDoubleAddback (divKTrialCallV5QHat …)`, whose exposed deep trial
  ARGUMENT triggers the kernel term-size wall.  The per-digit conservation /
  remainder-lt / collapse (proved on `iterWithDoubleAddback` in `N3V5RemainderLt`)
  are first wrapped onto `iterN3V5` (via the trivial `iterN3V5_true_eq` bridge),
  then combined by `set` + `rw` + `ring` with `iterN3V5` projections as atoms.
  Per-digit input to the v5 n=3 quotient telescope.  Bead `evm-asm-wbc4i.9.3`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N3V5RemainderLt
public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5Families

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- `iterN3V5 true …` is the call-path double-addback over the v5 trial. -/
theorem iterN3V5_true_eq (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterN3V5 true v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  rw [iterN3V5_unfold]; simp

/-- Per-digit conservation, wrapped onto `iterN3V5 true` (`uTop = 0`, clean —
    matches n2's `iterN2V5_true_conservation_from_shape` pattern: simplify the
    `uTop` term away on the deep form so the per-digit step needs no `simp at`). -/
theorem iterN3V5_call_conservation (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63) (hcall : u3.toNat < v2.toNat) :
    val256 u0 u1 u2 u3 =
      (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).1.toNat * val256 v0 v1 v2 0 +
        val256
          (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.1
          (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.1
          (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.1
          (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.1 +
        (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.2.toNat * 2 ^ 256 := by
  rw [iterN3V5_true_eq]
  have h := n3_trial_call_val256_conservation v0 v1 v2 u0 u1 u2 u3 0 hv2 hcall
  have h0 : (0 : Word).toNat = 0 := rfl
  simpa [h0] using h

/-- Per-digit remainder bound, wrapped onto `iterN3V5 true` (`uTop = 0`). -/
theorem iterN3V5_call_remainder_lt (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63) (hcall : u3.toNat < v2.toNat) :
    val256
        (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.1
        (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.1
        (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.1
        (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.1 +
      (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.2.toNat * 2 ^ 256 <
    val256 v0 v1 v2 0 := by
  rw [iterN3V5_true_eq]
  exact n3_trial_call_remainder_lt v0 v1 v2 u0 u1 u2 u3 hv2 hcall

/-- Per-digit remainder collapse, wrapped onto `iterN3V5 true` (`uTop = 0`). -/
theorem iterN3V5_call_collapse (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63) (hcall : u3.toNat < v2.toNat) :
    (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.1 = 0 ∧
    (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.2 = 0 := by
  rw [iterN3V5_true_eq]
  exact n3_trial_call_collapse v0 v1 v2 u0 u1 u2 u3 hv2 hcall

/-- **v5 n=3 per-digit Euclidean step (call path), on `iterN3V5`.**  Combines the
    wrapped conservation / collapse / remainder-lt with `iterN3V5` projections as
    `ring` atoms — kernel-cheap (no deep trial argument). -/
theorem iterN3V5_call_step (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63) (hcall : u3.toNat < v2.toNat) :
    val256 u0 u1 u2 u3 =
        (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).1.toNat * val256 v0 v1 v2 0 +
        ((iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.1.toNat +
          2 ^ 64 * (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.1.toNat +
          2 ^ 128 * (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.1.toNat) ∧
      (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.1.toNat +
          2 ^ 64 * (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.1.toNat +
          2 ^ 128 * (iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.1.toNat <
        val256 v0 v1 v2 0 := by
  obtain ⟨hc3z, hcz⟩ := iterN3V5_call_collapse v0 v1 v2 u0 u1 u2 u3 hv2 hcall
  have hconv := iterN3V5_call_conservation v0 v1 v2 u0 u1 u2 u3 hv2 hcall
  have hlt := iterN3V5_call_remainder_lt v0 v1 v2 u0 u1 u2 u3 hv2 hcall
  set out := iterN3V5 true v0 v1 v2 0 u0 u1 u2 u3 0 with hout
  have h0 : (0 : Word).toNat = 0 := rfl
  have hcollapse : val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 =
      out.2.1.toNat + 2 ^ 64 * out.2.2.1.toNat + 2 ^ 128 * out.2.2.2.1.toNat := by
    rw [hc3z]; simp only [EvmWord.val256, h0]; ring
  refine ⟨?_, ?_⟩
  · rw [hconv, hcollapse, hcz, h0]; ring
  · rw [hcollapse] at hlt; rw [hcz, h0] at hlt; simpa using hlt

/-! ### Max branch (`bltu = false`, trial `= signExtend12 4095 = 2^64-1`)

Mirrors the call path.  `iterN3V5 false …` unfolds (via `iterN3Max`) to the
double-addback over the capped trial; the per-digit conservation / remainder-lt /
collapse (max path) carry an extra window-validity hypothesis
`val256 window < 2^64 · val256 v` (the running-remainder invariant in the
telescope). -/

/-- `iterN3V5 false …` is the max-path double-addback over the capped trial. -/
theorem iterN3V5_false_eq (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterN3V5 false v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterWithDoubleAddback (signExtend12 (4095 : BitVec 12)) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold iterN3V5 iterN3Max; simp only [Bool.false_eq_true, if_false]

/-- `iterN3V5 false …` collapsed to the NAMED `iterN3Max` (stops *before* unfolding
    the irreducible `iterN3Max`).  Unlike `iterN3V5_false_eq` — which over-unfolds
    to `iterWithDoubleAddback (signExtend12 4095) …` — this keeps the result in the
    same named form the loop combos / unified wrappers expect for the max branch,
    so `simp only [iterN3V5_false_eq_max]` rewrites a bundle window to `iterN3Max`
    without forcing the explosive defeq through the irreducible def.  Mirror of
    n2's `loopN2IterSelectedV5_false`. -/
theorem iterN3V5_false_eq_max (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterN3V5 false v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold iterN3V5; simp only [Bool.false_eq_true, if_false]

/-- Per-digit conservation, wrapped onto `iterN3V5 false` (clean, `uTop = 0`). -/
theorem iterN3V5_max_conservation (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63) (hmax : ¬ BitVec.ult u3 v2) :
    val256 u0 u1 u2 u3 =
      (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).1.toNat * val256 v0 v1 v2 0 +
        val256
          (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.1
          (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.1
          (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.1
          (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.1 +
        (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.2.toNat * 2 ^ 256 := by
  rw [iterN3V5_false_eq]
  have h := n3_trial_max_val256_conservation v0 v1 v2 u0 u1 u2 u3 0 hv2 hmax
  have h0 : (0 : Word).toNat = 0 := rfl
  simpa [h0] using h

/-- Per-digit remainder bound, wrapped onto `iterN3V5 false` (`uTop = 0`). -/
theorem iterN3V5_max_remainder_lt (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63) (hmax : ¬ BitVec.ult u3 v2)
    (hvalid : val256 u0 u1 u2 u3 < 2 ^ 64 * val256 v0 v1 v2 0) :
    val256
        (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.1
        (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.1
        (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.1
        (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.1 +
      (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.2.toNat * 2 ^ 256 <
    val256 v0 v1 v2 0 := by
  rw [iterN3V5_false_eq]
  exact n3_trial_max_remainder_lt v0 v1 v2 u0 u1 u2 u3 hv2 hmax hvalid

/-- Per-digit remainder collapse, wrapped onto `iterN3V5 false` (`uTop = 0`). -/
theorem iterN3V5_max_collapse (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63) (hmax : ¬ BitVec.ult u3 v2)
    (hvalid : val256 u0 u1 u2 u3 < 2 ^ 64 * val256 v0 v1 v2 0) :
    (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.1 = 0 ∧
    (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.2 = 0 := by
  rw [iterN3V5_false_eq]
  exact n3_trial_max_collapse v0 v1 v2 u0 u1 u2 u3 hv2 hmax hvalid

/-- **v5 n=3 per-digit Euclidean step (max path), on `iterN3V5`.** -/
theorem iterN3V5_max_step (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63) (hmax : ¬ BitVec.ult u3 v2)
    (hvalid : val256 u0 u1 u2 u3 < 2 ^ 64 * val256 v0 v1 v2 0) :
    val256 u0 u1 u2 u3 =
        (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).1.toNat * val256 v0 v1 v2 0 +
        ((iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.1.toNat +
          2 ^ 64 * (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.1.toNat +
          2 ^ 128 * (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.1.toNat) ∧
      (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.1.toNat +
          2 ^ 64 * (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.1.toNat +
          2 ^ 128 * (iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.1.toNat <
        val256 v0 v1 v2 0 := by
  obtain ⟨hc3z, hcz⟩ := iterN3V5_max_collapse v0 v1 v2 u0 u1 u2 u3 hv2 hmax hvalid
  have hconv := iterN3V5_max_conservation v0 v1 v2 u0 u1 u2 u3 hv2 hmax
  have hlt := iterN3V5_max_remainder_lt v0 v1 v2 u0 u1 u2 u3 hv2 hmax hvalid
  set out := iterN3V5 false v0 v1 v2 0 u0 u1 u2 u3 0 with hout
  have h0 : (0 : Word).toNat = 0 := rfl
  have hcollapse : val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 =
      out.2.1.toNat + 2 ^ 64 * out.2.2.1.toNat + 2 ^ 128 * out.2.2.2.1.toNat := by
    rw [hc3z]; simp only [EvmWord.val256, h0]; ring
  refine ⟨?_, ?_⟩
  · rw [hconv, hcollapse, hcz, h0]; ring
  · rw [hcollapse] at hlt; rw [hcz, h0] at hlt; simpa using hlt

end EvmAsm.Evm64
