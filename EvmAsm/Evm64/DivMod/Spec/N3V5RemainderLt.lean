/-
  EvmAsm.Evm64.DivMod.Spec.N3V5RemainderLt

  The v5 n=3 per-digit val256 conservation (call path).  For a 3-limb divisor
  `(v0,v1,v2,0)` (top limb `v2`, normalized `v2 ≥ 2^63`) in the call regime
  (`u3 < v2`), the digit's `iterWithDoubleAddback` over the v5 trial
  `divKTrialCallV5QHat u3 u2 v2` satisfies the Euclidean conservation

    `val256 u0 u1 u2 u3 + uTop·2^256
       = q·val256 v0 v1 v2 0 + val256(rem) + carry·2^256`.

  The n=3 analog of `iterN2V5_true_conservation_from_shape`, stated directly on
  `iterWithDoubleAddback` (the form `iterN3V5 true` unfolds to via
  `iterN3V5_unfold` + `if_pos`).  Reuses the position-independent
  `iterWithDoubleAddback_val256_conservation_of_branch_bounds` with the n=3 trial
  overestimate `n3_window_div_le_val256_div_plus_two_v5` (KnuthAFloorWindowN3) and
  `mulsubN4_c3_eq_one_v3_zero` (the `v3 = 0` borrow fact).  Per-digit step input
  for the v5 n=3 quotient telescope.  Bead `evm-asm-wbc4i.9.3`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.KnuthAFloorWindowN3
public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate
public import EvmAsm.Evm64.EvmWordArith.DivN4RemainderLt
public import EvmAsm.Evm64.EvmWordArith.DivN3MaxOverestimate

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **v5 n=3 per-digit val256 conservation (call path).**  `q = divKTrialCallV5QHat
    u3 u2 v2` is the v5 trial; the digit's double-addback iterate conserves value
    against the 3-limb divisor `(v0,v1,v2,0)`. -/
theorem n3_trial_call_val256_conservation
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (hv2 : v2.toNat ≥ 2^63)
    (hcall : u3.toNat < v2.toNat) :
    val256 u0 u1 u2 u3 + uTop.toNat * 2 ^ 256 =
      (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
          v0 v1 v2 0 u0 u1 u2 u3 uTop).1.toNat * val256 v0 v1 v2 0 +
        val256
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 uTop).2.2.2.2.1 +
        (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
          v0 v1 v2 0 u0 u1 u2 u3 uTop).2.2.2.2.2.toNat * 2 ^ 256 := by
  have hbnz : v0 ||| v1 ||| v2 ||| 0 ≠ 0 := by
    intro h
    have hv2z : v2 = 0 := (BitVec.or_eq_zero_iff.mp (BitVec.or_eq_zero_iff.mp h).1).2
    rw [hv2z] at hv2; simp at hv2
  set q := divKTrialCallV5QHat u3 u2 v2 with hq
  have hq_over : q.toNat ≤ val256 u0 u1 u2 u3 / val256 v0 v1 v2 0 + 2 := by
    rw [hq]; exact n3_window_div_le_val256_div_plus_two_v5 v0 v1 v2 u0 u1 u2 u3 hv2 hcall
  have hc3 : BitVec.ult uTop (mulsubN4 q v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 →
      (mulsubN4 q v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 = 1 := by
    intro hb
    apply mulsubN4_c3_eq_one_v3_zero
    intro hc3z
    rw [hc3z] at hb
    exact absurd hb (by simp [BitVec.ult])
  exact iterWithDoubleAddback_val256_conservation_of_branch_bounds
    q v0 v1 v2 0 u0 u1 u2 u3 uTop hbnz hq_over hc3
    (fun hb _ => q_pos_of_mulsub_borrow q v0 v1 v2 0 u0 u1 u2 u3 (hc3 hb))
    (fun hb hcz => q_ge_two_of_mulsub_borrow_and_addback_carry_zero
      q v0 v1 v2 0 u0 u1 u2 u3 (hc3 hb) hcz)

/-- The n=3 divisor value `(v0,v1,v2,0)` is a 3-limb number, hence `< 2^192`. -/
theorem n3_val256_v_lt_pow192 (v0 v1 v2 : Word) : val256 v0 v1 v2 0 < 2 ^ 192 := by
  have h0 : (0 : Word).toNat = 0 := rfl
  have := v0.isLt; have := v1.isLt; have := v2.isLt
  simp only [EvmWord.val256, h0]; omega

/-- **v5 n=3 per-digit remainder bound (call path, `uTop = 0`).**  The
    double-addback remainder is below the 3-limb divisor. -/
theorem n3_trial_call_remainder_lt
    (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63)
    (hcall : u3.toNat < v2.toNat) :
    val256
        (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 0).2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 0).2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.1 +
      (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.2.toNat
        * 2 ^ 256 <
    val256 v0 v1 v2 0 := by
  have hbnz : v0 ||| v1 ||| v2 ||| 0 ≠ 0 := by
    intro h
    have hv2z : v2 = 0 := (BitVec.or_eq_zero_iff.mp (BitVec.or_eq_zero_iff.mp h).1).2
    rw [hv2z] at hv2; simp at hv2
  have hv_pos : 0 < val256 v0 v1 v2 0 := by
    have h0 : (0 : Word).toNat = 0 := rfl
    simp only [EvmWord.val256, h0]; omega
  have hq_over := n3_window_div_le_val256_div_plus_two_v5 v0 v1 v2 u0 u1 u2 u3 hv2 hcall
  have hge := n3_window_val256_div_le_trial_v5 v0 v1 v2 u0 u1 u2 u3 hv2 hcall
  have hq_ge : val256 u0 u1 u2 u3 + (0 : Word).toNat * 2 ^ 256 <
      ((divKTrialCallV5QHat u3 u2 v2).toNat + 1) * val256 v0 v1 v2 0 := by
    have h0 : (0 : Word).toNat = 0 := rfl
    rw [h0, Nat.zero_mul, Nat.add_zero]
    exact (Nat.div_lt_iff_lt_mul hv_pos).mp (by omega)
  have hc3 : BitVec.ult (0 : Word)
        (mulsubN4 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 →
      (mulsubN4 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 = 1 := by
    intro hb
    apply mulsubN4_c3_eq_one_v3_zero
    intro hc3z
    rw [hc3z] at hb
    exact absurd hb (by decide)
  exact iterWithDoubleAddback_remainder_lt_of_plus_two
    (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 0 hbnz hc3 hq_over hq_ge

/-- **v5 n=3 per-digit remainder collapse (call path).**  The remainder fits in
    three limbs: the top limb (`rem3`) and the overflow carry are zero. -/
theorem n3_trial_call_collapse
    (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63)
    (hcall : u3.toNat < v2.toNat) :
    (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.1 = 0 ∧
    (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.2 = 0 := by
  have hlt := n3_trial_call_remainder_lt v0 v1 v2 u0 u1 u2 u3 hv2 hcall
  have hv192 := n3_val256_v_lt_pow192 v0 v1 v2
  set out := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 0 with hout
  have key : val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2 ^ 256 < 2 ^ 192 := by omega
  refine ⟨?_, ?_⟩
  · have h : out.2.2.2.2.1.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
  · have h : out.2.2.2.2.2.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)

/-- **v5 n=3 per-digit val256 conservation (max path).**  When the trial would
    overflow (`¬ u3 < v2`), the digit uses the cap trial `signExtend12 4095`; the
    double-addback iterate still conserves value against `(v0,v1,v2,0)`.  This is
    the form `iterN3Max` / `iterN3V5 false` unfold to. -/
theorem n3_trial_max_val256_conservation
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (hv2 : v2.toNat ≥ 2^63)
    (hmax : ¬ BitVec.ult u3 v2) :
    val256 u0 u1 u2 u3 + uTop.toNat * 2 ^ 256 =
      (iterWithDoubleAddback (signExtend12 (4095 : BitVec 12))
          v0 v1 v2 0 u0 u1 u2 u3 uTop).1.toNat * val256 v0 v1 v2 0 +
        val256
          (iterWithDoubleAddback (signExtend12 (4095 : BitVec 12)) v0 v1 v2 0 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (signExtend12 (4095 : BitVec 12)) v0 v1 v2 0 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (signExtend12 (4095 : BitVec 12)) v0 v1 v2 0 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (signExtend12 (4095 : BitVec 12)) v0 v1 v2 0 u0 u1 u2 u3 uTop).2.2.2.2.1 +
        (iterWithDoubleAddback (signExtend12 (4095 : BitVec 12))
          v0 v1 v2 0 u0 u1 u2 u3 uTop).2.2.2.2.2.toNat * 2 ^ 256 := by
  have hbnz : v0 ||| v1 ||| v2 ||| 0 ≠ 0 := by
    intro h
    have hv2z : v2 = 0 := (BitVec.or_eq_zero_iff.mp (BitVec.or_eq_zero_iff.mp h).1).2
    rw [hv2z] at hv2; simp at hv2
  set q := (signExtend12 (4095 : BitVec 12) : Word) with hq
  have hq_over : q.toNat ≤ val256 u0 u1 u2 u3 / val256 v0 v1 v2 0 + 2 := by
    rw [hq]; exact max_trial_local_overestimate_n3_of_not_ult v0 v1 v2 u0 u1 u2 u3 hv2 hmax
  have hc3 : BitVec.ult uTop (mulsubN4 q v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 →
      (mulsubN4 q v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 = 1 := by
    intro hb
    apply mulsubN4_c3_eq_one_v3_zero
    intro hc3z
    rw [hc3z] at hb
    exact absurd hb (by simp [BitVec.ult])
  exact iterWithDoubleAddback_val256_conservation_of_branch_bounds
    q v0 v1 v2 0 u0 u1 u2 u3 uTop hbnz hq_over hc3
    (fun hb _ => q_pos_of_mulsub_borrow q v0 v1 v2 0 u0 u1 u2 u3 (hc3 hb))
    (fun hb hcz => q_ge_two_of_mulsub_borrow_and_addback_carry_zero
      q v0 v1 v2 0 u0 u1 u2 u3 (hc3 hb) hcz)

/-- **v5 n=3 per-digit remainder bound (max path, `uTop = 0`).**  The cap-trial
    double-addback remainder is below the 3-limb divisor, given the window-validity
    invariant `val256 u < 2^64 · val256 v`. -/
theorem n3_trial_max_remainder_lt
    (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63)
    (hmax : ¬ BitVec.ult u3 v2)
    (hvalid : val256 u0 u1 u2 u3 < 2 ^ 64 * val256 v0 v1 v2 0) :
    val256
        (iterWithDoubleAddback (signExtend12 (4095 : BitVec 12)) v0 v1 v2 0 u0 u1 u2 u3 0).2.1
        (iterWithDoubleAddback (signExtend12 (4095 : BitVec 12)) v0 v1 v2 0 u0 u1 u2 u3 0).2.2.1
        (iterWithDoubleAddback (signExtend12 (4095 : BitVec 12)) v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.1
        (iterWithDoubleAddback (signExtend12 (4095 : BitVec 12)) v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.1 +
      (iterWithDoubleAddback (signExtend12 (4095 : BitVec 12)) v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.2.toNat
        * 2 ^ 256 <
    val256 v0 v1 v2 0 := by
  have hbnz : v0 ||| v1 ||| v2 ||| 0 ≠ 0 := by
    intro h
    have hv2z : v2 = 0 := (BitVec.or_eq_zero_iff.mp (BitVec.or_eq_zero_iff.mp h).1).2
    rw [hv2z] at hv2; simp at hv2
  set q : Word := signExtend12 (4095 : BitVec 12) with hq
  have hq_over := max_trial_local_overestimate_n3_of_not_ult v0 v1 v2 u0 u1 u2 u3 hv2 hmax
  have hqsucc : q.toNat + 1 = 2 ^ 64 := by rw [hq, signExtend12_4095_toNat]; omega
  have hq_ge : val256 u0 u1 u2 u3 + (0 : Word).toNat * 2 ^ 256 <
      (q.toNat + 1) * val256 v0 v1 v2 0 := by
    have h0 : (0 : Word).toNat = 0 := rfl
    rw [h0, hqsucc, Nat.zero_mul, Nat.add_zero]; exact hvalid
  have hc3 : BitVec.ult (0 : Word) (mulsubN4 q v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 →
      (mulsubN4 q v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 = 1 := by
    intro hb
    apply mulsubN4_c3_eq_one_v3_zero
    intro hz; rw [hz] at hb; exact absurd hb (by decide)
  exact iterWithDoubleAddback_remainder_lt_of_plus_two
    q v0 v1 v2 0 u0 u1 u2 u3 0 hbnz hc3 hq_over hq_ge

/-- **v5 n=3 per-digit remainder collapse (max path).**  Top limb (`rem3`) and
    overflow carry are zero. -/
theorem n3_trial_max_collapse
    (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63)
    (hmax : ¬ BitVec.ult u3 v2)
    (hvalid : val256 u0 u1 u2 u3 < 2 ^ 64 * val256 v0 v1 v2 0) :
    (iterWithDoubleAddback (signExtend12 (4095 : BitVec 12)) v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.1 = 0 ∧
    (iterWithDoubleAddback (signExtend12 (4095 : BitVec 12)) v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.2 = 0 := by
  have hlt := n3_trial_max_remainder_lt v0 v1 v2 u0 u1 u2 u3 hv2 hmax hvalid
  have hv192 := n3_val256_v_lt_pow192 v0 v1 v2
  set out := iterWithDoubleAddback (signExtend12 (4095 : BitVec 12)) v0 v1 v2 0 u0 u1 u2 u3 0 with hout
  have key : val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2 ^ 256 < 2 ^ 192 := by omega
  refine ⟨?_, ?_⟩
  · have h : out.2.2.2.2.1.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
  · have h : out.2.2.2.2.2.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)

end EvmAsm.Evm64
