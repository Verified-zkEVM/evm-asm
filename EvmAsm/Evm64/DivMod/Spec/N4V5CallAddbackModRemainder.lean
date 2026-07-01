/-
  EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackModRemainder

  n=4 MOD call+addback remainder arithmetic bridge (Step 1 of the n=4 MOD lane's
  addback branch).  The pure-Nat kernel `post1_val_eq_amod_pow_s_pure_nat`
  (single addback) in `Spec/CallAddbackPureNat.lean` proves `remainder_val = (a %
  b) * 2^s`, but was UNUSED — nothing connected the addback EvmWord-level `val256`
  conservation to its `h_mulsub`/`h_addback` hypotheses.  This file provides the
  connection at the `val256` level, taking the runtime carry/c3/qHat facts as
  hypotheses (`_of_facts`); the semantic derivation of those facts (from
  `n4CallAddbackBeqSemanticHoldsV5`) is the follow-up.

  Kernel note: the arithmetic is factored into a fully-abstract `Nat`-only helper
  (`amod_single_pure`) so the kernel checks it with no huge `val256 (mulsubN4 …)`
  terms; the concrete conservation equations (which DO carry those terms, proven
  by the imported `iterSingleAddback_val256_conservation_gen` / `mulsubN4_val256_eq`)
  are fed as opaque arguments at the end, avoiding kernel deep recursion.

  Bead: n=4 MOD lane addback bridge.
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddbackPureNat
import EvmAsm.Evm64.DivMod.LoopSemantic
import EvmAsm.Evm64.EvmWordArith.DivN4SingleAddbackVal256
import EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddbackVal256
import EvmAsm.Evm64.EvmWordArith.DivN4SingleAddbackGen
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

set_option maxRecDepth 4000

/-- Fully-abstract single-addback remainder identity over `Nat`: from the two
    conservation equations + the exact-quotient hypothesis, the corrected
    remainder equals `a % b`.  No huge `val256` terms here, so the kernel checks
    it without deep recursion.  `k` plays the role of `q.toNat`. -/
theorem amod_single_pure (Av Bv MSv ABv uTop k qseK abTop : Nat)
    (hq_pos : 1 ≤ k)
    (hms : Av + (uTop + 1) * 2 ^ 256 = MSv + k * Bv)
    (hcons : Av + uTop * 2 ^ 256 = qseK * Bv + ABv + abTop * 2 ^ 256)
    (hqse : qseK = k - 1) (habtop : abTop = 0)
    (hqHat : k = (Av + uTop * 2 ^ 256) / Bv + 1)
    (hAB : ABv < 2 ^ 256) (hBpos : 0 < Bv) (hBlt : Bv < 2 ^ 256) :
    ABv = (Av + uTop * 2 ^ 256) % Bv := by
  -- Fold the raw conservation into the clean `(k-1)*Bv + ABv` shape (Nat vars only:
  -- tiny motive, no huge-term rewrite proof).
  subst hqse habtop
  simp only [Nat.zero_mul, Nat.add_zero] at hcons
  have hqB : k * Bv = (k - 1) * Bv + Bv := by
    have h1 : k - 1 + 1 = k := Nat.sub_add_cancel hq_pos
    calc k * Bv = (k - 1 + 1) * Bv := by rw [h1]
      _ = (k - 1) * Bv + Bv := by rw [Nat.add_mul, Nat.one_mul]
  have h_mulsub :
      (uTop + 1) * 2 ^ 256 + ((Av + uTop * 2 ^ 256) * 2 ^ 0 - uTop * 2 ^ 256) =
        MSv + ((Av + uTop * 2 ^ 256) / Bv + 1) * (Bv * 2 ^ 0) := by
    simp only [pow_zero, Nat.mul_one]; rw [← hqHat]; omega
  have h_addback : ABv + 2 ^ 256 = MSv + Bv * 2 ^ 0 := by
    simp only [pow_zero, Nat.mul_one]; omega
  have h_u4_le : uTop * 2 ^ 256 ≤ (Av + uTop * 2 ^ 256) * 2 ^ 0 := by
    simp only [pow_zero, Nat.mul_one]; omega
  have h_amod : (Av + uTop * 2 ^ 256) % Bv * 2 ^ 0 < 2 ^ 256 := by
    simp only [pow_zero, Nat.mul_one]
    exact lt_of_lt_of_le (Nat.mod_lt _ hBpos) (le_of_lt hBlt)
  have hres := post1_val_eq_amod_pow_s_pure_nat ABv MSv (Av + uTop * 2 ^ 256) Bv 0
    uTop (uTop + 1) h_mulsub h_addback h_u4_le hAB h_amod (by omega)
  simpa only [pow_zero, Nat.mul_one] using hres

/-- **Single-addback (carry ≠ 0) MOD remainder = (a % b) (·2^0), from runtime facts.**

    The single-addback corrected remainder `ab := addbackN4 (mulsub …) (u4 - c3) v`
    satisfies `val256(ab.low4) = (val256 a' + uTop·2^256) % val256 b'` where the
    trial `qHat` overshoots the normalized quotient by exactly one (`hqHat`), the
    mulsub top limb is `u4 + 1` (`hc3`), the addback carry is one (`hcarry_one`),
    and standard bounds hold.  (The `·2^s` funnel to the true shift is applied by
    the getLimbN caller, exactly as in the call-skip path.) -/
theorem val256_addback_single_eq_amod_of_facts
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (huTop : uTop.toNat + 1 < 2 ^ 64)
    (hc3 : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = uTop + 1)
    (hcarry_one :
      addbackN4_carry
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 = 1)
    (hq_pos : 1 ≤ q.toNat)
    (hBnz : val256 v0 v1 v2 v3 ≠ 0)
    (hqHat : q.toNat =
      (val256 u0 u1 u2 u3 + uTop.toNat * 2 ^ 256) / val256 v0 v1 v2 v3 + 1) :
    let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
      (uTop - ms.2.2.2.2) v0 v1 v2 v3
    val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 =
      (val256 u0 u1 u2 u3 + uTop.toNat * 2 ^ 256) % val256 v0 v1 v2 v3 := by
  -- Everything is kept in the RAW `mulsubN4`/`addbackN4` form (matching the imported
  -- lemmas EXACTLY) so the final `exact` needs only syntactic matching plus cheap
  -- zeta on the goal's `let`s — no delta-unfolding of the huge defs (which is what
  -- triggers kernel deep recursion).  We deliberately do NOT `intro ms ab`.
  have hms : val256 u0 u1 u2 u3
        + (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat * 2 ^ 256 =
      val256 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        + q.toNat * val256 v0 v1 v2 v3 :=
    mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  have hcons := iterSingleAddback_val256_conservation_gen q v0 v1 v2 v3 u0 u1 u2 u3 uTop
    huTop hc3 hcarry_one hq_pos
  have htop0 := addbackN4_single_top_zero_of_c3_uTop_plus_one
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
    v0 v1 v2 v3 uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 hc3 hcarry_one
  have hc3n : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = uTop.toNat + 1 := by
    rw [hc3, BitVec.toNat_add]; simp only [show (1 : Word).toNat = 1 from rfl]; omega
  -- Only `hms` needs a (single, cheap) rewrite; `hcons` is fed RAW so no huge-term
  -- rewrite motive is ever built.
  rw [hc3n] at hms
  -- Discharge via the abstract helper, feeding the huge `val256` terms as opaque args
  -- in EXACTLY the raw form `hcons` carries (so no defeq blow-up on the ABv arg).
  exact amod_single_pure (val256 u0 u1 u2 u3) (val256 v0 v1 v2 v3)
    (val256 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1)
    (val256
      (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).1
      (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.1
      (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.1
      (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.1)
    uTop.toNat q.toNat
    (q + signExtend12 (4095 : BitVec 12)).toNat
    (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.2.toNat
    hq_pos hms hcons (add_signExtend12_4095_toNat q hq_pos)
    (by rw [htop0]; rfl) hqHat
    (val256_bound _ _ _ _) (Nat.pos_of_ne_zero hBnz) (val256_bound _ _ _ _)


/-- Fully-abstract DOUBLE-addback remainder identity over `Nat` (carry = 0, second
    addback carries).  `k` plays the role of `q.toNat`; the trial overshoots by 2. -/
theorem amod_double_pure (Av Bv MSv ABv uTop k qseK2 abTop : Nat)
    (hq_ge2 : 2 ≤ k)
    (hms : Av + (uTop + 1) * 2 ^ 256 = MSv + k * Bv)
    (hcons : Av + uTop * 2 ^ 256 = qseK2 * Bv + ABv + abTop * 2 ^ 256)
    (hqse : qseK2 = k - 2) (habtop : abTop = 0)
    (hqHat : k = (Av + uTop * 2 ^ 256) / Bv + 2)
    (hAB : ABv < 2 ^ 256) (hBpos : 0 < Bv) (hBlt : Bv < 2 ^ 256) :
    ABv = (Av + uTop * 2 ^ 256) % Bv := by
  subst hqse habtop
  simp only [Nat.zero_mul, Nat.add_zero] at hcons
  have hqB : k * Bv = (k - 2) * Bv + 2 * Bv := by
    have h1 : k - 2 + 2 = k := Nat.sub_add_cancel hq_ge2
    calc k * Bv = (k - 2 + 2) * Bv := by rw [h1]
      _ = (k - 2) * Bv + 2 * Bv := by rw [Nat.add_mul]
  have h_mulsub :
      (uTop + 1) * 2 ^ 256 + ((Av + uTop * 2 ^ 256) * 2 ^ 0 - uTop * 2 ^ 256) =
        MSv + ((Av + uTop * 2 ^ 256) / Bv + 2) * (Bv * 2 ^ 0) := by
    simp only [pow_zero, Nat.mul_one]; rw [← hqHat]; omega
  have h_addback : ABv + 2 ^ 256 = MSv + 2 * (Bv * 2 ^ 0) := by
    simp only [pow_zero, Nat.mul_one]; omega
  have h_u4_le : uTop * 2 ^ 256 ≤ (Av + uTop * 2 ^ 256) * 2 ^ 0 := by
    simp only [pow_zero, Nat.mul_one]; omega
  have h_amod : (Av + uTop * 2 ^ 256) % Bv * 2 ^ 0 < 2 ^ 256 := by
    simp only [pow_zero, Nat.mul_one]
    exact lt_of_lt_of_le (Nat.mod_lt _ hBpos) (le_of_lt hBlt)
  have hres := abPrime_val_eq_amod_pow_s_pure_nat ABv MSv (Av + uTop * 2 ^ 256) Bv 0
    uTop (uTop + 1) h_mulsub h_addback h_u4_le hAB h_amod (by omega)
  simpa only [pow_zero, Nat.mul_one] using hres

/-- **Double-addback (carry = 0) MOD remainder = (a % b) (·2^0), from runtime facts.**
    The doubly-corrected remainder `ab' := addbackN4 (addbackN4 (mulsub …) …) …`
    equals the (unscaled) true remainder when the trial `qHat` overshoots by two. -/
theorem val256_addback_double_eq_amod_of_facts
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (huTop : uTop.toNat + 1 < 2 ^ 64)
    (hc3 : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = uTop + 1)
    (hcarry_zero :
      addbackN4_carry (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 v0 v1 v2 v3 = 0)
    (hcarry2_one :
      addbackN4_carry
        (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).1
        (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.1
        (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.1
        (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.1
        v0 v1 v2 v3 = 1)
    (hq_ge2 : 2 ≤ q.toNat)
    (hBnz : val256 v0 v1 v2 v3 ≠ 0)
    (hqHat : q.toNat =
      (val256 u0 u1 u2 u3 + uTop.toNat * 2 ^ 256) / val256 v0 v1 v2 v3 + 2) :
    let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
    val256 ab'.1 ab'.2.1 ab'.2.2.1 ab'.2.2.2.1 =
      (val256 u0 u1 u2 u3 + uTop.toNat * 2 ^ 256) % val256 v0 v1 v2 v3 := by
  -- No `set`/`rw` folding of the doubly-nested `ab'` (that builds kernel-unreducible
  -- casts → deep recursion).  Feed the raw conservation directly; the huge `ab'`
  -- terms are inferred as OPAQUE args to the abstract helper (as in the single case).
  have hms : val256 u0 u1 u2 u3 + (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat * 2 ^ 256 =
      val256 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        + q.toNat * val256 v0 v1 v2 v3 :=
    mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  have hc3n : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = uTop.toNat + 1 := by
    rw [hc3, BitVec.toNat_add]; simp only [show (1 : Word).toNat = 1 from rfl]; omega
  rw [hc3n] at hms
  have hcons0 := iterDoubleAddback_val256_conservation_gen q v0 v1 v2 v3 u0 u1 u2 u3 uTop
    huTop hc3 hcarry_zero hcarry2_one hq_ge2
  have hqsub : (q + signExtend12 (4095 : BitVec 12) + signExtend12 (4095 : BitVec 12)).toNat
      = q.toNat - 2 := add_signExtend12_4095_add_signExtend12_4095_toNat q hq_ge2
  rw [hqsub] at hcons0
  -- second-addback top limb = 0 (raw form; small `.toNat` motive only)
  have hab_top : (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.2 = uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 := by
    have h := addbackN4_top_eq (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
      (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3
    simp only [] at h; rw [h, hcarry_zero]; simp
  have hab'_top0 :
      (addbackN4 (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).1 (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.1 (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.1 (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.1 (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.2 v0 v1 v2 v3).2.2.2.2 = 0 := by
    have h := addbackN4_single_top_zero_of_c3_uTop_plus_one
      (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).1 (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.1 (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.1 (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.1 v0 v1 v2 v3 uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 hc3 hcarry2_one
    rw [hab_top]; exact h
  -- Discharge: hcons0/goal infer MSv, ABv (= val256 ab'.low4), qseK2 (= q_out), abTop.
  refine amod_double_pure (val256 u0 u1 u2 u3) (val256 v0 v1 v2 v3) _ _ uTop.toNat q.toNat _ _
    hq_ge2 hms hcons0 rfl ?_ hqHat (val256_bound _ _ _ _) (Nat.pos_of_ne_zero hBnz)
    (val256_bound _ _ _ _)
  rw [hab'_top0]; rfl

end EvmAsm.Evm64
