/-
  EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackModWordLane

  n=4 MOD call+addback-beq remainder getLimbN facts (route ii): the four limbs of
  `EvmWord.mod a b` equal the funnel-shift-down of the addback-corrected remainder
  `un*Out`.  Uses the corrected quotient `q_out` with the complete overestimate
  bridge `denorm_limbN_eq_mod_of_overestimate_getLimbN`, plus the per-limb identity
  `un*Out = mulsubN4 q_out b' u` (from `val256` injectivity + the committed val256
  cruxes + the mulsub conservation `mulsubN4_val256_eq`).
-/
import EvmAsm.Evm64.EvmWordArith.MultiLimb
import EvmAsm.Evm64.DivMod.LoopSemantic
import EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackModRemainder
import EvmAsm.Evm64.DivMod.Spec.N4C3EqUTopPlusOne
import EvmAsm.Evm64.DivMod.Spec.CallAddbackV5

namespace EvmAsm.Evm64
open EvmAsm.Rv64 EvmWord

/-- `val256` is injective on `Word⁴` (base-2⁶⁴ representation, each limb < 2⁶⁴). -/
theorem val256_inj {x0 x1 x2 x3 y0 y1 y2 y3 : Word}
    (h : val256 x0 x1 x2 x3 = val256 y0 y1 y2 y3) :
    x0 = y0 ∧ x1 = y1 ∧ x2 = y2 ∧ x3 = y3 := by
  have b0 := x0.isLt; have b1 := x1.isLt; have b2 := x2.isLt; have b3 := x3.isLt
  have c0 := y0.isLt; have c1 := y1.isLt; have c2 := y2.isLt; have c3 := y3.isLt
  simp only [val256] at h
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_,
          BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩ <;> omega

/-- Exact-quotient mulsub remainder: if `q = D / V` (D = val256 u + u4*2^256 the
    normalized dividend, V = val256 v the normalized divisor), `V ≠ 0`, and the
    mulsub top-borrow `c3 ≤ u4`, then `val256 (mulsub q v u).low4 = D % V`.
    Via `mulsubN4_val256_eq` + Nat div/mod + `val256_bound` (omega). -/
theorem mulsub_exact_val256_low4 (q v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (hBnz : val256 v0 v1 v2 v3 ≠ 0)
    (hq : q.toNat = (val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256) / val256 v0 v1 v2 v3) :
    val256 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 =
      (val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256) % val256 v0 v1 v2 v3 := by
  have hcons := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only at hcons
  set ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3 with hms
  have hlow_lt := val256_bound ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
  have hV_lt := val256_bound v0 v1 v2 v3
  have hmod_lt : (val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256) % val256 v0 v1 v2 v3
      < val256 v0 v1 v2 v3 := Nat.mod_lt _ (Nat.pos_of_ne_zero hBnz)
  have hqV : q.toNat * val256 v0 v1 v2 v3 +
      (val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256) % val256 v0 v1 v2 v3
      = val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256 := by
    rw [hq, Nat.mul_comm]; exact Nat.div_add_mod _ _
  omega

/-- Scaled modulo `(A·2ˢ) % (B·2ˢ) = (A % B)·2ˢ` — the normalization link from the
    normalized remainder `D % V` to the scaled true remainder, used by the n=4
    addback getLimbN composition. -/
theorem scaled_nat_amod (A B s : Nat) :
    (A * 2 ^ s) % (B * 2 ^ s) = (A % B) * 2 ^ s := by
  rw [Nat.mul_comm A, Nat.mul_comm B, Nat.mul_comm (A % B), Nat.mul_mod_mul_left]

/-- Accessor-form abbreviations for the n=4 addback normalized dividend/divisor. -/
private noncomputable abbrev aD (a b : EvmWord) : Nat :=
  val256 (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)
    + (n4CallAddbackBeqU4 a b).toNat * 2 ^ 256

private noncomputable abbrev aV (b : EvmWord) : Nat :=
  val256 (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)

/-- **PROBE (single/carry≠0 branch):** `val256(ab) = D % V` in accessor form, from the
    branch conditions — the linchpin discharge feeding the committed single crux.
    Building this surfaces the exact accessor↔crux gap for the parent to finish. -/
theorem n4_addback_un_val256_eq_amod_single (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hborrow_ult : BitVec.ult (n4CallAddbackBeqU4 a b)
        (mulsubN4 (n4CallAddbackBeqQHatV5 a b)
          (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.2)
    (hcarry_one :
      addbackN4_carry
        (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).1
        (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.1
        (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.1
        (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.1
        (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) = 1)
    (hq_pos : 1 ≤ (n4CallAddbackBeqQHatV5 a b).toNat)
    (hBnz : aV b ≠ 0)
    (huTop : (n4CallAddbackBeqU4 a b).toNat + 1 < 2 ^ 64)
    (hqHat : (n4CallAddbackBeqQHatV5 a b).toNat = aD a b / aV b + 1) :
    let ms := mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
      (n4CallAddbackBeqU4 a b - ms.2.2.2.2)
      (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
    val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 = aD a b % aV b := by
  have hc3 := n4CallAddbackBeq_c3_eq_uTop_plus_one_of_borrow hb3nz hshift_nz hcall hborrow_ult
  exact val256_addback_single_eq_amod_of_facts
    (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) (n4CallAddbackBeqU4 a b)
    huTop hc3 hcarry_one hq_pos hBnz hqHat

/-- **PROBE (double/carry=0∧carry2≠0 branch):** `val256(ab') = D % V` in accessor
    form, from the branch conditions — the double-addback linchpin discharge feeding
    the committed double crux. -/
theorem n4_addback_un_val256_eq_amod_double (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hborrow_ult : BitVec.ult (n4CallAddbackBeqU4 a b)
        (mulsubN4 (n4CallAddbackBeqQHatV5 a b)
          (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.2)
    (hcarry_zero :
      addbackN4_carry
        (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).1
        (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.1
        (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.1
        (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.1
        (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) = 0)
    (hcarry2_one :
      addbackN4_carry
        (addbackN4
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).1
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.1
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.1
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.1
          (n4CallAddbackBeqU4 a b -
            (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
              (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
              (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
              (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.2)
          (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)).1
        (addbackN4
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).1
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.1
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.1
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.1
          (n4CallAddbackBeqU4 a b -
            (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
              (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
              (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
              (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.2)
          (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)).2.1
        (addbackN4
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).1
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.1
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.1
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.1
          (n4CallAddbackBeqU4 a b -
            (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
              (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
              (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
              (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.2)
          (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)).2.2.1
        (addbackN4
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).1
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.1
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.1
          (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
            (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.1
          (n4CallAddbackBeqU4 a b -
            (mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
              (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
              (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
              (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.2)
          (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)).2.2.2.1
        (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) = 1)
    (hq_ge2 : 2 ≤ (n4CallAddbackBeqQHatV5 a b).toNat)
    (hBnz : aV b ≠ 0)
    (huTop : (n4CallAddbackBeqU4 a b).toNat + 1 < 2 ^ 64)
    (hqHat : (n4CallAddbackBeqQHatV5 a b).toNat = aD a b / aV b + 2) :
    let ms := mulsubN4 (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b) (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
      (n4CallAddbackBeqU4 a b - ms.2.2.2.2)
      (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2
      (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
    val256 ab'.1 ab'.2.1 ab'.2.2.1 ab'.2.2.2.1 = aD a b % aV b := by
  have hc3 := n4CallAddbackBeq_c3_eq_uTop_plus_one_of_borrow hb3nz hshift_nz hcall hborrow_ult
  exact val256_addback_double_eq_amod_of_facts
    (n4CallAddbackBeqQHatV5 a b) (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) (n4CallAddbackBeqU4 a b)
    huTop hc3 hcarry_zero hcarry2_one hq_ge2 hBnz hqHat

end EvmAsm.Evm64
