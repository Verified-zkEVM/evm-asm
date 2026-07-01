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
import EvmAsm.Evm64.DivMod.Spec.CallSkipOverestimateBridge
import EvmAsm.Evm64.EvmWordArith.KnuthTheoremB
import EvmAsm.Evm64.EvmWordArith.CLZLemmas

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

/-- From the addback semantic (`q_out = qTrue`), the corrected quotient's `toNat`
    equals `a.toNat / b.toNat`.  Feeds the overestimate bridge's `hqHat_mul_le` /
    `hqHat_ge` bounds for the MOD addback getLimbN composition. -/
theorem n4CallAddbackBeqQOutV5_toNat_eq_div (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV5 a b) :
    (n4CallAddbackBeqQOutV5 a b).toNat = a.toNat / b.toNat := by
  unfold n4CallAddbackBeqSemanticHoldsV5 n4CallAddbackBeqQTrue at hsem
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  rw [ha_val, hb_val] at hsem
  have hdiv_toNat : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div; rw [if_neg hbnz]; exact BitVec.toNat_udiv
  omega

/-- The two overestimate-bridge bounds for the corrected quotient `q_out`, on the
    original (un-normalized) `a`/`b` limbs.  Since `q_out` is the exact quotient
    (`n4CallAddbackBeqQOutV5_toNat_eq_div`), the trial-multiplication bound and the
    ge-bound both hold on the nose.  These are exactly the `hqHat_mul_le` /
    `hqHat_ge` arguments of `denorm_limbN_eq_mod_of_overestimate_getLimbN` when it
    is applied with `qHat := q_out` in the n=4 MOD addback getLimbN lane. -/
theorem n4CallAddbackBeqQOutV5_bridge_bounds (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV5 a b) :
    (n4CallAddbackBeqQOutV5 a b).toNat *
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) ∧
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
      (n4CallAddbackBeqQOutV5 a b).toNat := by
  have hq := n4CallAddbackBeqQOutV5_toNat_eq_div a b hbnz hsem
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  rw [ha_val, hb_val, hq]
  exact ⟨Nat.div_mul_le_self a.toNat b.toNat, le_refl _⟩

/-- **n=4 MOD call+addback-beq getLimbN, single-addback branch (carry ≠ 0).**
    Under the single-addback branch conditions, the four limbs of `EvmWord.mod a b`
    are the funnel-shift-down of the once-corrected remainder `ab`.  Composes the
    complete overestimate bridge (`denorm_limbN_eq_mod_of_overestimate_getLimbN`,
    instantiated with the corrected quotient `q_out = a/b`) with the per-limb
    reconciliation `ab = mulsubN4 q_out …` (via `val256` injectivity: both sides'
    `val256` equal the normalized remainder `aD % aV`, from the committed single
    crux and the exact-quotient `mulsub_exact_val256_low4`).  The bridge's
    top-borrow bound is discharged internally (exact quotient ⇒ `c3 = u4`). -/
theorem n4_call_addback_beq_mod_getLimbN_v5_single (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV5 a b)
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
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let ms := mulsubN4 (n4CallAddbackBeqQHatV5 a b)
      (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
      (n4CallAddbackBeqU4 a b - ms.2.2.2.2)
      (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
    (EvmWord.mod a b).getLimbN 0 = ((ab.1 >>> shift) ||| (ab.2.1 <<< antiShift)) ∧
    (EvmWord.mod a b).getLimbN 1 = ((ab.2.1 >>> shift) ||| (ab.2.2.1 <<< antiShift)) ∧
    (EvmWord.mod a b).getLimbN 2 = ((ab.2.2.1 >>> shift) ||| (ab.2.2.2.1 <<< antiShift)) ∧
    (EvmWord.mod a b).getLimbN 3 = (ab.2.2.2.1 >>> shift) := by
  intro shift antiShift ms ab
  -- (0) shift bounds (mirror the call-skip template).
  have hclz_le := clzResult_fst_toNat_le (b.getLimbN 3)
  have hshift_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    by_contra h; apply hshift_nz; apply BitVec.eq_of_toNat_eq
    rw [show (0 : Word).toNat = 0 from rfl]; omega
  have hshift_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have hmod_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hanti_toNat_mod :
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat := by
    have h0se12 : signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1 =
        -((clzResult (b.getLimbN 3)).1) := by rw [signExtend12_0]; simp
    rw [h0se12, BitVec.toNat_neg]
    have : ((clzResult (b.getLimbN 3)).1).toNat ≤ 2 ^ 64 := by
      have := ((clzResult (b.getLimbN 3)).1).isLt; omega
    omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  -- (1) val256(ab) = aD % aV  (committed single crux).
  have hval_ab := n4_addback_un_val256_eq_amod_single a b hb3nz hshift_nz hcall
    hborrow_ult hcarry_one hq_pos hBnz huTop hqHat
  simp only at hval_ab
  -- (2) q_out = a/b and the overestimate bridge bounds.
  have hqout := n4CallAddbackBeqQOutV5_toNat_eq_div a b hbnz hsem
  obtain ⟨hmul_le, hge⟩ := n4CallAddbackBeqQOutV5_bridge_bounds a b hbnz hsem
  -- (3) Align the accessor normalized dividend/divisor to the raw `<<< s` form
  -- (s := clz.toNat), and to the scaled values `a.toNat*2^s`, `b.toNat*2^s`.
  have hscaleU := u_val256_eq_scaled_with_overflow (a.getLimbN 0) (a.getLimbN 1)
    (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 3) hshift_nz
  have hscaleB := b3_prime_val256_eq_scaled (b.getLimbN 0) (b.getLimbN 1)
    (b.getLimbN 2) (b.getLimbN 3) hshift_nz
  simp only [hmod_eq, hanti_toNat_mod] at hscaleU hscaleB
  have ha_toNat : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_toNat : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  rw [ha_toNat] at hscaleU
  rw [hb_toNat] at hscaleB
  -- Accessor abbrevs unfolded to the raw `<<< s` form.
  have hU0 := n4CallAddbackBeqU0_eq_direct (a := a) hshift_nz
  have hU1 := n4CallAddbackBeqU1_eq_direct (a := a) hshift_nz
  have hU2 := n4CallAddbackBeqU2_eq_direct (a := a) hshift_nz
  have hU3 := n4CallAddbackBeqU3_eq_direct (a := a) hshift_nz
  have hU4 := n4CallAddbackBeqU4_eq_direct (a := a) hshift_nz
  have hB0 := n4CallAddbackBeqB0Prime_eq_direct hshift_nz
  have hB1 := n4CallAddbackBeqB1Prime_eq_direct hshift_nz
  have hB2 := n4CallAddbackBeqB2Prime_eq_direct hshift_nz
  have hB3 := n4CallAddbackBeqB3Prime_eq_direct hshift_nz
  -- aD/aV in raw `<<< s` form equal the scaled values.
  set s := (clzResult (b.getLimbN 3)).1.toNat with hs_def
  -- The raw normalized limb tuple (matches the bridge's `msN` args, s = clz.toNat).
  have hq_raw : (n4CallAddbackBeqQOutV5 a b).toNat =
      (val256 ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))
        + ((a.getLimbN 3) >>> (64 - s)).toNat * 2 ^ 256) /
      val256 ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))) := by
    rw [hscaleU, hscaleB, hqout, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos s)]
  have hBnz_raw : val256 ((b.getLimbN 0) <<< s)
      (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
      (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
      (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))) ≠ 0 := by
    rw [hscaleB]
    have : 0 < b.toNat := by
      rcases Nat.eq_zero_or_pos b.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hbnz
      · exact h
    positivity
  -- (4) val256(msN.low4) = aD_raw % aV_raw, exact-quotient mulsub.
  have hval_msN := mulsub_exact_val256_low4 (n4CallAddbackBeqQOutV5 a b)
    ((b.getLimbN 0) <<< s)
    (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
    (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
    (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
    ((a.getLimbN 0) <<< s)
    (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
    (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
    (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))
    ((a.getLimbN 3) >>> (64 - s))
    hBnz_raw hq_raw
  -- (5) aD a b = aD_raw and aV b = aV_raw (accessor = raw via `_eq_direct`).
  have haD : aD a b =
      val256 ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))
        + ((a.getLimbN 3) >>> (64 - s)).toNat * 2 ^ 256 := by
    simp only [aD, hU0, hU1, hU2, hU3, hU4]
  have haV : aV b =
      val256 ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))) := by
    simp only [aV, hB0, hB1, hB2, hB3]
  -- (6) Per-limb: ab = msN via `val256` injectivity (both = aD % aV).
  rw [haD, haV] at hval_ab
  have hval_eq : val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 =
      val256
        (mulsubN4 (n4CallAddbackBeqQOutV5 a b)
          ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
          ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))).1
        (mulsubN4 (n4CallAddbackBeqQOutV5 a b)
          ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
          ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))).2.1
        (mulsubN4 (n4CallAddbackBeqQOutV5 a b)
          ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
          ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))).2.2.1
        (mulsubN4 (n4CallAddbackBeqQOutV5 a b)
          ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
          ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))).2.2.2.1 := by
    rw [hval_ab, hval_msN]
  obtain ⟨hab0, hab1, hab2, hab3⟩ := val256_inj hval_eq
  -- (7) Bridge top-borrow bound: exact quotient ⇒ c3 = u4.
  have hc3 : (mulsubN4 (n4CallAddbackBeqQOutV5 a b)
      ((b.getLimbN 0) <<< s)
      (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
      (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
      (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
      ((a.getLimbN 0) <<< s)
      (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
      (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
      (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))).2.2.2.2.toNat ≤
      ((a.getLimbN 3) >>> (64 - s)).toNat := by
    have hcons := mulsubN4_val256_eq (n4CallAddbackBeqQOutV5 a b)
      ((b.getLimbN 0) <<< s)
      (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
      (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
      (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
      ((a.getLimbN 0) <<< s)
      (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
      (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
      (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))
    simp only at hcons
    have hqmod : (n4CallAddbackBeqQOutV5 a b).toNat *
        val256 ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))) +
        (val256 ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))
          + ((a.getLimbN 3) >>> (64 - s)).toNat * 2 ^ 256) %
        val256 ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))) =
        val256 ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))
          + ((a.getLimbN 3) >>> (64 - s)).toNat * 2 ^ 256 := by
      rw [hq_raw, Nat.mul_comm]; exact Nat.div_add_mod _ _
    omega
  -- (8) Apply the per-limb overestimate bridge with qHat := q_out, s := clz.toNat.
  have h_limbs := denorm_limbN_eq_mod_of_overestimate_getLimbN (a := a) (b := b)
    (qHat := n4CallAddbackBeqQOutV5 a b) (s := s)
    hshift_pos hshift_lt_64 hb3_bound hmul_le hge hb3nz hc3
  -- (9) Rewrite ab → msN and align the funnel shifts.
  have hmodS : (clzResult (b.getLimbN 3)).1.toNat % 64 = s := by omega
  simp only [shift, antiShift, hmodS, hanti_toNat_mod, hab0, hab1, hab2, hab3]
  exact h_limbs

/-- **n=4 MOD call+addback-beq getLimbN, double-addback branch (carry = 0).**
    Mirror of `n4_call_addback_beq_mod_getLimbN_v5_single` for the double-addback
    branch: the four limbs of `EvmWord.mod a b` are the funnel-shift-down of the
    twice-corrected remainder `ab'`.  Same composition — overestimate bridge with
    `q_out = a/b` plus `ab' = mulsubN4 q_out …` by `val256` injectivity (both
    `val256` equal `aD % aV`, from the committed double crux). -/
theorem n4_call_addback_beq_mod_getLimbN_v5_double (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV5 a b)
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
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let ms := mulsubN4 (n4CallAddbackBeqQHatV5 a b)
      (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
      (n4CallAddbackBeqU4 a b - ms.2.2.2.2)
      (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2
      (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
    (EvmWord.mod a b).getLimbN 0 = ((ab'.1 >>> shift) ||| (ab'.2.1 <<< antiShift)) ∧
    (EvmWord.mod a b).getLimbN 1 = ((ab'.2.1 >>> shift) ||| (ab'.2.2.1 <<< antiShift)) ∧
    (EvmWord.mod a b).getLimbN 2 = ((ab'.2.2.1 >>> shift) ||| (ab'.2.2.2.1 <<< antiShift)) ∧
    (EvmWord.mod a b).getLimbN 3 = (ab'.2.2.2.1 >>> shift) := by
  intro shift antiShift ms ab ab'
  have hclz_le := clzResult_fst_toNat_le (b.getLimbN 3)
  have hshift_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    by_contra h; apply hshift_nz; apply BitVec.eq_of_toNat_eq
    rw [show (0 : Word).toNat = 0 from rfl]; omega
  have hshift_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have hmod_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hanti_toNat_mod :
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat := by
    have h0se12 : signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1 =
        -((clzResult (b.getLimbN 3)).1) := by rw [signExtend12_0]; simp
    rw [h0se12, BitVec.toNat_neg]
    have : ((clzResult (b.getLimbN 3)).1).toNat ≤ 2 ^ 64 := by
      have := ((clzResult (b.getLimbN 3)).1).isLt; omega
    omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  have hval_ab' := n4_addback_un_val256_eq_amod_double a b hb3nz hshift_nz hcall
    hborrow_ult hcarry_zero hcarry2_one hq_ge2 hBnz huTop hqHat
  simp only at hval_ab'
  have hqout := n4CallAddbackBeqQOutV5_toNat_eq_div a b hbnz hsem
  obtain ⟨hmul_le, hge⟩ := n4CallAddbackBeqQOutV5_bridge_bounds a b hbnz hsem
  have hscaleU := u_val256_eq_scaled_with_overflow (a.getLimbN 0) (a.getLimbN 1)
    (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 3) hshift_nz
  have hscaleB := b3_prime_val256_eq_scaled (b.getLimbN 0) (b.getLimbN 1)
    (b.getLimbN 2) (b.getLimbN 3) hshift_nz
  simp only [hmod_eq, hanti_toNat_mod] at hscaleU hscaleB
  have ha_toNat : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_toNat : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  rw [ha_toNat] at hscaleU
  rw [hb_toNat] at hscaleB
  have hU0 := n4CallAddbackBeqU0_eq_direct (a := a) hshift_nz
  have hU1 := n4CallAddbackBeqU1_eq_direct (a := a) hshift_nz
  have hU2 := n4CallAddbackBeqU2_eq_direct (a := a) hshift_nz
  have hU3 := n4CallAddbackBeqU3_eq_direct (a := a) hshift_nz
  have hU4 := n4CallAddbackBeqU4_eq_direct (a := a) hshift_nz
  have hB0 := n4CallAddbackBeqB0Prime_eq_direct hshift_nz
  have hB1 := n4CallAddbackBeqB1Prime_eq_direct hshift_nz
  have hB2 := n4CallAddbackBeqB2Prime_eq_direct hshift_nz
  have hB3 := n4CallAddbackBeqB3Prime_eq_direct hshift_nz
  set s := (clzResult (b.getLimbN 3)).1.toNat with hs_def
  have hq_raw : (n4CallAddbackBeqQOutV5 a b).toNat =
      (val256 ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))
        + ((a.getLimbN 3) >>> (64 - s)).toNat * 2 ^ 256) /
      val256 ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))) := by
    rw [hscaleU, hscaleB, hqout, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos s)]
  have hBnz_raw : val256 ((b.getLimbN 0) <<< s)
      (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
      (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
      (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))) ≠ 0 := by
    rw [hscaleB]
    have : 0 < b.toNat := by
      rcases Nat.eq_zero_or_pos b.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hbnz
      · exact h
    positivity
  have hval_msN := mulsub_exact_val256_low4 (n4CallAddbackBeqQOutV5 a b)
    ((b.getLimbN 0) <<< s)
    (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
    (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
    (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
    ((a.getLimbN 0) <<< s)
    (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
    (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
    (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))
    ((a.getLimbN 3) >>> (64 - s))
    hBnz_raw hq_raw
  have haD : aD a b =
      val256 ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))
        + ((a.getLimbN 3) >>> (64 - s)).toNat * 2 ^ 256 := by
    simp only [aD, hU0, hU1, hU2, hU3, hU4]
  have haV : aV b =
      val256 ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))) := by
    simp only [aV, hB0, hB1, hB2, hB3]
  rw [haD, haV] at hval_ab'
  have hval_eq : val256 ab'.1 ab'.2.1 ab'.2.2.1 ab'.2.2.2.1 =
      val256
        (mulsubN4 (n4CallAddbackBeqQOutV5 a b)
          ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
          ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))).1
        (mulsubN4 (n4CallAddbackBeqQOutV5 a b)
          ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
          ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))).2.1
        (mulsubN4 (n4CallAddbackBeqQOutV5 a b)
          ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
          ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))).2.2.1
        (mulsubN4 (n4CallAddbackBeqQOutV5 a b)
          ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
          ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))).2.2.2.1 := by
    rw [hval_ab', hval_msN]
  obtain ⟨hab0, hab1, hab2, hab3⟩ := val256_inj hval_eq
  have hc3 : (mulsubN4 (n4CallAddbackBeqQOutV5 a b)
      ((b.getLimbN 0) <<< s)
      (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
      (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
      (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
      ((a.getLimbN 0) <<< s)
      (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
      (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
      (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))).2.2.2.2.toNat ≤
      ((a.getLimbN 3) >>> (64 - s)).toNat := by
    have hcons := mulsubN4_val256_eq (n4CallAddbackBeqQOutV5 a b)
      ((b.getLimbN 0) <<< s)
      (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
      (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
      (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s)))
      ((a.getLimbN 0) <<< s)
      (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
      (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
      (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))
    simp only at hcons
    have hqmod : (n4CallAddbackBeqQOutV5 a b).toNat *
        val256 ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))) +
        (val256 ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))
          + ((a.getLimbN 3) >>> (64 - s)).toNat * 2 ^ 256) %
        val256 ((b.getLimbN 0) <<< s)
          (((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s)))
          (((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s)))
          (((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))) =
        val256 ((a.getLimbN 0) <<< s)
          (((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s)))
          (((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s)))
          (((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s)))
          + ((a.getLimbN 3) >>> (64 - s)).toNat * 2 ^ 256 := by
      rw [hq_raw, Nat.mul_comm]; exact Nat.div_add_mod _ _
    omega
  have h_limbs := denorm_limbN_eq_mod_of_overestimate_getLimbN (a := a) (b := b)
    (qHat := n4CallAddbackBeqQOutV5 a b) (s := s)
    hshift_pos hshift_lt_64 hb3_bound hmul_le hge hb3nz hc3
  have hmodS : (clzResult (b.getLimbN 3)).1.toNat % 64 = s := by omega
  simp only [shift, antiShift, hmodS, hanti_toNat_mod, hab0, hab1, hab2, hab3]
  exact h_limbs

end EvmAsm.Evm64
