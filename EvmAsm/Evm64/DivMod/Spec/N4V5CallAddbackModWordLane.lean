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

end EvmAsm.Evm64
