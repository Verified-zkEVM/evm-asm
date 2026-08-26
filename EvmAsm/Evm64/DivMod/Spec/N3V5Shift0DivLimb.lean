/-
  EvmAsm.Evm64.DivMod.Spec.N3V5Shift0DivLimb

  Lane-ready (`a b : EvmWord`) and per-limb forms of the n=3 v5 SHIFT=0 quotient
  correctness.  Bridges the `fromLimbs`-form `n3_shift0_quotient_word_eq_div`
  (#7561) to the `a b` form via `EvmWord.fromLimbs_match_getLimbN_id` (the `b3=0`
  padding discharged by the shape), then decomposes it into the four
  `(EvmWord.div a b).getLimbN i = digit_i` equalities via `getLimbN_fromLimbs_*`.
  These are (modulo the `n3Shift0R*` threading) the `hdiv0..hdiv3` facts the n=3
  shift=0 lane feeds to the post bridge `n3_shift0_fullPost_to_divStackDispatchPostV5`
  (#7559).  n=3 / 2-digit analog of `n2_shift0_quotient_word_eq_div_lane`
  (N2V5Shift0QuotientLane) + `n2_shift0_div_getLimbN_lane` (N2V5Shift0DivLimb).
  Bead `evm-asm-wbc4i.9.3.3.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N3V5Shift0Quotient

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Lane form of the shift=0 n=3 quotient word: equals `EvmWord.div a b`. -/
theorem n3_shift0_quotient_word_eq_div_lane (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 : Word) (bltu_1 bltu_0 : Bool)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3z : b.getLimbN 3 = 0)
    (hb2ge : b2.toNat ≥ 2^63)
    (hc1 : bltu_1 = true → BitVec.ult (0:Word) b2 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (0:Word) b2)
    (hc0 : bltu_0 = true →
      BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2) :
    EvmWord.fromLimbs (fun i : Fin 4 => match i with
        | 0 => (iterN3V5 bltu_0 b0 b1 b2 0 a0
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).1
        | 1 => (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).1
        | 2 => 0
        | 3 => 0)
      = EvmWord.div a b := by
  have hbase := n3_shift0_quotient_word_eq_div a0 a1 a2 a3 b0 b1 b2 hb2ge bltu_1 bltu_0
    hc1 hm1 hc0 hm0
  refine hbase.trans ?_
  congr 1
  · conv_rhs => rw [← EvmWord.fromLimbs_match_getLimbN_id a]
    congr 1
    funext i
    fin_cases i <;> simp only [ha0, ha1, ha2, ha3]
  · conv_rhs => rw [← EvmWord.fromLimbs_match_getLimbN_id b]
    congr 1
    funext i
    fin_cases i <;> simp only [hb0, hb1, hb2, hb3z]

/-- The four `(EvmWord.div a b).getLimbN i` shift=0 digit equalities. -/
theorem n3_shift0_div_getLimbN_lane (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 : Word) (bltu_1 bltu_0 : Bool)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3z : b.getLimbN 3 = 0)
    (hb2ge : b2.toNat ≥ 2^63)
    (hc1 : bltu_1 = true → BitVec.ult (0:Word) b2 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (0:Word) b2)
    (hc0 : bltu_0 = true →
      BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2) :
    (EvmWord.div a b).getLimbN 0 =
        (iterN3V5 bltu_0 b0 b1 b2 0 a0
          (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
          (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
          (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).1 ∧
    (EvmWord.div a b).getLimbN 1 = (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).1 ∧
    (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  have hword := n3_shift0_quotient_word_eq_div_lane a b a0 a1 a2 a3 b0 b1 b2 bltu_1 bltu_0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3z hb2ge hc1 hm1 hc0 hm0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← hword]
  · exact EvmWord.getLimbN_fromLimbs_0
  · exact EvmWord.getLimbN_fromLimbs_1
  · exact EvmWord.getLimbN_fromLimbs_2
  · exact EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
