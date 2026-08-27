/-
  EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackWordLane

  The n=4 v5 call+addback-beq word equality (limb form):
  `(EvmWord.div a b).getLimbN 0 = n4CallAddbackBeqQOutV5 a b` (and limbs 1,2,3 = 0),
  under `n4CallAddbackBeqSemanticHoldsV5 a b` (the algorithm's corrected quotient
  q_out equals the true quotient) and `b.getLimbN 3 ≠ 0`.  Direct v5 mirror of the
  v4 `n4_call_addback_beq_div_getLimbN` (CallAddbackRuntime), with `QOutV5` in place
  of `QOutV4` and the V5 semantic in place of the agnostic one.  Single-limb because
  `b3 ≠ 0 ⟹ val256 b ≥ 2^192` and `a < 2^256`.  These four facts are the
  `hdiv0..hdiv3` the n=4 call-addback lane skeleton (#7603) consumes.
  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallAddbackV5
public import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntime
public import EvmAsm.Evm64.EvmWordArith.DivLimbBridge

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (getLimbN_fromLimbs_0 getLimbN_fromLimbs_1 getLimbN_fromLimbs_2 getLimbN_fromLimbs_3
  val256 val256_ge_pow192_of_limb3 val256_bound)

/-- n=4 v5 call+addback-beq per-limb `EvmWord.div a b` facts, with the v5 corrected
    quotient `n4CallAddbackBeqQOutV5`.  v5 mirror of `n4_call_addback_beq_div_getLimbN`. -/
theorem n4_call_addback_beq_div_getLimbN_v5 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV5 a b) :
    (EvmWord.div a b).getLimbN 0 = n4CallAddbackBeqQOutV5 a b ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
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
  have hq_toNat : (n4CallAddbackBeqQOutV5 a b).toNat = (EvmWord.div a b).toNat := by omega
  have hb3_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≥ 2 ^ 192 :=
    val256_ge_pow192_of_limb3 _ _ _ _ hb3nz
  rw [hb_val] at hb3_val
  have hqlt : (n4CallAddbackBeqQOutV5 a b).toNat < 2 ^ 64 := by
    rw [hq_toNat, hdiv_toNat]
    have hbnd := val256_bound (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    rw [ha_val] at hbnd
    calc a.toNat / b.toNat ≤ (2 ^ 256 - 1) / b.toNat := Nat.div_le_div_right (by omega)
      _ ≤ (2 ^ 256 - 1) / 2 ^ 192 := Nat.div_le_div_left hb3_val (by omega)
      _ = 2 ^ 64 - 1 := by norm_num
      _ < 2 ^ 64 := by omega
  set q := n4CallAddbackBeqQOutV5 a b with hq_def
  set target := EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with | 0 => q | 1 => 0 | 2 => 0 | 3 => 0) with htarget_def
  have htarget_toNat : target.toNat = q.toNat := by
    simp [htarget_def, EvmWord.fromLimbs_toNat]
  have htarget_eq_div : target = EvmWord.div a b :=
    BitVec.eq_of_toNat_eq (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← htarget_eq_div]; exact getLimbN_fromLimbs_0
  · rw [← htarget_eq_div]; exact getLimbN_fromLimbs_1
  · rw [← htarget_eq_div]; exact getLimbN_fromLimbs_2
  · rw [← htarget_eq_div]; exact getLimbN_fromLimbs_3

end EvmAsm.Evm64
