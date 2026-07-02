/-
  EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackModGetLimb

  Combined n=4 v5 MOD call+addback-beq getLimbN: the four
  `(EvmWord.mod a b).getLimbN i` remainder facts in the carry-selected
  post-addback `un*Out` funnel form, from the runtime addback conditions (the v5
  borrow + carry2 packaged predicates + the v5 semantic).  Case-splits on the
  first addback carry `n4CallAddbackBeqCarryV5` and dispatches to the committed
  single/double getLimbN cores (`n4_call_addback_beq_mod_getLimbN_v5_single` /
  `_double`), discharging their arithmetic side conditions:
  * `hborrow_ult`   — `n4CallAddbackBeqBorrow_raw_of_runtimeV5`
  * `hcarry_one`/`hcarry_zero`/`hcarry2_one` — carry case + `addbackN4_carry_eq_one_of_ne_zero`
    (+ `n4CallAddbackBeqCarry2Nz_of_runtimeV5` for the double branch)
  * `hq_pos`/`hq_ge2`/`hqHat` — `qTrue ≤ qHat` (`n4CallAddbackBeqQHatV5_ge_qTrue`)
    + `qOut = a/b` (`n4CallAddbackBeqQOutV5_toNat_eq_div`) + the `signExtend12 4095 = -1`
    decrement arithmetic (`signExtend12_4095_toNat`), with `aD/aV = qTrue` via
    `n4CallAddbackBeqNormalized_div_eq_qTrueV5`
  * `hBnz`           — `n4CallAddbackBeqNormalizedDivisor_pos`
  * `huTop`          — `n4CallAddbackBeqU4_lt_pow63_of_shift_nz`
  MOD analog of the DIV combined `n4_call_addback_beq_div_getLimbN_v5`.  The
  quotient is `div128Quot_v5` (defeq to the cores' `n4CallAddbackBeqQHatV5`); the
  lane bridges it to the code-level `divKTrialCallV5QHat` via
  `divKTrialCallV5QHat_eq_div128Quot_v5`.
-/

import EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackModWordLane
import EvmAsm.Evm64.DivMod.Spec.N4QHatOvershoot
import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntimeV5
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

/-- `n4CallAddbackBeqQTrue a b = a.toNat / b.toNat`. -/
private theorem n4CallAddbackBeqQTrue_eq_toNat_div (a b : EvmWord) :
    n4CallAddbackBeqQTrue a b = a.toNat / b.toNat := by
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  rw [n4CallAddbackBeqQTrue_unfold, ha_val, hb_val]

/-- **n=4 MOD call+addback-beq getLimbN (carry-selected).**  The four limbs of
    `EvmWord.mod a b` are the funnel-shift-down of the post-addback remainder
    `un*Out = if carry = 0 then ab' else ab`, matching `fullModN4CallAddbackPostV5`
    (up to `divKTrialCallV5QHat = div128Quot_v5`).  Dispatches to the single/double
    cores under the runtime addback conditions. -/
theorem n4_call_addback_beq_mod_getLimbN_v5 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hsem : n4CallAddbackBeqSemanticHoldsV5 a b)
    (h_borrow : isAddbackBorrowN4CallV5Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v5 u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u4 - c3) b0' b1' b2' b3'
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let un0Out := if carry = 0 then ab'.1 else ab.1
    let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
    let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
    let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
    (EvmWord.mod a b).getLimbN 0 = ((un0Out >>> shift) ||| (un1Out <<< antiShift)) ∧
    (EvmWord.mod a b).getLimbN 1 = ((un1Out >>> shift) ||| (un2Out <<< antiShift)) ∧
    (EvmWord.mod a b).getLimbN 2 = ((un2Out >>> shift) ||| (un3Out <<< antiShift)) ∧
    (EvmWord.mod a b).getLimbN 3 = (un3Out >>> shift) := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat ms c3 ab ab' carry
        un0Out un1Out un2Out un3Out
  -- Shared discharges (independent of the carry branch).
  have hborrow_ult := n4CallAddbackBeqBorrow_raw_of_runtimeV5 h_borrow
  have hgeq := n4CallAddbackBeqQHatV5_ge_qTrue hb3nz hshift_nz hcall
  have hqout := n4CallAddbackBeqQOutV5_toNat_eq_div a b hbnz hsem
  have hqtrue := n4CallAddbackBeqQTrue_eq_toNat_div a b
  have hBpos := n4CallAddbackBeqNormalizedDivisor_pos (b := b) hb3nz
  have hu4lt := n4CallAddbackBeqU4_lt_pow63_of_shift_nz (a := a) hshift_nz
  have hnormdiv := n4CallAddbackBeqNormalized_div_eq_qTrueV5 (a := a) (b := b) hshift_nz
  have hQlt : (n4CallAddbackBeqQHatV5 a b).toNat < 2 ^ 64 :=
    (n4CallAddbackBeqQHatV5 a b).isLt
  have hBnz : val256 (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) ≠ 0 :=
    Nat.pos_iff_ne_zero.mp hBpos
  have huTop : (n4CallAddbackBeqU4 a b).toNat + 1 < 2 ^ 64 := by
    have : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
    omega
  -- Semantic identity `qHat ≥ a/b` in the original limbs.
  have hgeq' : a.toNat / b.toNat ≤ (n4CallAddbackBeqQHatV5 a b).toNat := by
    rw [← hqtrue]; exact hgeq
  by_cases hc : carry = 0
  · -- Double-addback branch (carry = 0): un*Out = ab'.
    have hcz : n4CallAddbackBeqCarryV5 a b = 0 := hc
    -- hcarry_zero (accessor form).
    have hcarry_zero := (n4CallAddbackBeqCarryV5_eq_normalized (a := a) (b := b)).symm.trans hcz
    -- hcarry2_one via the packaged carry2 predicate.
    have hcarry2g := n4CallAddbackBeqCarry2Nz_of_runtimeV5 h_carry2
    have hcarry2_ne := hcarry2g hcarry_zero
    have hcarry2_one := addbackN4_carry_eq_one_of_ne_zero _ _ _ _ _ _ _ _ hcarry2_ne
    -- hq_ge2 and hqHat (+2) from qOut = qHat + (-1) + (-1) and qHat ≥ a/b.
    have hqo := n4CallAddbackBeqQOutV5_of_carry_eq_zero hcz
    have hqoN := congrArg BitVec.toNat hqo
    rw [hqout, BitVec.toNat_add, BitVec.toNat_add, signExtend12_4095_toNat] at hqoN
    have hq_ge2 : 2 ≤ (n4CallAddbackBeqQHatV5 a b).toNat := by omega
    have hqHat : (n4CallAddbackBeqQHatV5 a b).toNat =
        n4CallAddbackBeqUNormValV5 a b / n4CallAddbackBeqBNormVal b + 2 := by
      rw [hnormdiv, hqtrue]; omega
    simp only [un0Out, un1Out, un2Out, un3Out, if_pos hc]
    exact n4_call_addback_beq_mod_getLimbN_v5_double a b hbnz hb3nz hshift_nz hsem hcall
      hborrow_ult hcarry_zero hcarry2_one hq_ge2 hBnz huTop hqHat
  · -- Single-addback branch (carry ≠ 0): un*Out = ab.
    have hcne : n4CallAddbackBeqCarryV5 a b ≠ 0 := hc
    have hcarry_ne : addbackN4_carry
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
        (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) ≠ 0 := by
      rw [← n4CallAddbackBeqCarryV5_eq_normalized]; exact hcne
    have hcarry_one := addbackN4_carry_eq_one_of_ne_zero _ _ _ _ _ _ _ _ hcarry_ne
    have hqo := n4CallAddbackBeqQOutV5_of_carry_ne_zero hcne
    have hqoN := congrArg BitVec.toNat hqo
    rw [hqout, BitVec.toNat_add, signExtend12_4095_toNat] at hqoN
    have hq_pos : 1 ≤ (n4CallAddbackBeqQHatV5 a b).toNat := by omega
    have hqHat : (n4CallAddbackBeqQHatV5 a b).toNat =
        n4CallAddbackBeqUNormValV5 a b / n4CallAddbackBeqBNormVal b + 1 := by
      rw [hnormdiv, hqtrue]; omega
    simp only [un0Out, un1Out, un2Out, un3Out, if_neg hc]
    exact n4_call_addback_beq_mod_getLimbN_v5_single a b hbnz hb3nz hshift_nz hsem hcall
      hborrow_ult hcarry_one hq_pos hBnz huTop hqHat

end EvmAsm.Evm64
