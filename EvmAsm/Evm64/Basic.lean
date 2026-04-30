/-
  EvmAsm.Evm64.Basic

  Types and conversions for 256-bit EVM words on 64-bit RISC-V.
  Each EvmWord is stored as 4 little-endian 64-bit limbs.
-/

import EvmAsm.Rv64.Basic
import Std.Tactic.BVDecide

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- A 256-bit EVM word. -/
abbrev EvmWord := BitVec 256

namespace EvmWord

/-- Extract the i-th 64-bit limb (little-endian, i=0 is LSB). -/
def getLimb (v : EvmWord) (i : Fin 4) : Word :=
  v.extractLsb' (i.val * 64) 64

/-- Concrete `Fin 4` `.val` projections. Used by `getLimb` rewrites
    throughout `Basic.lean` and the `EvmWordArith` bridge lemmas. -/
theorem fin4_val_0 : (0 : Fin 4).val = 0 := rfl
theorem fin4_val_1 : (1 : Fin 4).val = 1 := rfl
theorem fin4_val_2 : (2 : Fin 4).val = 2 := rfl
theorem fin4_val_3 : (3 : Fin 4).val = 3 := rfl

/-- Reconstruct a 256-bit value from 4 limbs. -/
def fromLimbs (limbs : Fin 4 → Word) : EvmWord :=
  (limbs 0).zeroExtend 256 |||
  ((limbs 1).zeroExtend 256 <<< 64) |||
  ((limbs 2).zeroExtend 256 <<< 128) |||
  ((limbs 3).zeroExtend 256 <<< 192)

/-- Bitwise AND distributes over limbs. -/
theorem getLimb_and {x y : EvmWord} {i : Fin 4} :
    (x &&& y).getLimb i = x.getLimb i &&& y.getLimb i := by
  simp only [getLimb, BitVec.extractLsb'_and]

/-- Bitwise OR distributes over limbs. -/
theorem getLimb_or {x y : EvmWord} {i : Fin 4} :
    (x ||| y).getLimb i = x.getLimb i ||| y.getLimb i := by
  simp only [getLimb, BitVec.extractLsb'_or]

/-- Bitwise XOR distributes over limbs. -/
theorem getLimb_xor {x y : EvmWord} {i : Fin 4} :
    (x ^^^ y).getLimb i = x.getLimb i ^^^ y.getLimb i := by
  simp only [getLimb, BitVec.extractLsb'_xor]

/-- Bitwise NOT distributes over limbs. -/
theorem getLimb_not {x : EvmWord} {i : Fin 4} :
    (~~~x).getLimb i = ~~~(x.getLimb i) := by
  simp only [getLimb]
  ext j
  simp only [BitVec.getElem_extractLsb', BitVec.getElem_not, BitVec.getLsbD_not]
  have hbound : i.val * 64 + j < 256 := by have := i.isLt; omega
  simp [hbound]

/-- Round-trip: fromLimbs ∘ getLimb = id. -/
theorem fromLimbs_getLimb (v : EvmWord) :
    EvmWord.fromLimbs (v.getLimb) = v := by
  simp only [fromLimbs, getLimb,
    fin4_val_0, fin4_val_1,
    fin4_val_2, fin4_val_3]
  bv_decide

private theorem getLimb_fromLimbs_0 (limbs : Fin 4 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 0 = limbs 0 := by
  simp only [fromLimbs, getLimb, fin4_val_0]
  generalize limbs 0 = l0; generalize limbs 1 = l1
  generalize limbs 2 = l2; generalize limbs 3 = l3
  bv_decide
private theorem getLimb_fromLimbs_1 (limbs : Fin 4 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 1 = limbs 1 := by
  simp only [fromLimbs, getLimb, fin4_val_1]
  generalize limbs 0 = l0; generalize limbs 1 = l1
  generalize limbs 2 = l2; generalize limbs 3 = l3
  bv_decide
private theorem getLimb_fromLimbs_2 (limbs : Fin 4 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 2 = limbs 2 := by
  simp only [fromLimbs, getLimb, fin4_val_2]
  generalize limbs 0 = l0; generalize limbs 1 = l1
  generalize limbs 2 = l2; generalize limbs 3 = l3
  bv_decide
private theorem getLimb_fromLimbs_3 (limbs : Fin 4 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 3 = limbs 3 := by
  simp only [fromLimbs, getLimb, fin4_val_3]
  generalize limbs 0 = l0; generalize limbs 1 = l1
  generalize limbs 2 = l2; generalize limbs 3 = l3
  bv_decide

/-- Round-trip: getLimb ∘ fromLimbs = id. -/
theorem getLimb_fromLimbs {limbs : Fin 4 → Word} {i : Fin 4} :
    (EvmWord.fromLimbs limbs).getLimb i = limbs i := by
  rcases i with ⟨i, hi⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · exact getLimb_fromLimbs_0 limbs
  · exact getLimb_fromLimbs_1 limbs
  · exact getLimb_fromLimbs_2 limbs
  · exact getLimb_fromLimbs_3 limbs

/-- Decompose an EvmWord's toNat into a sum of limb values times base powers.
    `v.toNat = limb0 + limb1 * 2^64 + limb2 * 2^128 + limb3 * 2^192` -/
theorem toNat_getLimb_decompose (v : EvmWord) :
    v.toNat = (v.getLimb 0).toNat + (v.getLimb 1).toNat * 2^64 +
              (v.getLimb 2).toNat * 2^128 + (v.getLimb 3).toNat * 2^192 := by
  have h0 : (v.getLimb 0).toNat = v.toNat % 2^64 := by
    simp [getLimb, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
  have h1 : (v.getLimb 1).toNat = v.toNat / 2^64 % 2^64 := by
    simp [getLimb, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
  have h2 : (v.getLimb 2).toNat = v.toNat / 2^128 % 2^64 := by
    simp [getLimb, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
  have h3 : (v.getLimb 3).toNat = v.toNat / 2^192 % 2^64 := by
    simp only [getLimb, fin4_val_3,
               BitVec.extractLsb', Nat.shiftRight_eq_div_pow,
               show 3 * 64 = 192 from by decide, BitVec.toNat_ofNat]
  rw [h0, h1, h2, h3]; omega

/-- The toNat of fromLimbs expressed as a weighted sum of individual limb values. -/
theorem fromLimbs_toNat {f : Fin 4 → Word} :
    (fromLimbs f).toNat = (f 0).toNat + (f 1).toNat * 2^64 +
                           (f 2).toNat * 2^128 + (f 3).toNat * 2^192 := by
  have h := toNat_getLimb_decompose (fromLimbs f)
  simp only [getLimb_fromLimbs] at h
  exact h

/-- The list of 4 limbs for an EvmWord. -/
def toLimbs (v : EvmWord) : List Word :=
  List.ofFn fun i : Fin 4 => v.getLimb i

theorem toLimbs_length {v : EvmWord} : v.toLimbs.length = 4 := by
  simp [toLimbs]

private theorem or3_eq_zero_left (a b c : BitVec 64) (h : a ||| b ||| c = 0) : a = 0 := by
  bv_decide
private theorem or3_eq_zero_mid (a b c : BitVec 64) (h : a ||| b ||| c = 0) : b = 0 := by
  bv_decide
private theorem or3_eq_zero_right (a b c : BitVec 64) (h : a ||| b ||| c = 0) : c = 0 := by
  bv_decide

/-- When the upper three limbs OR to zero, `v.toNat` equals `(v.getLimb 0).toNat`. -/
theorem toNat_eq_getLimb0_of_high_zero {v : EvmWord}
    (h : v.getLimb 1 ||| v.getLimb 2 ||| v.getLimb 3 = 0) :
    v.toNat = (v.getLimb 0).toNat := by
  have h1 := or3_eq_zero_left _ _ _ h
  have h2 := or3_eq_zero_mid _ _ _ h
  have h3 := or3_eq_zero_right _ _ _ h
  simp only [getLimb, fin4_val_0, fin4_val_1,
    fin4_val_2, fin4_val_3] at *
  have hn1 : (v.extractLsb' (1 * 64) 64).toNat = 0 := by rw [h1]; rfl
  have hn2 : (v.extractLsb' (2 * 64) 64).toNat = 0 := by rw [h2]; rfl
  have hn3 : (v.extractLsb' (3 * 64) 64).toNat = 0 := by rw [h3]; rfl
  simp [BitVec.extractLsb'_toNat] at hn1 hn2 hn3
  simp [BitVec.extractLsb'_toNat]
  have := v.isLt
  omega

/-- Extract the k-th 64-bit limb, returning 0 when k ≥ 4 (out of range). -/
def getLimbN (v : EvmWord) (k : Nat) : Word :=
  if h : k < 4 then v.getLimb ⟨k, h⟩ else 0

theorem getLimbN_lt (v : EvmWord) (k : Nat) (h : k < 4) :
    v.getLimbN k = v.getLimb ⟨k, h⟩ := by
  simp [getLimbN, h]

theorem getLimbN_ge (v : EvmWord) (k : Nat) (h : k ≥ 4) :
    v.getLimbN k = 0 := by
  simp [getLimbN, show ¬(k < 4) from by omega]

/-- Convert getLimb (Fin 4) to getLimbN (Nat). Use this simp lemma to normalize
    all getLimb calls to getLimbN for consistent Expr.hash in xperm. -/
theorem getLimb_eq_getLimbN {v : EvmWord} {i : Fin 4} :
    v.getLimb i = v.getLimbN i.val := by
  simp [getLimbN, i.isLt]

/-- Convert `getLimb (k : Fin 4)` to `getLimbN k` for concrete indices.
    Use `simp only [getLimb_as_getLimbN]` to batch-convert bridge lemma hypotheses. -/
theorem getLimb_as_getLimbN_0 {v : EvmWord} : v.getLimb 0 = v.getLimbN 0 := by simp [getLimbN]
theorem getLimb_as_getLimbN_1 {v : EvmWord} : v.getLimb 1 = v.getLimbN 1 := by simp [getLimbN]
theorem getLimb_as_getLimbN_2 {v : EvmWord} : v.getLimb 2 = v.getLimbN 2 := by simp [getLimbN]
theorem getLimb_as_getLimbN_3 {v : EvmWord} : v.getLimb 3 = v.getLimbN 3 := by simp [getLimbN]

-- getLimbN versions of operation lemmas (for xperm AC fast path consistency)
theorem getLimbN_and {x y : EvmWord} {k : Nat} :
    (x &&& y).getLimbN k = x.getLimbN k &&& y.getLimbN k := by
  simp [getLimbN]; split <;> simp [getLimb, BitVec.extractLsb'_and]

theorem getLimbN_or {x y : EvmWord} {k : Nat} :
    (x ||| y).getLimbN k = x.getLimbN k ||| y.getLimbN k := by
  simp [getLimbN]; split <;> simp [getLimb, BitVec.extractLsb'_or]

theorem getLimbN_xor {x y : EvmWord} {k : Nat} :
    (x ^^^ y).getLimbN k = x.getLimbN k ^^^ y.getLimbN k := by
  simp [getLimbN]; split <;> simp [getLimb, BitVec.extractLsb'_xor]

theorem getLimbN_not {x : EvmWord} {k : Nat} (hk : k < 4) :
    (~~~ x).getLimbN k = ~~~ (x.getLimbN k) := by
  simp only [getLimbN, hk, dif_pos, getLimb_not]

theorem getLimbN_zero (k : Nat) :
    (0 : EvmWord).getLimbN k = 0 := by
  unfold getLimbN; split
  · simp [getLimb]
  · rfl

theorem getLimbN_one (k : Nat) :
    (1 : EvmWord).getLimbN k = if k = 0 then 1 else 0 := by
  unfold getLimbN
  split
  · next h =>
    have hfin : ∀ j : Fin 4, (1 : EvmWord).getLimb j = if j.val = 0 then 1 else 0 := by
      decide
    exact hfin ⟨k, h⟩
  · next h => simp [show ¬(k = 0) from by omega]

/-- `(1 : EvmWord).getLimbN k = 0` for `k ≠ 0`. Avoids the chained `getLimbN_one`
    + `show ¬((k : Nat) = 0) from by decide` idiom at call sites that know `k`
    is a concrete positive literal (issue #263). -/
theorem getLimbN_one_of_ne_zero {k : Nat} (hk : k ≠ 0) :
    (1 : EvmWord).getLimbN k = 0 := by
  rw [getLimbN_one, if_neg hk]

theorem getLimbN_one_zero : (1 : EvmWord).getLimbN 0 = 1 := by
  rw [getLimbN_one, if_pos rfl]
theorem getLimbN_one_one : (1 : EvmWord).getLimbN 1 = 0 :=
  getLimbN_one_of_ne_zero (by decide)
theorem getLimbN_one_two : (1 : EvmWord).getLimbN 2 = 0 :=
  getLimbN_one_of_ne_zero (by decide)
theorem getLimbN_one_three : (1 : EvmWord).getLimbN 3 = 0 :=
  getLimbN_one_of_ne_zero (by decide)

theorem getLimbN_ite {c : Prop} [Decidable c] {x y : EvmWord} {k : Nat} :
    (if c then x else y).getLimbN k = if c then x.getLimbN k else y.getLimbN k := by
  split <;> rfl

private theorem extractLsb'_ge_width (v : BitVec 256) (s : Nat) (h : s ≥ 256) :
    BitVec.extractLsb' s 64 v = (0 : BitVec 64) := by
  ext j
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD]
  apply Nat.testBit_lt_two_pow
  calc v.toNat < 2 ^ 256 := v.isLt
    _ ≤ 2 ^ (s + ↑j) := Nat.pow_le_pow_right (by omega) (by omega)

/-- `getLimbN` equals `extractLsb'` unconditionally (out-of-range extractions are zero). -/
theorem getLimbN_eq_extractLsb' (v : EvmWord) (k : Nat) :
    v.getLimbN k = BitVec.extractLsb' (k * 64) 64 v := by
  unfold getLimbN getLimb
  split
  · rfl
  · rename_i h; exact (extractLsb'_ge_width v (k * 64) (by omega)).symm

/-- Splitting a 64-bit extraction at offset `base + bs` across two adjacent
    64-bit-aligned blocks at `base` and `base + 64`. -/
private theorem extractLsb'_split_64 (v : BitVec 256) (base bs : Nat) (hbs : bs < 64) :
    BitVec.extractLsb' (base + bs) 64 v =
    (BitVec.extractLsb' base 64 v >>> bs) |||
    ((BitVec.extractLsb' (base + 64) 64 v <<< (64 - bs)) &&&
     (if bs = 0 then (0 : BitVec 64) else BitVec.allOnes 64)) := by
  ext j
  rename_i hj
  by_cases hbs0 : bs = 0
  · subst hbs0; simp [BitVec.getElem_extractLsb']
  · simp only [if_neg hbs0]
    simp only [BitVec.getElem_extractLsb', BitVec.getElem_or, BitVec.getElem_and,
               BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft,
               BitVec.getLsbD_extractLsb', BitVec.getElem_allOnes j hj, Bool.and_true]
    by_cases hbsj : bs + j < 64
    · simp [hbsj, show j < 64 - bs from by omega]; congr 1; omega
    · simp only [hbsj, show ¬(j < 64 - bs) from by omega, decide_false, Bool.false_and,
                 Bool.not_false, Bool.true_and, Bool.false_or]
      congr 1; omega

/-- Shifting a 256-bit word right by `≥ 256` yields zero. -/
theorem ushiftRight_geq_256 {v : EvmWord} {n : Nat} (h : n ≥ 256) :
    v >>> n = (0 : EvmWord) := by
  ext j
  simp only [BitVec.getElem_ushiftRight]
  simp [BitVec.getLsbD]
  apply Nat.testBit_lt_two_pow
  calc v.toNat < 2 ^ 256 := v.isLt
    _ ≤ 2 ^ (n + ↑j) := Nat.pow_le_pow_right (by omega) (by omega)

theorem shiftLeft_geq_256 {v : EvmWord} {n : Nat} (h : n ≥ 256) :
    v <<< n = (0 : EvmWord) := by
  ext j
  simp only [BitVec.getElem_shiftLeft]
  have : (j : Nat) < n := by omega
  simp [this]

/-- **SHL bridge lemma (merge case).** When `i * 64 ≥ n`, the i-th limb of `v <<< n` equals
    a shift-and-merge of two adjacent source limbs (indexed downward by the limb shift).

    With `ls := n / 64` and `bs := n % 64`:
    `getLimb (v <<< n) i = (getLimbN v (i - ls) <<< bs) ||| ((getLimbN v (i - ls - 1) >>> (64 - bs)) &&& mask)`

    The condition `i * 64 ≥ n` ensures all 64 extracted bits come from `v`. -/
theorem getLimb_shiftLeft {v : EvmWord} {n : Nat} {i : Fin 4} (hge : i.val * 64 ≥ n) :
    getLimb (v <<< n) i =
    (getLimbN v (i.val - n / 64) <<< (n % 64)) |||
    ((getLimbN v (i.val - n / 64 - 1) >>> (64 - n % 64)) &&&
     (if n % 64 = 0 then (0 : BitVec 64) else BitVec.allOnes 64)) := by
  simp only [getLimb]
  -- Step 1: extractLsb' commutes with shiftLeft (when i*64 >= n)
  have h_shift : BitVec.extractLsb' (i.val * 64) 64 (v <<< n) =
                 BitVec.extractLsb' (i.val * 64 - n) 64 v := by
    ext j
    simp only [BitVec.getElem_extractLsb']
    simp only [BitVec.getLsbD_shiftLeft]
    have hlt256 : i.val * 64 + (j : Nat) < 256 := by omega
    have hge_n : ¬(i.val * 64 + (j : Nat) < n) := by omega
    simp [hlt256, hge_n]
    congr 1; omega
  rw [h_shift]
  -- Step 2: decompose the position
  by_cases hmod0 : n % 64 = 0
  · -- When bs = 0: position is (i - ls) * 64, no splitting needed
    have h0 : i.val * 64 - n = (i.val - n / 64) * 64 := by omega
    rw [h0, hmod0]
    simp [BitVec.and_zero, BitVec.or_zero, BitVec.shiftLeft_zero,
          getLimbN_eq_extractLsb']
  · -- When bs > 0: split across two adjacent limbs
    have h_decomp : i.val * 64 - n = (i.val - n / 64 - 1) * 64 + (64 - n % 64) := by omega
    rw [h_decomp]
    have hbs_lt : 64 - n % 64 < 64 := by omega
    rw [extractLsb'_split_64 v ((i.val - n / 64 - 1) * 64) (64 - n % 64) hbs_lt]
    -- Convert extractLsb' back to getLimbN
    have h1 : BitVec.extractLsb' ((i.val - n / 64 - 1) * 64) 64 v =
               v.getLimbN (i.val - n / 64 - 1) :=
      (getLimbN_eq_extractLsb' v (i.val - n / 64 - 1)).symm
    have h_off : (i.val - n / 64 - 1) * 64 + 64 = (i.val - n / 64) * 64 := by omega
    have h2 : BitVec.extractLsb' ((i.val - n / 64 - 1) * 64 + 64) 64 v =
               v.getLimbN (i.val - n / 64) := by
      rw [h_off]; exact (getLimbN_eq_extractLsb' v (i.val - n / 64)).symm
    rw [h1, h2]
    -- extractLsb'_split_64 gives mask `if (64 - n%64) = 0 then 0 else allOnes`.
    -- Target has mask `if n%64 = 0 then 0 else allOnes`.
    -- Since n%64 ≠ 0: both masks are `allOnes 64`.
    have hmask1 : (if (64 - n % 64 = 0) then (0 : BitVec 64) else BitVec.allOnes 64) =
                   BitVec.allOnes 64 := if_neg (by omega)
    have hmask2 : (if (n % 64 = 0) then (0 : BitVec 64) else BitVec.allOnes 64) =
                   BitVec.allOnes 64 := if_neg hmod0
    rw [hmask1, hmask2]
    -- Now both AND masks are allOnes, so x &&& allOnes = x
    simp only [BitVec.and_allOnes]
    -- Goal: (getLimbN v (i-L-1) >>> (64-bs) ||| getLimbN v (i-L) <<< (64-(64-bs)))
    --     = (getLimbN v (i-L) <<< bs ||| getLimbN v (i-L-1) >>> (64-bs))
    have h64 : 64 - (64 - n % 64) = n % 64 := by omega
    rw [h64]
    exact BitVec.or_comm _ _

/-- **SHL bridge lemma (first limb).** When `i = n / 64`, the i-th limb of `v <<< n` equals
    the lowest limb of `v` shifted left by `n % 64`. -/
theorem getLimb_shiftLeft_eq_div {v : EvmWord} {n : Nat} {i : Fin 4} (heq : i.val = n / 64) :
    getLimb (v <<< n) i = getLimbN v 0 <<< (n % 64) := by
  simp only [getLimb]
  rw [getLimbN_eq_extractLsb']
  ext j
  simp only [Nat.zero_mul, BitVec.getElem_extractLsb', BitVec.getElem_shiftLeft]
  simp only [BitVec.getLsbD_shiftLeft]
  by_cases hjbs : (j : Nat) < n % 64
  · -- j < bs: both sides false
    have hlt_n : i.val * 64 + (j : Nat) < n := by omega
    simp [hjbs, hlt_n]
  · -- j >= bs: both sides give v.getLsbD (j - n%64)
    have hge_n : ¬(i.val * 64 + (j : Nat) < n) := by omega
    have hlt256 : i.val * 64 + (j : Nat) < 256 := by omega
    simp [hjbs, hge_n, hlt256]
    congr 1; omega

/-- **SHL bridge lemma (zero limb).** When `(i + 1) * 64 ≤ n`, the i-th limb of `v <<< n`
    is zero (all extracted bits are below the shift amount). -/
theorem getLimb_shiftLeft_low {v : EvmWord} {n : Nat} {i : Fin 4} (hlo : (i.val + 1) * 64 ≤ n) :
    getLimb (v <<< n) i = 0 := by
  simp only [getLimb]
  ext j
  simp only [BitVec.getElem_extractLsb']
  simp only [BitVec.getLsbD_shiftLeft]
  have hlt : i.val * 64 + (j : Nat) < n := by omega
  simp [hlt]

/-- Shifting a 256-bit word right by 0 is the identity on each limb. -/
theorem getLimb_ushiftRight_zero {v : EvmWord} {i : Fin 4} :
    getLimb (v >>> 0) i = v.getLimb i := by
  simp [getLimb]

/-- **SHR bridge lemma.** The i-th limb of `v >>> n` equals a shift-and-merge of
    two adjacent source limbs, indexed by the limb shift `n / 64` and bit shift `n % 64`.

    Concretely, with `ls := n / 64` and `bs := n % 64`:
    - When `i + ls ≥ 4`: both `getLimbN` terms are zero, so the result is 0.
    - When `i + ls = 3`: the second `getLimbN` (index 4) is zero, giving `v.getLimb 3 >>> bs`.
    - When `i + ls < 3`: we get the full merge
      `(v.getLimb (i+ls) >>> bs) ||| ((v.getLimb (i+ls+1) <<< (64-bs)) &&& mask)`.

    The mask `if bs = 0 then 0 else allOnes 64` ensures the `bs = 0` case reduces to
    just the logical shift with no spurious high bits from the left-shift. -/
theorem getLimb_ushiftRight {v : EvmWord} {n : Nat} {i : Fin 4} :
    getLimb (v >>> n) i =
    (getLimbN v (i.val + n / 64) >>> (n % 64)) |||
    ((getLimbN v (i.val + n / 64 + 1) <<< (64 - n % 64)) &&&
     (if n % 64 = 0 then (0 : BitVec 64) else BitVec.allOnes 64)) := by
  simp only [getLimb]
  -- Step 1: extractLsb' commutes with ushiftRight
  have h_shift : BitVec.extractLsb' (i.val * 64) 64 (v >>> n) =
                 BitVec.extractLsb' (i.val * 64 + n) 64 v := by
    ext j; simp [BitVec.getElem_extractLsb', BitVec.getLsbD_ushiftRight]; congr 1; omega
  rw [h_shift]
  -- Step 2: decompose the position into limb-aligned base + bit offset
  have h_decomp : i.val * 64 + n = (i.val + n / 64) * 64 + n % 64 := by omega
  rw [h_decomp]
  -- Step 3: split the extraction across two adjacent 64-bit blocks
  rw [extractLsb'_split_64 v ((i.val + n / 64) * 64) (n % 64) (Nat.mod_lt n (by omega))]
  -- Step 4: rewrite extractLsb' back to getLimbN
  have h1 : BitVec.extractLsb' ((i.val + n / 64) * 64) 64 v =
             v.getLimbN (i.val + n / 64) :=
    (getLimbN_eq_extractLsb' v (i.val + n / 64)).symm
  have h_off : (i.val + n / 64) * 64 + 64 = (i.val + n / 64 + 1) * 64 := by omega
  have h2 : BitVec.extractLsb' ((i.val + n / 64) * 64 + 64) 64 v =
             v.getLimbN (i.val + n / 64 + 1) := by
    rw [h_off]; exact (getLimbN_eq_extractLsb' v (i.val + n / 64 + 1)).symm
  rw [h1, h2]

/-- When `v.toNat < 2^64`, the upper three limbs are zero. -/
theorem high_limbs_zero_of_toNat_lt {v : EvmWord} (h : v.toNat < 2^64) :
    v.getLimb 1 ||| v.getLimb 2 ||| v.getLimb 3 = 0 := by
  -- Each upper limb extracts bits [k*64, k*64+64) which are all zero when v < 2^64
  have hlimb : ∀ k : Fin 4, k.val ≥ 1 → v.getLimb k = 0 := by
    intro k hk
    simp only [getLimb]
    ext j
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD]
    -- v.toNat < 2^64 and k*64+j ≥ 64, so bit k*64+j of v is 0
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hge : k.val * 64 + ↑j ≥ 64 := by omega
    have hdiv : v.toNat / 2 ^ (k.val * 64 + ↑j) = 0 := by
      apply Nat.div_eq_of_lt
      calc v.toNat < 2 ^ 64 := h
        _ ≤ 2 ^ (k.val * 64 + ↑j) := Nat.pow_le_pow_right (by omega) hge
    simp [hdiv]
  have h1 := hlimb 1 (by omega)
  have h2 := hlimb 2 (by omega)
  have h3 := hlimb 3 (by omega)
  simp [h1, h2, h3]

@[simp] theorem getLimb_one {i : Fin 4} :
    (1 : EvmWord).getLimb i = if i = 0 then 1 else 0 := by
  have h : ∀ j : Fin 4, (1 : EvmWord).getLimb j = if j = 0 then 1 else 0 := by decide
  exact h i

@[simp] theorem getLimb_ite {c : Prop} [Decidable c] {x y : EvmWord} {i : Fin 4} :
    (if c then x else y).getLimb i = if c then x.getLimb i else y.getLimb i := by
  split <;> rfl

theorem eq_iff_limbs {a b : EvmWord} :
    a = b ↔ (∀ i, a.getLimb i = b.getLimb i) := by
  constructor
  · intro h; subst h; intro; rfl
  · intro h
    calc a = fromLimbs a.getLimb := (fromLimbs_getLimb a).symm
      _ = fromLimbs b.getLimb := by congr 1; funext i; exact h i
      _ = b := fromLimbs_getLimb b

theorem eq_zero_iff_limbs {a : EvmWord} :
    a = 0 ↔ a.getLimb 0 = 0 ∧ a.getLimb 1 = 0 ∧ a.getLimb 2 = 0 ∧ a.getLimb 3 = 0 := by
  constructor
  · intro h; subst h
    have hz : ∀ j : Fin 4, (0 : EvmWord).getLimb j = 0 := by decide
    exact ⟨hz 0, hz 1, hz 2, hz 3⟩
  · intro ⟨h0, h1, h2, h3⟩
    rw [← fromLimbs_getLimb a]
    unfold fromLimbs
    simp only [h0, h1, h2, h3]
    bv_decide

-- ============================================================================
-- SAR bridge lemmas: getLimb of sshiftRight (arithmetic right shift)
-- ============================================================================

/-- For merge limbs (all 64 extracted bits within v), sshiftRight agrees with ushiftRight.
    When `(i+1)*64 + n ≤ 256`, all bit positions `i*64 + j` (j < 64) satisfy
    `n + (i*64 + j) < 256`, so no sign extension occurs. -/
theorem getLimb_sshiftRight_eq_ushiftRight {v : EvmWord} {n : Nat} {i : Fin 4}
    (h : (i.val + 1) * 64 + n ≤ 256) :
    getLimb (BitVec.sshiftRight v n) i = getLimb (v >>> n) i := by
  simp only [getLimb]
  ext j
  rename_i hj
  simp only [BitVec.getElem_extractLsb']
  rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_ushiftRight]
  have h1 : ¬(256 ≤ i.val * 64 + j) := by omega
  have h2 : n + (i.val * 64 + j) < 256 := by omega
  simp [h1, h2]

/-- **SAR bridge lemma (last limb).** When `i + n/64 = 3`, the i-th limb of
    `sshiftRight v n` equals `sshiftRight (v.getLimb 3) (n % 64)`.
    This is the limb that gets arithmetic (sign-preserving) shift. -/
theorem getLimb_sshiftRight_last {v : EvmWord} {n : Nat} {i : Fin 4}
    (hiL : i.val + n / 64 = 3) :
    getLimb (BitVec.sshiftRight v n) i =
    BitVec.sshiftRight (v.getLimb ⟨3, by omega⟩) (n % 64) := by
  simp only [getLimb]
  ext j
  rename_i hj
  simp only [BitVec.getElem_extractLsb']
  rw [BitVec.getLsbD_sshiftRight]
  have h1 : ¬(256 ≤ i.val * 64 + j) := by omega
  simp only [h1, decide_false, Bool.not_false, Bool.true_and]
  simp only [BitVec.getElem_sshiftRight, BitVec.getElem_extractLsb']
  by_cases hlt : n + (i.val * 64 + j) < 256
  · have hmod_lt : n % 64 + j < 64 := by omega
    simp only [hlt, ↓reduceIte]
    rw [dif_pos hmod_lt]
    congr 1; omega
  · have hmod_ge : ¬(n % 64 + j < 64) := by omega
    simp only [hlt, ↓reduceIte]
    rw [dif_neg hmod_ge]
    simp only [BitVec.msb, BitVec.getMsbD, BitVec.getLsbD_extractLsb']
    simp only [show (0 : Nat) < 256 from by omega, show (0 : Nat) < 64 from by omega,
               show (64 : Nat) - 1 - 0 < 64 from by omega, decide_true, Bool.true_and]

/-- **SAR bridge lemma (sign limb via getLimb 3).** When `i + n/64 ≥ 4`, the i-th limb of
    `sshiftRight v n` equals `sshiftRight (v.getLimb 3) 63`. -/
theorem getLimb_sshiftRight_sign' {v : EvmWord} {n : Nat} {i : Fin 4}
    (hiL : i.val + n / 64 ≥ 4) :
    getLimb (BitVec.sshiftRight v n) i =
    BitVec.sshiftRight (v.getLimb ⟨3, by omega⟩) 63 := by
  simp only [getLimb]
  ext j
  rename_i hj
  simp only [BitVec.getElem_extractLsb']
  rw [BitVec.getLsbD_sshiftRight]
  have h1 : ¬(256 ≤ i.val * 64 + j) := by omega
  simp only [h1, decide_false, Bool.not_false, Bool.true_and]
  have : n / 64 * 64 ≤ n := Nat.div_mul_le_self n 64
  have hge : ¬(n + (i.val * 64 + j) < 256) := by omega
  simp only [hge, ↓reduceIte]
  simp only [BitVec.getElem_sshiftRight, BitVec.getElem_extractLsb']
  by_cases h3 : 63 + j < 64
  · -- j = 0: v.msb = v.getLsbD (3*64 + 63)
    rw [dif_pos h3]
    simp only [BitVec.msb, BitVec.getMsbD, show (256 : Nat) - 1 - 0 = 255 from by omega,
               show (0 : Nat) < 256 from by omega, decide_true, Bool.true_and]
    congr 1; omega
  · -- j ≥ 1: v.msb = (extractLsb' (3*64) 64 v).msb
    rw [dif_neg h3]
    simp only [BitVec.msb, BitVec.getMsbD, BitVec.getLsbD_extractLsb',
               show (0 : Nat) < 256 from by omega, show (0 : Nat) < 64 from by omega,
               show (64 : Nat) - 1 - 0 < 64 from by omega, decide_true, Bool.true_and]

/-- Shifting a 256-bit word arithmetically right by `≥ 256` yields sign extension on each limb. -/
theorem getLimb_sshiftRight_geq_256 {v : EvmWord} {n : Nat} (h : n ≥ 256) {i : Fin 4} :
    getLimb (BitVec.sshiftRight v n) i =
    BitVec.sshiftRight (v.getLimb ⟨3, by omega⟩) 63 :=
  getLimb_sshiftRight_sign' (by omega)

/-- `getLimb` of `fromLimbs` with a constant function. -/
theorem getLimb_fromLimbs_const {w : Word} {i : Fin 4} :
    (fromLimbs (fun _ => w)).getLimb i = w := by
  match i with
  | ⟨0, _⟩ => simp [fromLimbs, getLimb]; bv_decide
  | ⟨1, _⟩ => simp [fromLimbs, getLimb]; bv_decide
  | ⟨2, _⟩ => simp [fromLimbs, getLimb]; bv_decide
  | ⟨3, _⟩ => simp [fromLimbs, getLimb]; bv_decide
  | ⟨n+4, h⟩ => exact absurd h (by omega)

theorem getLimbN_fromLimbs_const {w : Word} {k : Nat} :
    (fromLimbs (fun _ => w)).getLimbN k = if k < 4 then w else 0 := by
  unfold getLimbN
  split
  · next h => simp [getLimb_fromLimbs_const]
  · next h => simp_all

/-- `k`-specialized variants of `getLimbN_fromLimbs_const` for `k = 0, 1, 2, 3`.
    Avoids the chained `getLimbN_fromLimbs_const` + `show (k : Nat) < 4 from by decide`
    + `ite_true` idiom at call sites that iterate over the four concrete limb
    indices (issue #263). -/
theorem getLimbN_fromLimbs_const_0 {w : Word} :
    (fromLimbs (fun _ => w)).getLimbN 0 = w := by
  rw [getLimbN_fromLimbs_const, if_pos (by decide)]
theorem getLimbN_fromLimbs_const_1 {w : Word} :
    (fromLimbs (fun _ => w)).getLimbN 1 = w := by
  rw [getLimbN_fromLimbs_const, if_pos (by decide)]
theorem getLimbN_fromLimbs_const_2 {w : Word} :
    (fromLimbs (fun _ => w)).getLimbN 2 = w := by
  rw [getLimbN_fromLimbs_const, if_pos (by decide)]
theorem getLimbN_fromLimbs_const_3 {w : Word} :
    (fromLimbs (fun _ => w)).getLimbN 3 = w := by
  rw [getLimbN_fromLimbs_const, if_pos (by decide)]

end EvmWord

end EvmAsm.Evm64
