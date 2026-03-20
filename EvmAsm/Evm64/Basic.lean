/-
  EvmAsm.Evm64.Basic

  Types and conversions for 256-bit EVM words on 64-bit RISC-V.
  Each EvmWord is stored as 4 little-endian 64-bit limbs.
-/

import EvmAsm.Rv64.Basic
import Std.Tactic.BVDecide
import Mathlib.Tactic.Set

namespace EvmAsm.Rv64

/-- A 256-bit EVM word. -/
abbrev EvmWord := BitVec 256

namespace EvmWord

/-- Extract the i-th 64-bit limb (little-endian, i=0 is LSB). -/
def getLimb (v : EvmWord) (i : Fin 4) : Word :=
  v.extractLsb' (i.val * 64) 64

/-- Reconstruct a 256-bit value from 4 limbs. -/
def fromLimbs (limbs : Fin 4 → Word) : EvmWord :=
  (limbs 0).zeroExtend 256 |||
  ((limbs 1).zeroExtend 256 <<< 64) |||
  ((limbs 2).zeroExtend 256 <<< 128) |||
  ((limbs 3).zeroExtend 256 <<< 192)

/-- Bitwise AND distributes over limbs. -/
theorem getLimb_and (x y : EvmWord) (i : Fin 4) :
    (x &&& y).getLimb i = x.getLimb i &&& y.getLimb i := by
  simp only [getLimb, BitVec.extractLsb'_and]

/-- Bitwise OR distributes over limbs. -/
theorem getLimb_or (x y : EvmWord) (i : Fin 4) :
    (x ||| y).getLimb i = x.getLimb i ||| y.getLimb i := by
  simp only [getLimb, BitVec.extractLsb'_or]

/-- Bitwise XOR distributes over limbs. -/
theorem getLimb_xor (x y : EvmWord) (i : Fin 4) :
    (x ^^^ y).getLimb i = x.getLimb i ^^^ y.getLimb i := by
  simp only [getLimb, BitVec.extractLsb'_xor]

/-- Bitwise NOT distributes over limbs. -/
theorem getLimb_not (x : EvmWord) (i : Fin 4) :
    (~~~x).getLimb i = ~~~(x.getLimb i) := by
  simp only [getLimb]
  have hi := i.isLt
  ext j
  simp only [BitVec.getElem_extractLsb', BitVec.getElem_not, BitVec.getLsbD_not]
  have hbound : i.val * 64 + j < 256 := by omega
  simp [hbound]

/-- Round-trip: fromLimbs ∘ getLimb = id. -/
theorem fromLimbs_getLimb (v : EvmWord) :
    EvmWord.fromLimbs (v.getLimb) = v := by
  simp only [fromLimbs, getLimb,
    show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  bv_decide

private theorem getLimb_fromLimbs_0 (limbs : Fin 4 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 0 = limbs 0 := by
  simp only [fromLimbs, getLimb, show (0 : Fin 4).val = 0 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1
  generalize limbs 2 = l2; generalize limbs 3 = l3
  bv_decide
private theorem getLimb_fromLimbs_1 (limbs : Fin 4 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 1 = limbs 1 := by
  simp only [fromLimbs, getLimb, show (1 : Fin 4).val = 1 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1
  generalize limbs 2 = l2; generalize limbs 3 = l3
  bv_decide
private theorem getLimb_fromLimbs_2 (limbs : Fin 4 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 2 = limbs 2 := by
  simp only [fromLimbs, getLimb, show (2 : Fin 4).val = 2 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1
  generalize limbs 2 = l2; generalize limbs 3 = l3
  bv_decide
private theorem getLimb_fromLimbs_3 (limbs : Fin 4 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 3 = limbs 3 := by
  simp only [fromLimbs, getLimb, show (3 : Fin 4).val = 3 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1
  generalize limbs 2 = l2; generalize limbs 3 = l3
  bv_decide

/-- Round-trip: getLimb ∘ fromLimbs = id. -/
theorem getLimb_fromLimbs (limbs : Fin 4 → Word) (i : Fin 4) :
    (EvmWord.fromLimbs limbs).getLimb i = limbs i := by
  rcases i with ⟨i, hi⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · exact getLimb_fromLimbs_0 limbs
  · exact getLimb_fromLimbs_1 limbs
  · exact getLimb_fromLimbs_2 limbs
  · exact getLimb_fromLimbs_3 limbs

/-- The list of 4 limbs for an EvmWord. -/
def toLimbs (v : EvmWord) : List Word :=
  List.ofFn fun i : Fin 4 => v.getLimb i

theorem toLimbs_length (v : EvmWord) : v.toLimbs.length = 4 := by
  simp [toLimbs]

private theorem or3_eq_zero_left (a b c : BitVec 64) (h : a ||| b ||| c = 0) : a = 0 := by
  bv_decide
private theorem or3_eq_zero_mid (a b c : BitVec 64) (h : a ||| b ||| c = 0) : b = 0 := by
  bv_decide
private theorem or3_eq_zero_right (a b c : BitVec 64) (h : a ||| b ||| c = 0) : c = 0 := by
  bv_decide

/-- When the upper three limbs OR to zero, `v.toNat` equals `(v.getLimb 0).toNat`. -/
theorem toNat_eq_getLimb0_of_high_zero (v : EvmWord)
    (h : v.getLimb 1 ||| v.getLimb 2 ||| v.getLimb 3 = 0) :
    v.toNat = (v.getLimb 0).toNat := by
  have h1 := or3_eq_zero_left _ _ _ h
  have h2 := or3_eq_zero_mid _ _ _ h
  have h3 := or3_eq_zero_right _ _ _ h
  simp only [getLimb, show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl] at *
  have hn1 : (v.extractLsb' (1 * 64) 64).toNat = 0 := by rw [h1]; rfl
  have hn2 : (v.extractLsb' (2 * 64) 64).toNat = 0 := by rw [h2]; rfl
  have hn3 : (v.extractLsb' (3 * 64) 64).toNat = 0 := by rw [h3]; rfl
  simp [BitVec.extractLsb'_toNat] at hn1 hn2 hn3
  simp [BitVec.extractLsb'_toNat]
  have hv := v.isLt
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
theorem ushiftRight_geq_256 (v : EvmWord) (n : Nat) (h : n ≥ 256) :
    v >>> n = (0 : EvmWord) := by
  ext j
  simp only [BitVec.getElem_ushiftRight]
  simp [BitVec.getLsbD]
  apply Nat.testBit_lt_two_pow
  calc v.toNat < 2 ^ 256 := v.isLt
    _ ≤ 2 ^ (n + ↑j) := Nat.pow_le_pow_right (by omega) (by omega)

/-- Shifting a 256-bit word right by 0 is the identity on each limb. -/
theorem getLimb_ushiftRight_zero (v : EvmWord) (i : Fin 4) :
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
theorem getLimb_ushiftRight (v : EvmWord) (n : Nat) (i : Fin 4) :
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
theorem high_limbs_zero_of_toNat_lt (v : EvmWord) (h : v.toNat < 2^64) :
    v.getLimb 1 ||| v.getLimb 2 ||| v.getLimb 3 = 0 := by
  -- Each upper limb extracts bits [k*64, k*64+64) which are all zero when v < 2^64
  have hlimb : ∀ k : Fin 4, k.val ≥ 1 → v.getLimb k = 0 := by
    intro k hk
    simp only [getLimb]
    ext j
    simp only [BitVec.getElem_extractLsb', BitVec.getElem_zero, BitVec.getLsbD,
      show k.val * 64 + ↑j < 256 from by omega]
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

end EvmWord

end EvmAsm.Rv64
