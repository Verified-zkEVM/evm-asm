/-
  EvmAsm.Evm64.EvmWordArith.Exp

  Pure EVM EXP semantics over 256-bit words. This is the semantic target for
  the executable EXP opcode proof: exponentiation in Nat, reduced modulo 2^256.
-/

import EvmAsm.Evm64.EvmWord

namespace EvmAsm.Evm64

namespace EvmWord

/-- EVM EXP semantics: `base ^ exponent`, reduced modulo `2^256`. -/
def exp (base exponent : EvmWord) : EvmWord :=
  BitVec.ofNat 256 (base.toNat ^ exponent.toNat)

/-- `EvmWord.exp` is Nat exponentiation modulo the 256-bit word modulus. -/
theorem exp_correct (base exponent : EvmWord) :
    (exp base exponent).toNat = base.toNat ^ exponent.toNat % 2^256 := by
  simp [exp, BitVec.toNat_ofNat]

/-- EVM's `0^0` case follows Nat exponentiation and returns one. -/
theorem exp_zero_zero : exp 0 0 = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  decide

/-- Any base raised to the zero EVM word is one. -/
theorem exp_zero_right (base : EvmWord) : exp base 0 = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  simp

/-- The maximum EVM word raised to zero is one. -/
theorem exp_max_zero_right : exp (-1 : EvmWord) 0 = 1 := by
  exact exp_zero_right (-1 : EvmWord)

/-- One raised to any exponent remains one. -/
theorem exp_one_left (exponent : EvmWord) : exp 1 exponent = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  simp

/-- Zero raised to any nonzero EVM exponent remains zero. -/
theorem exp_zero_left_of_ne_zero (exponent : EvmWord) (h : exponent ≠ 0) :
    exp 0 exponent = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  have hpos : 0 < exponent.toNat := by
    rcases Nat.eq_zero_or_pos exponent.toNat with hz | hp
    · exact absurd (BitVec.eq_of_toNat_eq (by simp [hz])) h
    · exact hp
  simp [Nat.zero_pow hpos]

/-- Zero raised to an exponent with positive Nat value remains zero. -/
theorem exp_zero_left_of_toNat_pos (exponent : EvmWord)
    (h_pos : 0 < exponent.toNat) :
    exp 0 exponent = 0 := by
  exact exp_zero_left_of_ne_zero exponent (by
    intro h_zero
    rw [h_zero] at h_pos
    simp at h_pos)

/-- Zero raised to one remains zero. -/
theorem exp_zero_one : exp (0 : EvmWord) 1 = 0 := by
  exact exp_zero_left_of_ne_zero 1 (by decide)

/-- Zero raised to the maximum EVM word exponent remains zero. -/
theorem exp_zero_left_max : exp 0 (-1 : EvmWord) = 0 := by
  exact exp_zero_left_of_ne_zero (-1 : EvmWord) (by decide)

/-- Any base raised to the EVM word one is itself. -/
theorem exp_one_right (base : EvmWord) : exp base 1 = base := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  simp [Nat.mod_eq_of_lt base.isLt]

/-- The maximum EVM word raised to one remains the maximum EVM word. -/
theorem exp_max_one_right : exp (-1 : EvmWord) 1 = (-1 : EvmWord) := by
  exact exp_one_right (-1 : EvmWord)

/-- Two raised to one remains two. -/
theorem exp_two_one : exp (2 : EvmWord) 1 = 2 := by
  exact exp_one_right (2 : EvmWord)

/-- Successor recurrence for EXP when the exponent increment does not wrap. -/
theorem exp_succ_right_of_toNat_lt (base exponent : EvmWord)
    (h : exponent.toNat + 1 < 2^256) :
    exp base (exponent + 1) = base * exp base exponent := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  have hSucc : (exponent + 1).toNat = exponent.toNat + 1 := by
    rw [BitVec.toNat_add]
    have h1 : (1 : EvmWord).toNat = 1 := by decide
    rw [h1]
    exact Nat.mod_eq_of_lt h
  rw [hSucc]
  rw [BitVec.toNat_mul]
  rw [exp_correct]
  rw [Nat.pow_succ]
  rw [Nat.mul_comm (base.toNat ^ exponent.toNat) base.toNat]
  rw [Nat.mul_mod]
  rw [Nat.mod_eq_of_lt base.isLt]

/-- Squaring recurrence for EXP when the next exponent is twice the previous
    exponent. -/
theorem exp_double_right_of_toNat_eq (base exponent nextExponent : EvmWord)
    (hNext : nextExponent.toNat = 2 * exponent.toNat) :
    exp base nextExponent = exp base exponent * exp base exponent := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct, BitVec.toNat_mul, exp_correct, hNext]
  rw [show base.toNat ^ (2 * exponent.toNat) =
      base.toNat ^ exponent.toNat * base.toNat ^ exponent.toNat by
    rw [show 2 * exponent.toNat = exponent.toNat + exponent.toNat by omega]
    rw [Nat.pow_add]]
  rw [← Nat.mul_mod]

/-- Square-and-multiply recurrence for EXP when the next exponent is twice the
    previous exponent plus one. -/
theorem exp_double_add_one_right_of_toNat_eq
    (base exponent nextExponent : EvmWord)
    (hNext : nextExponent.toNat = 2 * exponent.toNat + 1) :
    exp base nextExponent = base * (exp base exponent * exp base exponent) := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct, BitVec.toNat_mul, BitVec.toNat_mul, exp_correct, hNext]
  rw [show base.toNat ^ (2 * exponent.toNat + 1) =
      base.toNat * (base.toNat ^ exponent.toNat * base.toNat ^ exponent.toNat) by
    rw [show 2 * exponent.toNat + 1 =
        (exponent.toNat + exponent.toNat) + 1 by omega]
    rw [Nat.pow_succ, Nat.pow_add]
    rw [Nat.mul_comm
      (base.toNat ^ exponent.toNat * base.toNat ^ exponent.toNat) base.toNat]]
  rw [← Nat.mul_mod
    (base.toNat ^ exponent.toNat) (base.toNat ^ exponent.toNat) (2^256)]
  rw [Nat.mul_mod
    (base.toNat) (base.toNat ^ exponent.toNat * base.toNat ^ exponent.toNat)
    (2^256)]
  rw [Nat.mul_mod
    (base.toNat)
    ((base.toNat ^ exponent.toNat * base.toNat ^ exponent.toNat) % 2^256)
    (2^256)]
  rw [Nat.mod_mod]

/-- One MSB-first square-and-multiply step on the accumulator: square, then
    multiply by `base` when the current exponent bit is set. This is the pure
    per-iteration accumulator update performed by the EXP loop body. -/
def expSqMulStep (base acc : EvmWord) (bit : Bool) : EvmWord :=
  if bit then base * (acc * acc) else acc * acc

/-- Accumulator invariant preservation for one square-and-multiply step.

    If the accumulator currently equals `exp base e` (the running power for the
    processed exponent prefix `e`), then after one MSB-first step consuming
    `bit` it equals `exp base e'`, where `e'` is the extended prefix
    `e' = 2*e + bit`.  This is the per-iteration semantic bridge the EXP loop
    body realizes; it unifies `exp_double_right_of_toNat_eq` (bit = 0) and
    `exp_double_add_one_right_of_toNat_eq` (bit = 1). -/
theorem expSqMulStep_correct (base e e' : EvmWord) (bit : Bool)
    (hNext : e'.toNat = 2 * e.toNat + (if bit then 1 else 0)) :
    expSqMulStep base (exp base e) bit = exp base e' := by
  unfold expSqMulStep
  cases bit with
  | false =>
    show exp base e * exp base e = exp base e'
    have hNext' : e'.toNat = 2 * e.toNat := by simpa using hNext
    exact (exp_double_right_of_toNat_eq base e e' hNext').symm
  | true =>
    show base * (exp base e * exp base e) = exp base e'
    have hNext' : e'.toNat = 2 * e.toNat + 1 := by simpa using hNext
    exact (exp_double_add_one_right_of_toNat_eq base e e' hNext').symm

/-- The square-and-multiply step from the unit accumulator (`exp base 0 = 1`)
    yields `base^bit`: the first MSB-first iteration's accumulator value. -/
theorem expSqMulStep_one (base e' : EvmWord) (bit : Bool)
    (hNext : e'.toNat = (if bit then 1 else 0)) :
    expSqMulStep base (1 : EvmWord) bit = exp base e' := by
  have h1 : (1 : EvmWord) = exp base (0 : EvmWord) := (exp_zero_right base).symm
  rw [h1]
  exact expSqMulStep_correct base 0 e' bit (by simpa using hNext)

/-- MSB-first fold of the square-and-multiply step over a list of exponent
    bits (list head = most significant bit). This is the pure accumulator
    trajectory the 256-iteration EXP loop body realizes. -/
def expSqMulFold (base acc : EvmWord) : List Bool → EvmWord
  | [] => acc
  | b :: bs => expSqMulFold base (expSqMulStep base acc b) bs

/-- Value of an MSB-first bit list (list head = most significant bit). -/
def bitsToNatMsb : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) * 2 ^ bs.length + bitsToNatMsb bs

/-- MSB-first square-and-multiply fold correctness, generalized over a running
    prefix exponent `e`.

    If the accumulator equals `exp base e` for the processed prefix `e`, folding
    the remaining `bits` (most significant first) yields `exp base ef`, where
    `ef` is the full exponent `ef = e * 2^|bits| + value(bits)` — provided that
    value fits in 256 bits (which holds for any ≤256-bit EVM exponent). -/
theorem expSqMulFold_exp (base : EvmWord) (bits : List Bool) :
    ∀ (e ef : EvmWord), ef.toNat < 2 ^ 256 →
      ef.toNat = e.toNat * 2 ^ bits.length + bitsToNatMsb bits →
      expSqMulFold base (exp base e) bits = exp base ef := by
  induction bits with
  | nil =>
    intro e ef _ hef
    simp only [expSqMulFold]
    simp only [bitsToNatMsb, List.length_nil, Nat.pow_zero, Nat.mul_one,
      Nat.add_zero] at hef
    rw [BitVec.eq_of_toNat_eq hef.symm]
  | cons b bs ih =>
    intro e ef hlt hef
    simp only [expSqMulFold]
    -- The extended prefix `e1 = 2*e + b` is bounded by `ef`, hence fits.
    have h3 : (2 : Nat) ≤ 2 ^ (b :: bs).length := by
      rw [List.length_cons]
      calc (2 : Nat) = 2 ^ 1 := (Nat.pow_one 2).symm
        _ ≤ 2 ^ (bs.length + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hpos : 1 ≤ 2 ^ bs.length := Nat.one_le_pow _ _ (by omega)
    have hA : 2 * e.toNat ≤ e.toNat * 2 ^ (b :: bs).length := by
      calc 2 * e.toNat = e.toNat * 2 := by rw [Nat.mul_comm]
        _ ≤ e.toNat * 2 ^ (b :: bs).length := Nat.mul_le_mul_left _ h3
    have hB : (if b then 1 else 0) ≤ bitsToNatMsb (b :: bs) := by
      simp only [bitsToNatMsb]
      calc (if b then (1 : Nat) else 0) = (if b then 1 else 0) * 1 := (Nat.mul_one _).symm
        _ ≤ (if b then 1 else 0) * 2 ^ bs.length := Nat.mul_le_mul_left _ hpos
        _ ≤ (if b then 1 else 0) * 2 ^ bs.length + bitsToNatMsb bs := Nat.le_add_right _ _
    have hge : 2 * e.toNat + (if b then 1 else 0) ≤ ef.toNat := by
      rw [hef]; omega
    have hbnd : 2 * e.toNat + (if b then 1 else 0) < 2 ^ 256 := by omega
    have he1 : (BitVec.ofNat 256 (2 * e.toNat + (if b then 1 else 0)) : EvmWord).toNat
        = 2 * e.toNat + (if b then 1 else 0) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbnd]
    rw [expSqMulStep_correct base e
      (BitVec.ofNat 256 (2 * e.toNat + (if b then 1 else 0))) b he1]
    refine ih (BitVec.ofNat 256 (2 * e.toNat + (if b then 1 else 0))) ef hlt ?_
    rw [he1, hef]
    simp only [bitsToNatMsb, List.length_cons, Nat.pow_succ]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ bs.length) 2,
      ← Nat.mul_assoc e.toNat 2 (2 ^ bs.length), Nat.mul_comm e.toNat 2,
      Nat.mul_assoc 2 e.toNat (2 ^ bs.length)]
    omega

/-- MSB-first square-and-multiply from the unit accumulator computes `EvmWord.exp`.

    Folding the square-and-multiply step from `acc = 1` (`= exp base 0`) over any
    bit sequence whose MSB-first value equals the exponent yields
    `exp base exponent`.  This is the semantic capstone the EXP loop realizes:
    the loop body produces exactly such a bit sequence (the 256 exponent bits,
    most significant first), so its accumulator ends at `base ^ exponent`. -/
theorem expSqMulFold_one (base exponent : EvmWord) (bits : List Bool)
    (hval : bitsToNatMsb bits = exponent.toNat) :
    expSqMulFold base (1 : EvmWord) bits = exp base exponent := by
  rw [show (1 : EvmWord) = exp base 0 from (exp_zero_right base).symm]
  refine expSqMulFold_exp base bits 0 exponent exponent.isLt ?_
  simp [hval]

/-- The MSB-first bit list of the low `k` bits of `v` (most significant of the
    `k` bits first): position `k-1` down to position `0`. -/
def natBitsMsb : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, v => decide (v / 2 ^ k % 2 = 1) :: natBitsMsb k v

/-- `natBitsMsb k v` has exactly `k` bits. -/
theorem natBitsMsb_length (k v : Nat) : (natBitsMsb k v).length = k := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp [natBitsMsb, ih]

/-- The MSB-first value of `natBitsMsb k v` is `v` reduced mod `2^k`. -/
theorem bitsToNatMsb_natBitsMsb (k v : Nat) :
    bitsToNatMsb (natBitsMsb k v) = v % 2 ^ k := by
  induction k generalizing v with
  | zero => simp [natBitsMsb, bitsToNatMsb, Nat.pow_zero, Nat.mod_one]
  | succ k ih =>
    simp only [natBitsMsb, bitsToNatMsb, natBitsMsb_length]
    have hcoef :
        (if decide (v / 2 ^ k % 2 = 1) then (1 : Nat) else 0) = v / 2 ^ k % 2 := by
      rcases (show v / 2 ^ k % 2 = 0 ∨ v / 2 ^ k % 2 = 1 from by omega) with h | h <;>
        rw [h] <;> decide
    rw [hcoef, ih, Nat.pow_succ, Nat.mod_mul,
      Nat.mul_comm (2 ^ k) (v / 2 ^ k % 2)]
    omega

/-- The canonical 256-bit MSB-first decomposition of an EvmWord has value equal
    to the word itself (no reduction needed, since `w.toNat < 2^256`). -/
theorem bitsToNatMsb_natBitsMsb_toNat (w : EvmWord) :
    bitsToNatMsb (natBitsMsb 256 w.toNat) = w.toNat := by
  rw [bitsToNatMsb_natBitsMsb, Nat.mod_eq_of_lt w.isLt]

/-- Square-and-multiply over the canonical 256-bit MSB-first decomposition of the
    exponent computes `EvmWord.exp`. This is the concrete bit-sequence instance
    of `expSqMulFold_one`: the EXP loop consumes exactly these 256 bits (most
    significant first), so its accumulator ends at `base ^ exponent mod 2^256`. -/
theorem expSqMulFold_natBitsMsb (base exponent : EvmWord) :
    expSqMulFold base 1 (natBitsMsb 256 exponent.toNat) = exp base exponent :=
  expSqMulFold_one base exponent _ (bitsToNatMsb_natBitsMsb_toNat exponent)

/-- The GH #92 cross-limb boundary case `EXP(2, 64)`. -/
theorem exp_two_64 : exp (2 : EvmWord) (64 : EvmWord) =
    BitVec.ofNat 256 (2^64) := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  decide

/-- The GH #92 mid-word boundary case `EXP(2, 128)`. -/
theorem exp_two_128 : exp (2 : EvmWord) (128 : EvmWord) =
    BitVec.ofNat 256 (2^128) := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  decide

/-- The GH #92 pre-wrap boundary case `EXP(2, 255)` is the high bit. -/
theorem exp_two_255 : exp (2 : EvmWord) (255 : EvmWord) =
    BitVec.ofNat 256 (2^255) := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  decide

/-- The GH #92 boundary case `EXP(2, 256)` wraps to zero modulo `2^256`. -/
theorem exp_two_256 : exp (2 : EvmWord) (256 : EvmWord) = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  decide

-- Edge checks required by GH #92's EXP acceptance notes.
example : exp (0 : EvmWord) (0 : EvmWord) = 1 := by
  exact exp_zero_zero

example : exp (2 : EvmWord) (256 : EvmWord) = 0 := by
  exact exp_two_256

end EvmWord

end EvmAsm.Evm64
