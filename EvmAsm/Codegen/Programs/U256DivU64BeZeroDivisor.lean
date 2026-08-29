/-
  EvmAsm.Codegen.Programs.U256DivU64BeZeroDivisor

  Closed form of the `u256_div_u64_be` machine result at divisor zero.

  The restoring-division bit step (`divBitStep`) is total: at `b = 0` the
  comparison `BitVec.ult shifted b` is false (nothing is unsigned-below
  zero), so `less = 0`, `take = 1`, `mask` is all-ones, and the subtracted
  term `b &&& mask` vanishes.  Every bit therefore shifts one dividend bit
  into the remainder and writes a `1` into the quotient — the loop never
  traps and never reads uninitialised memory, it just computes garbage.

  This file pins that garbage down exactly:
  * the quotient is `0xFF` in all 32 output bytes (`2^256 - 1` big-endian);
  * the remainder follows the shift register `rem ← 256 * rem + a[k]`,
    i.e. it is the last eight dividend bytes packed big-endian.

  Issue #12951: with `parent_gas_limit ∈ {0, 1}` the parent gas target is 0
  and the reference (`fork.py:432`) raises `ZeroDivisionError`, rejecting the
  payload.  The guest instead terminates with this definable output.  Because
  the quotient is the *constant* `0xFF…FF`, an attacker can predict it
  trivially — this is the exploitability input the maintainer asked for.
-/

import Mathlib.Data.List.GetD
import Mathlib.Tactic

import EvmAsm.Codegen.Programs.U256DivU64BeSAsm

namespace EvmAsm.Codegen.U256DivU64Be

/-! ### Nat helpers -/

/-- A Nat lemma used repeatedly below: or-ing a single bit into an even
    number is the same as adding it. -/
private theorem nat_lor_one_of_even {x : Nat} (h : x % 2 = 0) : x ||| 1 = x + 1 := by
  refine Nat.eq_of_testBit_eq (fun i => ?_)
  cases i with
  | zero => simp [Nat.testBit]; omega
  | succ j =>
    have h1 : Nat.testBit 1 (j + 1) = false := by
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
      rw [Nat.div_eq_of_lt (by simp : (1 : Nat) < 2 ^ (j + 1))]
      rfl
    have h2 : (x + 1) / 2 = x / 2 := by omega
    conv_rhs => rw [Nat.testBit_add_one]
    rw [Nat.testBit_or, Nat.testBit_add_one, h2, h1]
    simp

/-- Halving decomposition of a division by a power of two:
    `B / 2^(k-1) = 2 * (B / 2^k) + (B / 2^(k-1)) % 2`. -/
private theorem div_shift_step (B k : Nat) (hk : 1 ≤ k) :
    B / 2 ^ (k - 1) = 2 * (B / 2 ^ k) + (B / 2 ^ (k - 1)) % 2 := by
  have h1 : B / 2 ^ k = (B / 2 ^ (k - 1)) / 2 := by
    have hk2 : 2 ^ k = 2 ^ (k - 1) * 2 := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    rw [hk2, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have h2 := Nat.div_add_mod (B / 2 ^ (k - 1)) 2
  omega

/-- The single dividend bit fed in at the call with `n + 1` steps remaining
    is bit `n` of the original byte. -/
private theorem top_bit_of_shifted (B n : Nat) (hn : n ≤ 7) :
    ((B * 2 ^ (7 - n) % 256) / 128) % 2 = (B / 2 ^ n) % 2 := by
  interval_cases n <;> omega

private theorem shr63_toNat (rem : Word) :
    (rem >>> (63 : BitVec 6).toNat).toNat = rem.toNat >>> 63 := rfl

private theorem lor_one_self_of_le_one (x : Word) (hx : x.toNat ≤ 1) :
    ((1 : Word) ||| x) = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or]
  interval_cases x.toNat <;> simp

/-- At a zero divisor the bit step degenerates: the quotient always takes
    the bit and the remainder is a pure shift-in. -/
private theorem divBitStep_zero (bit rem : Word) (_hbit : bit.toNat ≤ 1) :
    U256DivU64BeSAsm.divBitStep bit 0 rem
      = (1, (rem <<< (1 : BitVec 6).toNat) ||| bit) := by
  simp only [U256DivU64BeSAsm.divBitStep]
  have hhigh : (rem >>> (63 : BitVec 6).toNat).toNat ≤ 1 := by
    rw [shr63_toNat, Nat.shiftRight_eq_div_pow]
    have := rem.isLt
    omega
  have hult : BitVec.ult ((rem <<< (1 : BitVec 6).toNat) ||| bit) 0 = false := by
    simp [BitVec.ult]
  rw [hult]
  simp only [Bool.false_eq_true, if_false]
  have hxor : ((0 : Word) ^^^ 1) = 1 := by decide
  rw [hxor, lor_one_self_of_le_one _ hhigh]
  simp

/-- The binary-tail identity driving the zero-divisor induction: the low
    `n+1` bits of `B` decompose into the top fed bit plus the shifted tail. -/
private theorem binary_tail (B n : Nat) :
    B % 2 ^ (n + 1) = 2 ^ n * (B / 2 ^ n % 2) + B % 2 ^ n := by
  have h1 := Nat.div_add_mod B (2 ^ n)
  have h2 := Nat.div_add_mod (B / 2 ^ n) 2
  have hlt : B % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have hlt1 : B / 2 ^ n % 2 < 2 := Nat.mod_lt _ (by positivity)
  have hdd : B / 2 ^ (n + 1) = B / 2 ^ n / 2 := by
    rw [show 2 ^ (n + 1) = 2 ^ n * 2 from by rw [Nat.pow_succ, Nat.mul_comm]]
    exact (Nat.div_div_eq_div_mul B (2 ^ n) 2).symm
  have key : B = 2 ^ (n + 1) * (B / 2 ^ (n + 1)) + (2 ^ n * (B / 2 ^ n % 2) + B % 2 ^ n) := by
    calc B = 2 ^ n * (B / 2 ^ n) + B % 2 ^ n := h1.symm
    _ = 2 ^ n * (2 * (B / 2 ^ n / 2) + B / 2 ^ n % 2) + B % 2 ^ n := by rw [h2]
    _ = 2 ^ (n + 1) * (B / 2 ^ (n + 1)) + (2 ^ n * (B / 2 ^ n % 2) + B % 2 ^ n) := by
          rw [hdd, show 2 ^ (n + 1) = 2 ^ n * 2 from by rw [Nat.pow_succ]]
          ring
  have hlt2 : 2 ^ n * (B / 2 ^ n % 2) + B % 2 ^ n < 2 ^ (n + 1) := by
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    rcases Nat.lt_or_ge (B / 2 ^ n % 2) 1 with h0 | h1'
    · have ht0 : B / 2 ^ n % 2 = 0 := by omega
      rw [ht0]; omega
    · have ht1 : B / 2 ^ n % 2 = 1 := by omega
      rw [ht1]; omega
  have step1 : B % 2 ^ (n + 1)
      = (2 ^ (n + 1) * (B / 2 ^ (n + 1)) + (2 ^ n * (B / 2 ^ n % 2) + B % 2 ^ n)) % 2 ^ (n + 1) :=
    congrArg (fun x => x % 2 ^ (n + 1)) key
  rw [step1, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]

/-- Doubling mod 2^64: the wrap only eats the top bit, so the low 63 bits
    survive — this is what makes the shifted register even. -/
private theorem mul_two_mod (x : Nat) : (2 * x) % 2 ^ 64 = 2 * (x % 2 ^ 63) := by
  have h := Nat.div_add_mod x (2 ^ 63)
  have h0 : x % 2 ^ 63 < 2 ^ 63 := Nat.mod_lt _ (by positivity)
  have h2 : 2 * x = 2 ^ 64 * (x / 2 ^ 63) + 2 * (x % 2 ^ 63) := by
    calc 2 * x = 2 * (2 ^ 63 * (x / 2 ^ 63) + x % 2 ^ 63) := by rw [h]
    _ = 2 * (2 ^ 63 * (x / 2 ^ 63)) + 2 * (x % 2 ^ 63) := Nat.mul_add ..
    _ = 2 ^ 64 * (x / 2 ^ 63) + 2 * (x % 2 ^ 63) := by
          rw [← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ 63), ← Nat.pow_succ]
  rw [h2, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- The zero-divisor step is a pure shift-in: appending bit `bit` (0 or 1)
    to the shifted remainder is doubling mod 2^64 plus the bit. -/
private theorem shift_lor_bit_toNat (rem bit : Word) (hbit : bit.toNat ≤ 1) :
    ((rem <<< (1 : BitVec 6).toNat) ||| bit).toNat = (2 * rem.toNat + bit.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_or]
  have hsh : (rem <<< (1 : BitVec 6).toNat).toNat = 2 * (rem.toNat % 2 ^ 63) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have h1 : (BitVec.toNat (1 : BitVec 6)) = 1 := rfl
    rw [h1, Nat.pow_one, Nat.mul_comm, mul_two_mod]
  rw [hsh]
  have hmod := mul_two_mod rem.toNat
  rcases Nat.lt_or_ge bit.toNat 1 with h0 | h1
  · have hb0 : bit.toNat = 0 := by omega
    rw [hb0]
    simp
    omega
  · have hb1 : bit.toNat = 1 := by omega
    rw [hb1, nat_lor_one_of_even (by omega)]
    omega

/-- Left-shifting the extended base byte by `7-n` and then by one equals
    shifting by `8-n` (the recursion's base-byte bookkeeping). -/
private theorem shifted_base_byte (b : BitVec 8) (n : Nat) (hn : n ≤ 7) :
    ((BitVec.zeroExtend 64 b) <<< ((7 - n) : Nat)) <<< ((1 : BitVec 6).toNat)
      = (BitVec.zeroExtend 64 b) <<< ((8 - n) : Nat) := by
  have hb := b.isLt
  have hz : (BitVec.zeroExtend 64 b).toNat = b.toNat := rfl
  have h1 : BitVec.toNat (1 : BitVec 6) = 1 := rfl
  have hle1 : b.toNat ≤ 255 := by omega
  have hbnd : b.toNat * 2 ^ (7 - n) < 2 ^ 63 := by
    calc b.toNat * 2 ^ (7 - n) ≤ 255 * 2 ^ 7 :=
          Nat.mul_le_mul hle1 (Nat.pow_le_pow_right (by norm_num)
            (show (7 : Nat) - n ≤ 7 by omega))
      _ < 2 ^ 63 := by norm_num
  have hbnd2 : b.toNat * 2 ^ (8 - n) < 2 ^ 64 := by
    calc b.toNat * 2 ^ (8 - n) ≤ 255 * 2 ^ 8 :=
          Nat.mul_le_mul hle1 (Nat.pow_le_pow_right (by norm_num)
            (show (8 : Nat) - n ≤ 8 by omega))
      _ < 2 ^ 64 := by norm_num
  have he : (BitVec.zeroExtend 64 b <<< ((7 - n) : Nat)).toNat
      = b.toNat * 2 ^ (7 - n) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hz,
      Nat.mod_eq_of_lt (by have := hbnd; omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, he, h1, pow_one,
    Nat.mod_eq_of_lt (by have := hbnd; omega),
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hz,
    Nat.mod_eq_of_lt hbnd2,
    show 2 ^ (8 - n) = 2 ^ (7 - n) * 2 from by
      rw [show 8 - n = (7 - n) + 1 from by omega, Nat.pow_succ]]
  ring

/-- Multiplicative lifting of a residue out of a `2^64`-modulus: a factor
    `c` can be moved across the mod boundary. -/
private theorem mod_mul_lift (c x y : Nat) :
    (c * (x % 2 ^ 64) + y) % 2 ^ 64 = (c * x + y) % 2 ^ 64 := by
  have hx := Nat.div_add_mod x (2 ^ 64)
  have heq : c * x + y = 2 ^ 64 * (c * (x / 2 ^ 64)) + (c * (x % 2 ^ 64) + y) := by
    calc c * x + y = c * (2 ^ 64 * (x / 2 ^ 64) + x % 2 ^ 64) + y := by rw [hx]
      _ = 2 ^ 64 * (c * (x / 2 ^ 64)) + (c * (x % 2 ^ 64) + y) := by ring
  rw [heq,
    Nat.add_comm (2 ^ 64 * (c * (x / 2 ^ 64))) (c * (x % 2 ^ 64) + y),
    Nat.add_mul_mod_self_left]

/-- The bit fed at the call with `n + 1` steps remaining: bit `n` of the
    dividend byte, extracted from the word-shifted base. -/
private theorem fed_bit_toNat (b : BitVec 8) (n : Nat) (hn : n ≤ 7) :
    (((BitVec.zeroExtend 64 b) <<< ((7 - n) : Nat)) >>> ((7 : BitVec 6).toNat) &&& (1 : Word)).toNat
      = (b.toNat / 2 ^ n) % 2 := by
  have hb : b.toNat < 2 ^ 8 := b.isLt
  have hpush : ∀ x : Word, (x >>> ((7 : BitVec 6).toNat)).toNat = x.toNat >>> 7 := fun _ => rfl
  have hpbound : 2 ^ (7 - n) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle : b.toNat * 2 ^ (7 - n) < 2 ^ 64 := by
    calc b.toNat * 2 ^ (7 - n) ≤ 255 * 2 ^ 7 := Nat.mul_le_mul (by omega) hpbound
    _ < 2 ^ 64 := by norm_num
  have hz : (BitVec.zeroExtend 64 b).toNat = b.toNat := rfl
  have hshift : ((BitVec.zeroExtend 64 b) <<< ((7 - n) : Nat)).toNat = b.toNat * 2 ^ (7 - n) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hz, Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64)]
  have hp7 : (2 : Nat) ^ 7 = 2 ^ n * 2 ^ (7 - n) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hs := Nat.div_add_mod b.toNat (2 ^ n)
  have hrlt : b.toNat % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have hsmall : b.toNat % 2 ^ n * 2 ^ (7 - n) < 2 ^ 7 := by
    rw [hp7]
    exact Nat.mul_lt_mul_of_lt_of_le hrlt (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
  have hkey : b.toNat * 2 ^ (7 - n) / 2 ^ 7 = b.toNat / 2 ^ n := by
    have hsplit : b.toNat * 2 ^ (7 - n)
        = (b.toNat / 2 ^ n) * 2 ^ 7 + b.toNat % 2 ^ n * 2 ^ (7 - n) := by
      conv_lhs => rw [← hs]
      rw [hp7]
      ring
    have hN := Nat.div_add_mod (b.toNat * 2 ^ (7 - n)) (2 ^ 7)
    omega
  rw [BitVec.toNat_and, hpush, Nat.shiftRight_eq_div_pow, hshift, hkey,
    show BitVec.toNat (1 : Word) = 1 from rfl, Nat.and_one_is_mod]

/-- The zero-divisor closed form over a full bit-step chain: after `n` steps
    the quotient is all-ones-filled and the remainder is a pure shift register
    holding the low `n` bits of the original byte, all modulo `2^64` —
    unconditionally, no bounded-remainder hypothesis. -/
private theorem aux_zero_mod (b : BitVec 8) :
    ∀ (n : Nat) (rem q : Word), n ≤ 8 →
      (U256DivU64BeSAsm.divByteStepAux
          ((BitVec.zeroExtend 64 b) <<< ((8 - n) : Nat)) 0 rem q n).1.toNat
        = (2 ^ n * q.toNat + (2 ^ n - 1)) % 2 ^ 64
      ∧ (U256DivU64BeSAsm.divByteStepAux
          ((BitVec.zeroExtend 64 b) <<< ((8 - n) : Nat)) 0 rem q n).2.toNat
        = (2 ^ n * rem.toNat + b.toNat % 2 ^ n) % 2 ^ 64 := by
  intro n
  induction n with
  | zero =>
    intro rem q _
    simp only [U256DivU64BeSAsm.divByteStepAux, Nat.pow_zero, Nat.one_mul,
      Nat.sub_self, Nat.add_zero, Nat.mod_one]
    exact ⟨(Nat.mod_eq_of_lt q.isLt).symm, (Nat.mod_eq_of_lt rem.isLt).symm⟩
  | succ n ih =>
    intro rem q hn
    have hle : n ≤ 7 := by omega
    have hbase := shifted_base_byte b n hle
    simp only [U256DivU64BeSAsm.divByteStepAux]
    rw [show (8 : Nat) - (n + 1) = 7 - n from by omega, hbase]
    have hd := fed_bit_toNat b n hle
    rw [divBitStep_zero]
    case _hbit =>
      rw [hd]
      have h2 := Nat.mod_lt (b.toNat / 2 ^ n) (y := 2) (by norm_num)
      omega
    dsimp only
    obtain ⟨hq1, hr1⟩ := ih _ _ (by omega)
    refine ⟨?_, ?_⟩
    · rw [hq1, shift_lor_bit_toNat q 1 (by simp),
        show BitVec.toNat (1 : Word) = 1 from rfl,
        mod_mul_lift (2 ^ n) (2 * q.toNat + 1) (2 ^ n - 1)]
      refine congrArg (fun x => x % 2 ^ 64) ?_
      have hP : 0 < 2 ^ n := by positivity
      rw [Nat.pow_succ]
      ring_nf
      omega
    · rw [hr1, shift_lor_bit_toNat _ _
        (by rw [hd]; have h2 := Nat.mod_lt (b.toNat / 2 ^ n) (y := 2) (by norm_num); omega),
        hd]
      rw [mod_mul_lift (2 ^ n), binary_tail b.toNat n]
      refine congrArg (fun x => x % 2 ^ 64) ?_
      ring

/-- Generic mod-lift: a multiple of `M` inside the scaled summand vanishes. -/
private theorem mod_mul_lift_gen (c x y M : Nat) (_hM : 0 < M) :
    (c * (x % M) + y) % M = (c * x + y) % M := by
  have hx := Nat.div_add_mod x M
  have heq : c * x + y = M * (c * (x / M)) + (c * (x % M) + y) := by
    calc c * x + y = c * (M * (x / M) + x % M) + y := by rw [hx]
    _ = M * (c * (x / M)) + (c * (x % M) + y) := by ring
  rw [heq, Nat.add_comm (M * (c * (x / M))) (c * (x % M) + y),
    Nat.add_mul_mod_self_left]

/-- Closed form of the b = 0 byte step: quotient word all-ones, remainder a
    pure shift-in (mod 2^64). -/
private theorem divByteStepWord_zero (byte : BitVec 8) (rem : Word) :
    (U256DivU64BeSAsm.divByteStepWord byte 0 rem).1.toNat = 255
    ∧ (U256DivU64BeSAsm.divByteStepWord byte 0 rem).2.toNat
      = (256 * rem.toNat + byte.toNat) % 2 ^ 64 := by
  have hz := aux_zero_mod byte 8 rem 0 (by norm_num)
  unfold U256DivU64BeSAsm.divByteStepWord at hz ⊢
  rw [show (8 - 8 : Nat) = 0 from rfl, BitVec.shiftLeft_zero] at hz
  have hb := byte.isLt
  refine ⟨?_, ?_⟩
  · simpa using hz.1
  · have h2' := hz.2
    rw [Nat.mod_eq_of_lt (by omega : byte.toNat < 2 ^ 8)] at h2'
    simpa using h2'

/-- Byte-narrowed form used by `divState`. -/
private theorem divByteStep_zero (byte : BitVec 8) (rem : Word) :
    (U256DivU64BeSAsm.divByteStep byte 0 rem).1 = 255
    ∧ (U256DivU64BeSAsm.divByteStep byte 0 rem).2.toNat
      = (256 * rem.toNat + byte.toNat) % 2 ^ 64 := by
  unfold U256DivU64BeSAsm.divByteStep
  obtain ⟨h1, h2⟩ := divByteStepWord_zero byte rem
  refine ⟨?_, h2⟩
  show (U256DivU64BeSAsm.divByteStepWord byte 0 rem).1.truncate 8 = 255
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h1]
  rfl

/-- Composition of the mod-arithmetic recurrence `x (i+1) = (c * x i + d i) % M`. -/
private theorem chain_two (x : Nat → Nat) (c : Nat) (d : Nat → Nat) (M : Nat)
    (_hM : 0 < M) (x0 : Nat) (hx0 : x 0 = x0) (hx0lt : x0 < M)
    (hstep : ∀ i, x (i + 1) = (c * x i + d i) % M) (n : Nat) :
    x n = (c ^ n * x0 + ∑ i ∈ Finset.range n, d i * c ^ (n - 1 - i)) % M := by
  induction n with
  | zero =>
    rw [hx0, Nat.pow_zero, Nat.one_mul, Finset.sum_range_zero, Nat.add_zero,
      Nat.mod_eq_of_lt hx0lt]
  | succ n ih =>
    rw [hstep n, ih, Nat.pow_succ, Finset.sum_range_succ, Nat.add_sub_cancel]
    have hsum : c * (∑ i ∈ Finset.range n, d i * c ^ (n - 1 - i))
        = ∑ i ∈ Finset.range n, d i * c ^ (n - i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < n := Finset.mem_range.mp hi
      rw [show n - i = (n - 1 - i) + 1 from by omega, Nat.pow_succ]
      ring
    rw [mod_mul_lift_gen c _ _ M (by omega), Nat.mul_add, hsum]
    have h1 : c * (c ^ n * x0) = c ^ (n + 1) * x0 := by
      rw [Nat.pow_succ]; ring
    have h1' : c ^ n * c * x0 = c ^ (n + 1) * x0 := by
      rw [Nat.pow_succ]
    have hlast : d n * c ^ (n - n) = d n := by simp
    simp only [Nat.add_assoc, h1, h1', hlast]

/-- `divState` preserves the dividend list's length. -/
private theorem divState_len (a orig : List (BitVec 8)) (b : Word) (k : Nat) :
    (U256DivU64BeSAsm.divState a orig b k).1.length = orig.length := by
  induction k with
  | zero => simp [U256DivU64BeSAsm.divState]
  | succ k ih =>
    rw [U256DivU64BeSAsm.divState_succ]
    simp only [List.length_set]
    simpa using ih

/-- At divisor zero every processed quotient byte is 255. -/
private theorem quot_all_255 (a orig : List (BitVec 8)) (k : Nat) (hlen : k ≤ orig.length) :
    ∀ i, i < k → (U256DivU64BeSAsm.divState a orig 0 k).1.getD i 0 = 255 := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    have hdl := divState_len a orig 0 k
    have hlen' : k ≤ orig.length := by omega
    rw [U256DivU64BeSAsm.divState_succ]
    have hq : BitVec.truncate 8
        (U256DivU64BeSAsm.divByteStepWord (a.getD k 0) 0
            (U256DivU64BeSAsm.divState a orig 0 k).2).1 = 255 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, (divByteStepWord_zero _ _).1]
      rfl
    simp only [U256DivU64BeSAsm.divByteStep]
    rw [hq]
    by_cases hik : i = k
    · rw [hik]
      have hlt : k < ((U256DivU64BeSAsm.divState a orig 0 k).1.set k 255).length := by
        rw [List.length_set]; omega
      rw [List.getD_eq_getElem _ _ hlt, List.getElem_set_self hlt]
    · have hne : k ≠ i := by omega
      have hlt2 : i < ((U256DivU64BeSAsm.divState a orig 0 k).1.set k 255).length := by
        rw [List.length_set]; omega
      have hilt0 : i < (U256DivU64BeSAsm.divState a orig 0 k).1.length := by omega
      have ih' := ih hlen' i (by omega)
      rw [List.getD_eq_getElem _ _ hilt0] at ih'
      rw [List.getD_eq_getElem _ _ hlt2, List.getElem_set_ne hne]
      exact ih'

/-- At divisor zero the remainder is the big-endian tail of the dividend mod 2^64. -/
private theorem divState_rem_zero (a orig : List (BitVec 8)) (k : Nat) :
    (U256DivU64BeSAsm.divState a orig 0 k).2.toNat
      = (∑ i ∈ Finset.range k, (a.getD i 0).toNat * 256 ^ (k - 1 - i)) % 2 ^ 64 := by
  have hx0 : (U256DivU64BeSAsm.divState a orig 0 0).2.toNat = 0 := by
    simp [U256DivU64BeSAsm.divState]
  have hx0lt : (U256DivU64BeSAsm.divState a orig 0 0).2.toNat < 2 ^ 64 := by
    rw [hx0]; norm_num
  have hstep : ∀ i, (U256DivU64BeSAsm.divState a orig 0 (i + 1)).2.toNat
      = (256 * (U256DivU64BeSAsm.divState a orig 0 i).2.toNat + (a.getD i 0).toNat) % 2 ^ 64 := by
    intro i
    rw [U256DivU64BeSAsm.divState_succ]
    show (U256DivU64BeSAsm.divByteStep (a.getD i 0) 0
      (U256DivU64BeSAsm.divState a orig 0 i).2).2.toNat = _
    exact (divByteStep_zero _ _).2
  have hres := chain_two (fun k => (U256DivU64BeSAsm.divState a orig 0 k).2.toNat) 256
    (fun i => (a.getD i 0).toNat) (2 ^ 64) (by norm_num) 0 hx0 hx0lt hstep k
  simp only [Nat.mul_zero, Nat.zero_add] at hres
  exact hres

end EvmAsm.Codegen.U256DivU64Be

-- Axiom audit while the file is small; extend as the closed form lands (coord 13030).
#print axioms EvmAsm.Codegen.U256DivU64Be.binary_tail
#print axioms EvmAsm.Codegen.U256DivU64Be.divState_len
#print axioms EvmAsm.Codegen.U256DivU64Be.quot_all_255
#print axioms EvmAsm.Codegen.U256DivU64Be.divState_rem_zero
#print axioms EvmAsm.Codegen.U256DivU64Be.aux_zero_mod
#print axioms EvmAsm.Codegen.U256DivU64Be.divByteStepWord_zero
#print axioms EvmAsm.Codegen.U256DivU64Be.chain_two
