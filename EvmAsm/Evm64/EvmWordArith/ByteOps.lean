/-
  EvmAsm.Evm64.EvmWordArith.ByteOps

  BYTE correctness: limb-level byte extraction = 256-bit byte extraction.
-/

import EvmAsm.Evm64.EvmWordArith.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- BYTE correctness: limb-level byte extraction = 256-bit byte extraction
-- ============================================================================

/-- Extracting a byte from a 64-bit limb within a larger value gives the same
    result as extracting directly from the larger value, because the mod 2^64
    doesn't affect bytes that fit within the limb.

    Key identity: `a % 2^64 / 2^B % 256 = a / 2^B % 256` when `B + 8 ≤ 64`.
    Proof: `2^64 = 2^B * 2^(64-B)`, and `2^(64-B) ≥ 256`, so the high quotient
    `(a / 2^64) * 2^(64-B)` is a multiple of 256 and vanishes under `% 256`. -/
private theorem mod_pow64_div_mod256_eq (a B : Nat) (hB : B + 8 ≤ 64) :
    a % 2 ^ 64 / 2 ^ B % 256 = a / 2 ^ B % 256 := by
  -- a = q * 2^64 + r, and 2^64 = 2^B * 2^(64-B)
  -- So a / 2^B = q * 2^(64-B) + r / 2^B
  -- Since 2^(64-B) is a multiple of 256 (because 64-B ≥ 8),
  -- the q * 2^(64-B) term vanishes under % 256.
  set q := a / 2 ^ 64
  set r := a % 2 ^ 64
  have : r < 2 ^ 64 := Nat.mod_lt _ (by positivity)
  have ha : a = q * 2 ^ 64 + r := by omega
  have h64 : (2 : Nat) ^ 64 = 2 ^ B * 2 ^ (64 - B) := by
    rw [← Nat.pow_add]; congr 1; omega
  -- a / 2^B = q * 2^(64-B) + r / 2^B
  have hdiv : a / 2 ^ B = q * 2 ^ (64 - B) + r / 2 ^ B := by
    conv_lhs => rw [ha, h64]
    rw [show q * (2 ^ B * 2 ^ (64 - B)) + r = r + 2 ^ B * (q * 2 ^ (64 - B)) from by ring]
    rw [Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ B)]
    omega
  -- 256 divides q * 2^(64-B)
  have hdvd : 256 ∣ q * 2 ^ (64 - B) := by
    refine Dvd.dvd.mul_left ?_ q
    exact ⟨2 ^ (64 - B - 8), by
      rw [show (256 : Nat) = 2 ^ 8 from by norm_num, ← Nat.pow_add]; congr 1; omega⟩
  rw [hdiv]
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, show 256 * k + r / 2 ^ B = r / 2 ^ B + k * 256 from by omega]
  rw [Nat.add_mul_mod_self_right]

/-- The BYTE operation: limb-level byte extraction equals direct 256-bit extraction.

    For byte index `i` (0 ≤ i < 32, big-endian), the limb-level computation:
    - `limb_from_msb = i / 8`, selecting limb `3 - i/8`
    - `bit_shift = 56 - (i%8) * 8`, shift within the 64-bit limb
    - result = `(getLimb (3 - i/8) >>> bit_shift) % 256`

    equals the direct 256-bit extraction: `(x >>> ((31-i)*8)) % 256`.
    This connects the RISC-V limb-level BYTE implementation to the
    EVM-level BYTE semantics. -/
theorem byte_extract_correct {x : EvmWord} {i : Nat} (hi : i < 32) :
    let limbIdx : Fin 4 := ⟨3 - i / 8, by omega⟩
    let bitShift := 56 - (i % 8) * 8
    ((x.getLimb limbIdx).toNat / 2 ^ bitShift) % 256 =
    (x.toNat / 2 ^ ((31 - i) * 8)) % 256 := by
  simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  -- Goal: x.toNat / 2^((3-i/8)*64) % 2^64 / 2^(56-(i%8)*8) % 256 =
  --       x.toNat / 2^((31-i)*8) % 256
  have hshift : (3 - i / 8) * 64 + (56 - i % 8 * 8) = (31 - i) * 8 := by omega
  rw [mod_pow64_div_mod256_eq _ _ (by omega)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hshift]

-- ============================================================================
-- EvmWord.byte: word-level BYTE definition and getLimb theorems
-- ============================================================================

/-- EVM BYTE semantics: extract the i-th byte (big-endian) from x, returning 0 if i ≥ 32. -/
def byte (i x : EvmWord) : EvmWord :=
  if i.toNat < 32 then
    BitVec.ofNat 256 ((x.toNat / 2 ^ ((31 - i.toNat) * 8)) % 256)
  else 0

private theorem getLimb_0_ofNat_small (n : Nat) :
    getLimb (BitVec.ofNat 256 n) 0 = BitVec.ofNat 64 n := by
  simp only [getLimb]
  simp only [Fin.val_zero, Nat.zero_mul]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega

private theorem getLimb_high_ofNat_small (n : Nat) (hn : n < 2 ^ 64)
    (i : Fin 4) (hi : i.val ≠ 0) :
    getLimb (BitVec.ofNat 256 n) i = 0 := by
  simp only [getLimb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have : 0 < i.val := Nat.pos_of_ne_zero hi
  have : 2 ^ 64 ≤ 2 ^ (i.val * 64) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : n % 2 ^ 256 = n := Nat.mod_eq_of_lt (by linarith [show 2 ^ 64 ≤ 2 ^ 256 from by norm_num])
  rw [this]
  have : n / 2 ^ (i.val * 64) = 0 := Nat.div_eq_of_lt (by linarith)
  simp [this]

theorem byte_getLimb_0 (idx x : EvmWord) (hi : idx.toNat < 32) :
    (byte idx x).getLimb 0 =
    BitVec.ofNat 64 ((x.toNat / 2 ^ ((31 - idx.toNat) * 8)) % 256) := by
  unfold byte
  rw [if_pos hi]
  exact getLimb_0_ofNat_small _

theorem byte_getLimb_high (idx x : EvmWord) (j : Fin 4) (hj : j.val ≠ 0) :
    (byte idx x).getLimb j = 0 := by
  unfold byte
  split
  · next hi =>
    have : (x.toNat / 2 ^ ((31 - idx.toNat) * 8)) % 256 < 2 ^ 64 := by
      have := Nat.mod_lt (x.toNat / 2 ^ ((31 - idx.toNat) * 8)) (by norm_num : 0 < 256)
      linarith [show (256 : Nat) ≤ 2 ^ 64 from by norm_num]
    exact getLimb_high_ofNat_small _ this j hj
  · show (0 : EvmWord).getLimb j = 0
    simp [getLimb]

/-- Bridge theorem connecting `EvmWord.byte` to limb-level extraction.
    The program computes the result per-limb; this theorem shows that
    `(byte idx x).getLimb 0` equals the limb-level extraction formula. -/
theorem byte_correct (idx x : EvmWord) (hi : idx.toNat < 32) :
    (byte idx x).getLimb 0 =
    BitVec.ofNat 64 (((x.getLimb ⟨3 - idx.toNat / 8, by omega⟩).toNat /
      2 ^ (56 - (idx.toNat % 8) * 8)) % 256) := by
  rw [byte_getLimb_0 _ _ hi]
  congr 1
  exact (byte_extract_correct hi).symm

theorem byte_zero (idx x : EvmWord) (hi : ¬ (idx.toNat < 32)) :
    byte idx x = 0 := by
  simp [byte, hi]

end EvmWord

end EvmAsm.Evm64
