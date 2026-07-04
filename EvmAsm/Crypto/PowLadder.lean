/-
  EvmAsm.Crypto.PowLadder

  Pure-Nat specification of MSB-first square-and-multiply modular
  exponentiation (bead evm-asm-4ch8f.11).

  This is the spec side of the crypto formal-verification pilot and the
  seed of the shared field-arithmetic library
  (docs/4ch8f-crypto-strategy.md): an SAsm machine proof is written
  against exactly these names and signatures, so the definitions and
  theorem statements here must not be renamed or reshaped.

  Contents:

  * `beBytesToNat` / `beBit` — big-endian byte-string exponent encoding
    and its MSB-first bit view;
  * `ladderStep` / `ladder`  — one square-and-multiply step, and `i`
    steps of the ladder from `acc₀ = 1`;
  * `ladder_inv` / `ladder_correct` — the loop invariant
    `ladder i = x ^ (e >>> (bits - i)) % m` and the resulting
    end-to-end correctness `ladder bits = x ^ e % m`;
  * `leLimbsToNat_natToLeLimbs` / `leLimbsToNat_lt` — round-trip and
    range facts for the little-endian u64 limb encoding used by the
    ZisK `Arith256Mod`/`Arith384Mod` accelerators
    (`EvmAsm.Rv64.ZiskAccel`).

  All proofs are kernel-checked (no `native_decide`/`bv_decide`); the
  two `decide` examples at the end pin the ladder against concrete
  `x ^ e % m` values.
-/
import EvmAsm.Rv64.ZiskAccel

namespace EvmAsm.Crypto

/-- Big-endian bytes to Nat. -/
def beBytesToNat (bs : List (BitVec 8)) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- MSB-first bit `i` of a big-endian byte string: bit `7 - i % 8` of byte `i / 8`. -/
def beBit (bs : List (BitVec 8)) (i : Nat) : Bool :=
  (bs.getD (i / 8) 0).getLsbD (7 - i % 8)

/-- One MSB square-and-multiply step: square, then multiply by `x` iff the bit is set. -/
def ladderStep (m x acc : Nat) (b : Bool) : Nat :=
  if b then (acc * acc % m) * x % m else acc * acc % m

/-- `i` MSB-first ladder steps over the big-endian exponent bytes `bs`, from `acc₀ = 1`. -/
def ladder (m x : Nat) (bs : List (BitVec 8)) : Nat → Nat
  | 0 => 1
  | i + 1 => ladderStep m x (ladder m x bs i) (beBit bs i)

-- ============================================================================
-- beBytesToNat: structure lemmas
-- ============================================================================

/-- Generalized-accumulator unfolding of the `beBytesToNat` foldl. -/
private theorem foldl_be (bs : List (BitVec 8)) (acc : Nat) :
    List.foldl (fun a (b : BitVec 8) => a * 256 + b.toNat) acc bs
      = acc * 256 ^ bs.length
        + List.foldl (fun a (b : BitVec 8) => a * 256 + b.toNat) 0 bs := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (acc * 256 + b.toNat), ih (0 * 256 + b.toNat)]
    have h : acc * 256 * 256 ^ bs.length = acc * 256 ^ (bs.length + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ bs.length) 256, ← Nat.mul_assoc]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul]
    omega

private theorem beBytesToNat_cons (b : BitVec 8) (bs : List (BitVec 8)) :
    beBytesToNat (b :: bs) = b.toNat * 2 ^ (8 * bs.length) + beBytesToNat bs := by
  have h256 : (256 : Nat) ^ bs.length = 2 ^ (8 * bs.length) := by
    have h : (256 : Nat) = 2 ^ 8 := by decide
    rw [h, ← Nat.pow_mul]
  show List.foldl _ (0 * 256 + b.toNat) bs = _
  rw [foldl_be, ← h256]
  simp [beBytesToNat]

theorem beBytesToNat_lt (bs : List (BitVec 8)) : beBytesToNat bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => exact Nat.two_pow_pos _
  | cons b bs ih =>
    rw [beBytesToNat_cons, List.length_cons]
    have h1 : 2 ^ (8 * (bs.length + 1)) = 2 ^ (8 * bs.length) * 256 := by
      rw [Nat.mul_succ, Nat.pow_add]
    have hb : b.toNat < 256 := b.isLt
    rw [h1]
    calc b.toNat * 2 ^ (8 * bs.length) + beBytesToNat bs
        < b.toNat * 2 ^ (8 * bs.length) + 2 ^ (8 * bs.length) :=
          Nat.add_lt_add_left ih _
      _ = (b.toNat + 1) * 2 ^ (8 * bs.length) := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 256 * 2 ^ (8 * bs.length) :=
          Nat.mul_le_mul (by omega) (Nat.le_refl _)
      _ = 2 ^ (8 * bs.length) * 256 := Nat.mul_comm ..

theorem beBytesToNat_testBit (bs : List (BitVec 8)) (i : Nat) (hi : i < 8 * bs.length) :
    (beBytesToNat bs).testBit (8 * bs.length - 1 - i) = beBit bs i := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    simp only [List.length_cons] at hi ⊢
    rw [beBytesToNat_cons, Nat.mul_comm b.toNat,
      Nat.testBit_two_pow_mul_add _ (beBytesToNat_lt bs)]
    by_cases h8 : i < 8
    · rw [if_neg (by omega)]
      have h1 : 8 * (bs.length + 1) - 1 - i - 8 * bs.length = 7 - i := by omega
      rw [h1]
      simp only [beBit, Nat.div_eq_of_lt h8, Nat.mod_eq_of_lt h8, List.getD_cons_zero]
      rfl
    · rw [if_pos (by omega)]
      have h1 : 8 * (bs.length + 1) - 1 - i = 8 * bs.length - 1 - (i - 8) := by omega
      rw [h1, ih (i - 8) (by omega)]
      have h2 : i / 8 = (i - 8) / 8 + 1 := by omega
      have h3 : i % 8 = (i - 8) % 8 := by omega
      simp only [beBit, h2, h3, List.getD_cons_succ]

-- ============================================================================
-- Ladder invariant and correctness
-- ============================================================================

/-- Peeling one bit off a right shift:
    `e >>> (k - 1) = 2 * (e >>> k) + bit_(k-1)(e)`. -/
private theorem shiftRight_pred (e k : Nat) (hk : 0 < k) :
    e >>> (k - 1) = 2 * (e >>> k) + (e.testBit (k - 1)).toNat := by
  have hsplit : 2 ^ k = 2 ^ (k - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hsplit,
    ← Nat.div_div_eq_div_mul, Nat.testBit_eq_decide_div_mod_eq]
  generalize e / 2 ^ (k - 1) = q
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> simp [h] <;> omega

theorem ladder_inv (m x : Nat) (hm : 1 < m) (bs : List (BitVec 8)) (i : Nat)
    (hi : i ≤ 8 * bs.length) :
    ladder m x bs i = x ^ (beBytesToNat bs >>> (8 * bs.length - i)) % m := by
  induction i with
  | zero =>
    have h0 : beBytesToNat bs >>> (8 * bs.length - 0) = 0 := by
      rw [Nat.sub_zero, Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (beBytesToNat_lt bs)
    rw [h0]
    simp [ladder, Nat.mod_eq_of_lt hm]
  | succ i ih =>
    have hiN : i < 8 * bs.length := by omega
    have ihv := ih (by omega)
    have hstep : beBytesToNat bs >>> (8 * bs.length - (i + 1))
        = 2 * (beBytesToNat bs >>> (8 * bs.length - i))
          + ((beBytesToNat bs).testBit (8 * bs.length - 1 - i)).toNat := by
      have h1 := shiftRight_pred (beBytesToNat bs) (8 * bs.length - i) (by omega)
      have h2 : 8 * bs.length - (i + 1) = 8 * bs.length - i - 1 := by omega
      have h3 : 8 * bs.length - i - 1 = 8 * bs.length - 1 - i := by omega
      rw [h3] at h1
      rw [h2, h3, h1]
    have hbit := beBytesToNat_testBit bs i hiN
    show ladderStep m x (ladder m x bs i) (beBit bs i) = _
    rw [hstep, ihv, ← hbit]
    cases hb : (beBytesToNat bs).testBit (8 * bs.length - 1 - i) with
    | false =>
      simp only [ladderStep, Bool.false_eq_true, if_false, Bool.toNat_false, Nat.add_zero]
      rw [Nat.mod_mul_mod, Nat.mul_mod_mod, ← Nat.pow_add, Nat.two_mul]
    | true =>
      have hsq : (x ^ (beBytesToNat bs >>> (8 * bs.length - i)) % m)
          * (x ^ (beBytesToNat bs >>> (8 * bs.length - i)) % m) % m
          = x ^ (2 * (beBytesToNat bs >>> (8 * bs.length - i))) % m := by
        rw [Nat.mod_mul_mod, Nat.mul_mod_mod, ← Nat.pow_add, Nat.two_mul]
      simp only [ladderStep, if_true, Bool.toNat_true]
      rw [hsq, Nat.mod_mul_mod, ← Nat.pow_succ]

theorem ladder_correct (m x : Nat) (hm : 1 < m) (bs : List (BitVec 8)) :
    ladder m x bs (8 * bs.length) = x ^ beBytesToNat bs % m := by
  have h := ladder_inv m x hm bs (8 * bs.length) (Nat.le_refl _)
  simpa using h

-- ============================================================================
-- Little-endian u64 limb encoding (ZisK Arith256Mod / Arith384Mod)
-- ============================================================================

private theorem leLimbsToNat_cons (w : BitVec 64) (ws : List (BitVec 64)) :
    Rv64.Accel.leLimbsToNat (w :: ws) = Rv64.Accel.leLimbsToNat ws * 2 ^ 64 + w.toNat :=
  rfl

theorem leLimbsToNat_natToLeLimbs (n v : Nat) (h : v < 2 ^ (64 * n)) :
    Rv64.Accel.leLimbsToNat (Rv64.Accel.natToLeLimbs n v) = v := by
  induction n generalizing v with
  | zero =>
    have hv : v = 0 := by
      simp only [Nat.mul_zero, Nat.pow_zero] at h
      omega
    subst hv
    rfl
  | succ n ih =>
    have hcons : Rv64.Accel.natToLeLimbs (n + 1) v
        = BitVec.ofNat 64 v :: Rv64.Accel.natToLeLimbs n (v >>> 64) := by
      unfold Rv64.Accel.natToLeLimbs
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      have hhd : BitVec.ofNat 64 (v >>> (64 * 0)) = BitVec.ofNat 64 v := by
        simp
      have htl : (List.range n).map
            ((fun i => BitVec.ofNat 64 (v >>> (64 * i))) ∘ Nat.succ)
          = (List.range n).map (fun i => BitVec.ofNat 64 (v >>> 64 >>> (64 * i))) := by
        apply List.map_congr_left
        intro i _
        simp only [Function.comp_apply]
        congr 1
        rw [← Nat.shiftRight_add]
        congr 1
        omega
      rw [hhd, htl]
    have hlt : v >>> 64 < 2 ^ (64 * n) := by
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add]
      have he : 64 + 64 * n = 64 * (n + 1) := by omega
      rw [he]
      exact h
    rw [hcons, leLimbsToNat_cons, ih _ hlt, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    exact Nat.div_add_mod' v (2 ^ 64)

theorem leLimbsToNat_lt (n : Nat) (ws : List Word) (h : ws.length = n) :
    Rv64.Accel.leLimbsToNat ws < 2 ^ (64 * n) := by
  subst h
  induction ws with
  | nil => exact Nat.two_pow_pos _
  | cons w ws ih =>
    rw [leLimbsToNat_cons, List.length_cons]
    have h1 : 2 ^ (64 * (ws.length + 1)) = 2 ^ (64 * ws.length) * 2 ^ 64 := by
      rw [Nat.mul_succ, Nat.pow_add]
    rw [h1]
    calc Rv64.Accel.leLimbsToNat ws * 2 ^ 64 + w.toNat
        < Rv64.Accel.leLimbsToNat ws * 2 ^ 64 + 2 ^ 64 := Nat.add_lt_add_left w.isLt _
      _ = (Rv64.Accel.leLimbsToNat ws + 1) * 2 ^ 64 := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 2 ^ (64 * ws.length) * 2 ^ 64 := Nat.mul_le_mul (by omega) (Nat.le_refl _)

-- ============================================================================
-- Kernel-checked sanity examples (guard against a vacuous ladder shape)
-- ============================================================================

set_option exponentiation.threshold 70000 in
set_option maxRecDepth 4000 in
example : ladder 1009 7 [0x01, 0x23] 16 = 7 ^ 0x123 % 1009 := by decide

set_option exponentiation.threshold 70000 in
set_option maxRecDepth 4000 in
example : ladder 1000003 5 [0x00, 0xFF, 0x10] 24 = 5 ^ 0xFF10 % 1000003 := by decide

end EvmAsm.Crypto
