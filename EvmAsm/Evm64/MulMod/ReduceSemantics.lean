/-
  EvmAsm.Evm64.MulMod.ReduceSemantics

  Folded semantic helpers for the bit-serial 512-by-256 MULMOD reducer.
  These definitions describe the accumulator state used by
  `evm_mulmod_reduce512_inner_step`; later proof slices connect the RV64
  instruction sequence to these helpers.
-/

import EvmAsm.Evm64.MulMod.Program

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Four little-endian 64-bit limbs packed as one 256-bit EVM word. -/
def mulModReduceWord (w0 w1 w2 w3 : Word) : EvmWord :=
  EvmWord.fromLimbs fun i =>
    match i with
    | 0 => w0
    | 1 => w1
    | 2 => w2
    | 3 => w3

/-- Remainder accumulator word stored at `sp - 32 .. sp - 8`. -/
def mulModReduceRemWord (r0 r1 r2 r3 : Word) : EvmWord :=
  mulModReduceWord r0 r1 r2 r3

/-- Modulus word stored in the caller-visible modulus slot `sp + 64 .. sp + 88`. -/
def mulModReduceModWord (n0 n1 n2 n3 : Word) : EvmWord :=
  mulModReduceWord n0 n1 n2 n3

/-- The input bit consumed from the current product limb `x17`. -/
def mulModReduceInputBit (x17 : Word) : Bool :=
  x17.getLsbD 63

/-- Convert a reducer input bit to the 256-bit value inserted into bit zero. -/
def mulModReduceBitWord (bit : Bool) : EvmWord :=
  if bit then (1 : EvmWord) else 0

/-- Shift the current remainder left by one and insert the consumed product bit. -/
@[irreducible] def mulModReduceShiftInBit (r : EvmWord) (bit : Bool) : EvmWord :=
  (r <<< 1) ||| mulModReduceBitWord bit

/-- One semantic step of the bit-serial reducer. -/
@[irreducible] def mulModReduceStep (r n : EvmWord) (bit : Bool) : EvmWord :=
  let shifted := mulModReduceShiftInBit r bit
  if shifted.toNat < n.toNat then shifted else shifted - n

@[simp] theorem mulModReduceWord_getLimbN_zero (w0 w1 w2 w3 : Word) :
    (mulModReduceWord w0 w1 w2 w3).getLimbN 0 = w0 := by
  simp [mulModReduceWord, EvmWord.getLimbN_fromLimbs_gen_0]

@[simp] theorem mulModReduceWord_getLimbN_one (w0 w1 w2 w3 : Word) :
    (mulModReduceWord w0 w1 w2 w3).getLimbN 1 = w1 := by
  simp [mulModReduceWord, EvmWord.getLimbN_fromLimbs_gen_1]

@[simp] theorem mulModReduceWord_getLimbN_two (w0 w1 w2 w3 : Word) :
    (mulModReduceWord w0 w1 w2 w3).getLimbN 2 = w2 := by
  simp [mulModReduceWord, EvmWord.getLimbN_fromLimbs_gen_2]

@[simp] theorem mulModReduceWord_getLimbN_three (w0 w1 w2 w3 : Word) :
    (mulModReduceWord w0 w1 w2 w3).getLimbN 3 = w3 := by
  simp [mulModReduceWord, EvmWord.getLimbN_fromLimbs_gen_3]

@[simp] theorem mulModReduceRemWord_getLimbN_zero (r0 r1 r2 r3 : Word) :
    (mulModReduceRemWord r0 r1 r2 r3).getLimbN 0 = r0 := by
  simp [mulModReduceRemWord]

@[simp] theorem mulModReduceRemWord_getLimbN_one (r0 r1 r2 r3 : Word) :
    (mulModReduceRemWord r0 r1 r2 r3).getLimbN 1 = r1 := by
  simp [mulModReduceRemWord]

@[simp] theorem mulModReduceRemWord_getLimbN_two (r0 r1 r2 r3 : Word) :
    (mulModReduceRemWord r0 r1 r2 r3).getLimbN 2 = r2 := by
  simp [mulModReduceRemWord]

@[simp] theorem mulModReduceRemWord_getLimbN_three (r0 r1 r2 r3 : Word) :
    (mulModReduceRemWord r0 r1 r2 r3).getLimbN 3 = r3 := by
  simp [mulModReduceRemWord]

@[simp] theorem mulModReduceModWord_getLimbN_zero (n0 n1 n2 n3 : Word) :
    (mulModReduceModWord n0 n1 n2 n3).getLimbN 0 = n0 := by
  simp [mulModReduceModWord]

@[simp] theorem mulModReduceModWord_getLimbN_one (n0 n1 n2 n3 : Word) :
    (mulModReduceModWord n0 n1 n2 n3).getLimbN 1 = n1 := by
  simp [mulModReduceModWord]

@[simp] theorem mulModReduceModWord_getLimbN_two (n0 n1 n2 n3 : Word) :
    (mulModReduceModWord n0 n1 n2 n3).getLimbN 2 = n2 := by
  simp [mulModReduceModWord]

@[simp] theorem mulModReduceModWord_getLimbN_three (n0 n1 n2 n3 : Word) :
    (mulModReduceModWord n0 n1 n2 n3).getLimbN 3 = n3 := by
  simp [mulModReduceModWord]

@[simp] theorem mulModReduceBitWord_false :
    mulModReduceBitWord false = (0 : EvmWord) := by
  rfl

@[simp] theorem mulModReduceBitWord_true :
    mulModReduceBitWord true = (1 : EvmWord) := by
  rfl

/-- Iterate the bit-serial reducer step over the top `k` bits of the product
    word `w`: each step consumes `w`'s most significant bit and shifts `w` left
    by one. After 64 steps the limb `w` is fully folded into the remainder. -/
def mulModReduceStepN (r n : EvmWord) (w : Word) : Nat → EvmWord
  | 0 => r
  | k + 1 =>
    mulModReduceStepN (mulModReduceStep r n (mulModReduceInputBit w)) n (w <<< 1) k

@[simp] theorem mulModReduceStepN_zero (r n : EvmWord) (w : Word) :
    mulModReduceStepN r n w 0 = r := rfl

theorem mulModReduceStepN_succ (r n : EvmWord) (w : Word) (k : Nat) :
    mulModReduceStepN r n w (k + 1) =
      mulModReduceStepN (mulModReduceStep r n (mulModReduceInputBit w)) n (w <<< 1) k :=
  rfl

/-- The bit-loop counter (`x15`) after the loop's `ADDI x15, x15, -1`: starting
    from `m` remaining iterations it becomes `m - 1`. -/
theorem mulModReduceBitCounter_decr (m : Nat) (h1 : 1 ≤ m) (h64 : m ≤ 64) :
    BitVec.ofNat 64 m + signExtend12 (4095 : BitVec 12) = BitVec.ofNat 64 (m - 1) := by
  have hse : signExtend12 (4095 : BitVec 12) = (-1 : BitVec 64) := by decide
  rw [hse]; bv_omega

/-- The decremented bit-loop counter is zero exactly when one iteration
    remained. -/
theorem mulModReduceBitCounter_eq_zero_iff (m : Nat) (h1 : 1 ≤ m) (h64 : m ≤ 64) :
    (BitVec.ofNat 64 m + signExtend12 (4095 : BitVec 12) = 0) ↔ m = 1 := by
  have hse : signExtend12 (4095 : BitVec 12) = (-1 : BitVec 64) := by decide
  rw [hse]
  constructor
  · intro h; bv_omega
  · intro h; subst h; decide

/-- Iterate the per-limb 64-bit reduction over `m` product limbs (highest limb
    first), reading the limb sequence `limb` (`limb 0` is the limb processed
    next). After all eight product limbs the 512-bit product is fully folded
    into the remainder, leaving the reduced result. -/
def mulModReduceOuterFold (n : EvmWord) (limb : Nat → Word) (r : EvmWord) : Nat → EvmWord
  | 0 => r
  | m + 1 =>
    mulModReduceOuterFold n (fun i => limb (i + 1))
      (mulModReduceStepN r n (limb 0) 64) m

@[simp] theorem mulModReduceOuterFold_zero (n : EvmWord) (limb : Nat → Word) (r : EvmWord) :
    mulModReduceOuterFold n limb r 0 = r := rfl

theorem mulModReduceOuterFold_succ (n : EvmWord) (limb : Nat → Word) (r : EvmWord) (m : Nat) :
    mulModReduceOuterFold n limb r (m + 1) =
      mulModReduceOuterFold n (fun i => limb (i + 1))
        (mulModReduceStepN r n (limb 0) 64) m :=
  rfl

end EvmAsm.Evm64
