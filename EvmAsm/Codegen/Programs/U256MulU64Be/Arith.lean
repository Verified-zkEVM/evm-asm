/-
  EvmAsm.Codegen.Programs.U256MulU64Be.Arith

  **Numeric meaning of `u256_mul_u64_be`'s accumulator** (#12225).

  `mulWhole_spec` states its post operationally, as
  `copyState (mulState aBytes b 32) outBytes 32`. This module is where that fold
  gets tied to `Nat` multiplication; it currently holds the load-bearing
  INVARIANT that the fold's correctness rests on, which was previously implicit
  in the code.

  ## ⚠️ The apparent overflow in `mulOuterStep`, and why it is not one

  Each outer step folds one input byte:

      m  := byte.toNat * b.toNat            -- ≤ 255 · (2^64 − 1)
      r  := rippleState acc (m % 2^64) i 8
      hi := m / 2^64 + mulCarry acc lo i 8 + (r.getD (i+8) 0).toNat
      r.set (i+8) (BitVec.ofNat 8 hi)       -- ONE byte, truncating

  `m / 2^64` alone reaches 254, so if slot `i+8` already held a partial sum the
  `BitVec.ofNat 8` would silently drop a carry — and nothing propagates it
  further. The write is sound only because **slot `i+8` is still zero when step
  `i` runs**: step `k` writes indices `k … k+8`, so after steps `0 … i−1` the
  highest index touched is `(i−1)+8 = i+7`, and the accumulator starts as 40 zero
  bytes.

  `mulState_getD_high` below is that invariant. It is the fact a numeric proof of
  the fold has to establish first, and it is worth having stated even before the
  numeric tie lands, because the single-byte `hi` write looks wrong without it.
-/
import EvmAsm.Codegen.Programs.U256MulU64Be.WholeModel

namespace EvmAsm.Codegen.U256MulU64Be

open EvmAsm.Rv64

/-- Value of the little-endian-indexed accumulator. The operands are big-endian
    but `mulState` indexes its 40-byte accumulator from the low end, so this is
    the reader a numeric characterisation needs. -/
def accValue (xs : List (BitVec 8)) : Nat :=
  (List.range xs.length).foldl (fun acc i => acc + (xs.getD i 0).toNat * 256 ^ i) 0

/-- The inner ripple touches only indices `i … i + k − 1`: anything at or above
    `i + k` is untouched. -/
theorem rippleState_getD_high (accE : List (BitVec 8)) (M0 i : Nat) :
    ∀ (k j : Nat), i + k ≤ j →
      (rippleState accE M0 i k).getD j 0 = accE.getD j 0 := by
  intro k
  induction k with
  | zero => intro j _; rfl
  | succ k ih =>
    intro j hj
    rw [rippleState_succ, List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
      ← List.getD_eq_getElem?_getD]
    exact ih j (by omega)

/-- **The invariant the truncating `hi` write rests on**: after folding `i` input
    bytes, every accumulator slot at index `i + 8` or above is still zero.

    Consequence (and the reason this matters): at step `i` the term
    `(r.getD (i+8) 0).toNat` in `mulOuterStep` is `0`, so
    `hi ≤ 254 + carry < 256` and `BitVec.ofNat 8 hi` loses nothing. Without this,
    the model would drop carries at every outer step. -/
theorem mulState_getD_high (a : List (BitVec 8)) (b : Word) :
    ∀ (i j : Nat), i + 8 ≤ j → (mulState a b i).getD j 0 = 0 := by
  intro i
  induction i with
  | zero =>
    intro j _
    show (List.replicate 40 (0 : BitVec 8)).getD j 0 = 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    rcases Nat.lt_or_ge j 40 with h | h
    · simp [h]
    · simp [Nat.not_lt.mpr h]
  | succ i ih =>
    intro j hj
    show (mulOuterStep a b (mulState a b i) i).getD j 0 = 0
    unfold mulOuterStep
    dsimp only
    split
    · exact ih j (by omega)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
        ← List.getD_eq_getElem?_getD]
      rw [rippleState_getD_high _ _ _ 8 j (by omega)]
      exact ih j (by omega)

/-! ### Non-vacuity: the fold really does compute the product

    The invariant above says the truncation is lossless; these check that the
    conclusion it protects actually holds, INCLUDING at the maximal input where a
    dropped carry would show up. `0xff…ff × 0xffffffffffffffff` is the case that
    exercises every outer step's `hi` at its largest. -/

private def mulTestA : List (BitVec 8) := List.replicate 30 (0 : BitVec 8) ++ [1, 2]
private def mulTestMax : List (BitVec 8) := List.replicate 32 (0xff : BitVec 8)

-- a = 258 (big-endian 0x…0102).
#guard accValue (mulState mulTestA 0xffffffffffffffff 32) == 258 * 0xffffffffffffffff

-- The maximal case: every outer step's `hi` is at its largest here.
#guard accValue (mulState mulTestMax 0xffffffffffffffff 32) == (2 ^ 256 - 1) * (2 ^ 64 - 1)

-- b = 0 and b = 1 boundaries.
#guard accValue (mulState mulTestMax 0 32) == 0
#guard accValue (mulState mulTestMax 1 32) == 2 ^ 256 - 1

-- The invariant itself, concretely: slot 8 is zero after one folded byte, and
-- slots below can be non-zero — so it is a real restriction, not vacuous.
#guard (mulState mulTestMax 1 1).getD 8 0 == 0
#guard (mulState mulTestMax 1 1).getD 0 0 != 0

end EvmAsm.Codegen.U256MulU64Be
