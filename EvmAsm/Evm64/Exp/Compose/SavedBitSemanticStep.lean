/-
  EvmAsm.Evm64.Exp.Compose.SavedBitSemanticStep

  Glue between the EXP loop body's structural per-iteration result definitions
  (`expTwoMulSquareW`, `expTwoMulIterRw`) and the pure semantic
  square-and-multiply step `EvmWord.expSqMulStep`.

  The skip path squares the accumulator (`acc * acc`); the cond-mul path
  squares then multiplies by the base (`acc * acc * base`).  Both are exactly
  one `expSqMulStep` on the accumulator word, modulo commutativity of EvmWord
  multiplication.  These lemmas are the connective tissue for threading the
  semantic accumulator invariant `acc = EvmWord.exp base prefix` through the
  256-iteration loop induction.

  Bead evm-asm-6snn.4.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBaseDefs
import EvmAsm.Evm64.EvmWordArith.Exp

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64.EvmWord

/-- The loop body's squaring result `expTwoMulSquareW` (the skip path: `acc²`)
    is the `bit = false` square-and-multiply step on the accumulator word
    `expResultWord r0 r1 r2 r3`. The base argument is irrelevant on this path. -/
theorem expTwoMulSquareW_eq_expSqMulStep_false
    (r0 r1 r2 r3 : Word) (base : EvmWord) :
    expTwoMulSquareW r0 r1 r2 r3 =
      expSqMulStep base (expResultWord r0 r1 r2 r3) false := by
  unfold expTwoMulSquareW expTwoMulIterW expSqMulStep
  rfl

/-- The loop body's cond-mul result `expTwoMulIterRw` (the cond path:
    `acc² · base`) is the `bit = true` square-and-multiply step on the
    accumulator word `expResultWord r0 r1 r2 r3` with base
    `expResultWord a0 a1 a2 a3` (modulo commutativity). -/
theorem expTwoMulIterRw_eq_expSqMulStep_true
    (r0 r1 r2 r3 a0 a1 a2 a3 : Word) :
    expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3 =
      expSqMulStep (expResultWord a0 a1 a2 a3)
        (expResultWord r0 r1 r2 r3) true := by
  unfold expTwoMulIterRw expTwoMulSquareW expTwoMulIterW expTwoMulIterAw
    expSqMulStep
  simp only [if_true]
  rw [BitVec.mul_comm]

/-- Per-iteration accumulator value preservation, skip path.

    If the input accumulator limb-word equals `exp base e`, the loop body's
    squaring result `expTwoMulSquareW` equals `exp base e'` for the doubled
    prefix `e'` with `e'.toNat = 2 * e.toNat`. -/
theorem expTwoMulSquareW_exp (base : EvmWord) (r0 r1 r2 r3 : Word) (e e' : EvmWord)
    (hacc : expResultWord r0 r1 r2 r3 = exp base e)
    (hnext : e'.toNat = 2 * e.toNat) :
    expTwoMulSquareW r0 r1 r2 r3 = exp base e' := by
  unfold expTwoMulSquareW expTwoMulIterW
  rw [hacc]
  exact (exp_double_right_of_toNat_eq base e e' hnext).symm

/-- Per-iteration accumulator value preservation, cond-mul path.

    If the input accumulator limb-word equals `exp base e` and the base
    limb-word equals `base`, the loop body's cond-mul result `expTwoMulIterRw`
    equals `exp base e'` for the doubled-plus-one prefix `e'` with
    `e'.toNat = 2 * e.toNat + 1`. -/
theorem expTwoMulIterRw_exp (base : EvmWord) (r0 r1 r2 r3 a0 a1 a2 a3 : Word)
    (e e' : EvmWord)
    (hacc : expResultWord r0 r1 r2 r3 = exp base e)
    (hbase : expResultWord a0 a1 a2 a3 = base)
    (hnext : e'.toNat = 2 * e.toNat + 1) :
    expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3 = exp base e' := by
  unfold expTwoMulIterRw expTwoMulSquareW expTwoMulIterW expTwoMulIterAw
  rw [hacc, hbase, BitVec.mul_comm]
  exact (exp_double_add_one_right_of_toNat_eq base e e' hnext).symm

end EvmAsm.Evm64.Exp.Compose
