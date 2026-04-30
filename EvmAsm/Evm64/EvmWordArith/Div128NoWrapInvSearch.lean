/-
  EvmAsm.Evm64.EvmWordArith.Div128NoWrapInvSearch

  ## Purpose

  Numerical decision search (#1337 / `evm-asm-8pb` / `evm-asm-b5n`) testing
  whether `Div128PhaseNoWrapInv` or `Div128AllPhasesNoWrapInv` actually
  holds under runtime `isSkipBorrowN4Call`. Both predicates were previously
  introduced as **conditional** hypotheses on KB-6c/d (`Div128FinalAssembly`)
  because the strict closed predecessor `D5` (skip-borrow ⟹
  `Div128PhaseNoWrapInv`) was shown FALSE by `Div128NoWrapDischarge`
  with the counterexample `a3 = 2^64-2, b3 = 1, b2 = 2^64-2`.

  This file replays that classical counterexample at the
  `Div128PhaseNoWrapInv` / `Div128AllPhasesNoWrapInv` granularity and
  pins down the result with `native_decide`. The findings are then used
  to decide which of the two strategies for closing #1337 to pursue:
    (a) bridge-and-discharge: `isSkipBorrowN4Call ⟹
        Div128(All)PhasesNoWrapInv` (only viable if the invariant holds
        under skip-borrow, i.e. the counterexample fails skip-borrow); OR
    (b) bypass-the-invariant: derive `div128Quot ≤ q_true + 2` directly
        from `isSkipBorrowN4Call` without going through the bundled
        no-wrap invariant (the only viable path if even one
        skip-borrow-satisfying input violates the invariant).

  Reference: `EvmAsm/Evm64/EvmWordArith/Div128NoWrapDischarge.lean`,
  `Div128CallSkipClose.lean` (no-discharge note around line 660-690),
  and the analogous numerical witnesses in
  `EvmAsm/Evm64/DivMod/SpecCallAddbackBeq/NumericalTests.lean`.

  All theorems below are Prop-level decision facts proved by
  `native_decide`. They are NOT consumed by other proofs; they exist as
  machine-checkable evidence supporting the architectural decision
  recorded on issue #1337.
-/

import EvmAsm.Evm64.EvmWordArith.Div128NoWrapDischarge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Counterexample 1 (D5 classical witness)
--
--   a3 := 2^64 - 2,  a2 = a1 = a0 := 0
--   b3 := 1,         b2 := 2^64 - 2,  b1 = b0 := 0
--
-- Properties verified below:
--   * `isSkipBorrowN4Call` HOLDS on this input (call trial, no addback).
--   * `Div128PhaseNoWrapInv` (with Phase-1 no-wrap conjunct) FAILS — this
--     replays the D5 counterexample at the bundled-predicate granularity.
--   * `Div128AllPhasesNoWrapInv` therefore also FAILS (it is strictly
--     stronger; the projection lemma `toPhaseNoWrapInv` would otherwise
--     give a contradiction).
--
-- Implication: the bridge `isSkipBorrowN4Call ⟹
-- Div128(All)PhasesNoWrapInv` is unprovable in general. KB-6c/d cannot
-- be discharged by such a bridge; closing #1337 unconditionally requires
-- the bypass strategy (b).
-- ============================================================================

private def ce1_a0 : Word := 0
private def ce1_a1 : Word := 0
private def ce1_a2 : Word := 0
private def ce1_a3 : Word := BitVec.ofNat 64 (2^64 - 2)
private def ce1_b0 : Word := 0
private def ce1_b1 : Word := 0
private def ce1_b2 : Word := BitVec.ofNat 64 (2^64 - 2)
private def ce1_b3 : Word := 1

-- Reconstruct the CLZ-normalized `(uHi, uLo, vTop)` triple consumed by
-- `Div128(All)PhasesNoWrapInv`. The shape mirrors the let-bindings inside
-- `isSkipBorrowN4Call` so the same shifted limbs feed both predicates.
private def ce1_shift : Nat := (clzResult ce1_b3).1.toNat % 64
private def ce1_antiShift : Nat :=
  (signExtend12 (0 : BitVec 12) - (clzResult ce1_b3).1).toNat % 64

private def ce1_u4 : Word := ce1_a3 >>> ce1_antiShift
private def ce1_u3 : Word :=
  (ce1_a3 <<< ce1_shift) ||| (ce1_a2 >>> ce1_antiShift)
private def ce1_b3' : Word :=
  (ce1_b3 <<< ce1_shift) ||| (ce1_b2 >>> ce1_antiShift)

/-- Skip-borrow holds on counterexample 1. -/
theorem ce1_isSkipBorrowN4Call_holds :
    isSkipBorrowN4Call ce1_a0 ce1_a1 ce1_a2 ce1_a3
                        ce1_b0 ce1_b1 ce1_b2 ce1_b3 := by
  unfold isSkipBorrowN4Call ce1_a0 ce1_a1 ce1_a2 ce1_a3
         ce1_b0 ce1_b1 ce1_b2 ce1_b3
  native_decide

/-- `Div128PhaseNoWrapInv` FAILS on counterexample 1's normalized triple
    `(u4, u3, b3')`, despite skip-borrow holding. This is the D5
    counterexample replayed at the bundled-predicate level. -/
theorem ce1_Div128PhaseNoWrapInv_fails :
    ¬ Div128PhaseNoWrapInv ce1_u4 ce1_u3 ce1_b3' := by
  unfold Div128PhaseNoWrapInv ce1_u4 ce1_u3 ce1_b3'
         ce1_shift ce1_antiShift ce1_a2 ce1_a3 ce1_b2 ce1_b3
  native_decide

/-- `Div128AllPhasesNoWrapInv` is strictly stronger and therefore also
    fails on counterexample 1. -/
theorem ce1_Div128AllPhasesNoWrapInv_fails :
    ¬ Div128AllPhasesNoWrapInv ce1_u4 ce1_u3 ce1_b3' := by
  intro h
  exact ce1_Div128PhaseNoWrapInv_fails h.toPhaseNoWrapInv

-- ============================================================================
-- Cross-check: the `div128Quot_v1` Knuth-B counterexample
--
--   a3 := 2^63 + 2^33,  a0 = a1 = a2 := 0
--   b3 := 1,            b2 := 2^33 - 1,  b0 = b1 := 0
--
-- This is the input motivating the v2 fix of `div128Quot` (witnessed in
-- `EvmAsm/Evm64/DivMod/SpecCallAddbackBeq/NumericalTests.lean`). It
-- DOES NOT satisfy `isSkipBorrowN4Call` — addback fires here — so it is
-- only relevant to the addback branch, not to the skip-borrow side of
-- the discharge bridge. We pin that property here as evidence (not a
-- counterexample for KB-6/skip-borrow).
-- ============================================================================

private def cev1_a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
private def cev1_b2 : Word := BitVec.ofNat 64 (2^33 - 1)
private def cev1_b3 : Word := 1

/-- The `div128Quot_v1` Knuth-B violation input does NOT satisfy
    skip-borrow — it lands in the addback branch. -/
theorem cev1_isSkipBorrowN4Call_fails :
    ¬ isSkipBorrowN4Call 0 0 0 cev1_a3 0 0 cev1_b2 cev1_b3 := by
  unfold isSkipBorrowN4Call cev1_a3 cev1_b2 cev1_b3
  native_decide

-- ============================================================================
-- DECISION (recorded on #1337 / evm-asm-8pb)
--
-- One skip-borrow-satisfying input (`ce1`) falsifies
-- `Div128PhaseNoWrapInv` (and therefore `Div128AllPhasesNoWrapInv`).
-- The bridge "skip-borrow ⟹ Div128(All)PhasesNoWrapInv" is therefore
-- UNPROVABLE.
--
-- Path forward for closing #1337 unconditionally:
--   * Pursue strategy (b): derive `div128Quot ≤ q_true + 2` directly
--     from `isSkipBorrowN4Call` without routing through the bundled
--     no-wrap invariants (Knuth Theorem B applied directly on the
--     skip-borrow algebra).
--   * Drop the conditional `Div128(All)PhasesNoWrapInv` hypothesis on
--     KB-6c/d once the direct derivation lands.
--
-- See `Div128NoWrapDischarge.lean` (lines 56–61, 830–844) for the
-- earlier D5 removal note and `Div128CallSkipClose.lean` (lines 660–690)
-- for the still-conditional KB-6 chain.
-- ============================================================================

end EvmAsm.Evm64
