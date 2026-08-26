/-
  EvmAsm.Evm64.DivMod.Spec.N3QuotientWord

  Quotient-word helper for the n=3 DIV path. Mirrors `Spec.N2QuotientWord`
  for n=3: packages the two non-zero per-limb results from
  `fullDivN3R{0,1}` (with `q2 = q3 = 0` because n=3 means `b3 = 0 ∧ b2 ≠ 0`,
  so `a / b < 2^128`) into a single `EvmWord`, and provides the standard
  structural lemmas (per-limb extraction, `BitVec.eq_of_toNat_eq` bridge,
  `toNat`-as-`val256`, and a `val256`-equality bridge to `EvmWord.div`).

  Consumed by `evm_div_n3_stack_spec_within_word` (mirror of
  `evm_div_n2_stack_spec_within_word`).

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

  See beads `evm-asm-pwvj`, parent `evm-asm-pb40` (#61).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified
public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4
public import EvmAsm.Evm64.EvmWordArith.DivAccumulate

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

/-- Pack the four per-limb DIV results from the n=3 path into a single
    `EvmWord`. The top two limbs are `0` because n=3 means `b3 = 0` with
    `b2 ≠ 0`, so the quotient cannot exceed 128 bits. -/
@[irreducible]
def fullDivN3QuotientWord (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 => (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 1 => (fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 2 => (0 : Word)
    | 3 => (0 : Word))

/-- If `fullDivN3QuotientWord ... = EvmWord.div a b`, then each limb of
    `EvmWord.div a b` matches the corresponding `fullDivN3R{0,1}` result
    (and limbs 2, 3 are zero). -/
theorem fullDivN3_hdivs_of_word_eq
    (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hdiv : fullDivN3QuotientWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hdiv]
    delta fullDivN3QuotientWord
    exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hdiv]
    delta fullDivN3QuotientWord
    exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hdiv]
    delta fullDivN3QuotientWord
    exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hdiv]
    delta fullDivN3QuotientWord
    exact EvmWord.getLimbN_fromLimbs_3

/-- Semantic bridge for the n=3 quotient word once the loop proof supplies the
    accumulated mulsub equation and quotient-overestimate bound. -/
theorem fullDivN3QuotientWord_eq_div_of_mulsub_overestimate
    (bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      val256 a0 a1 a2 a3 =
        (((fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^64 +
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          val256 b0 b1 b2 b3 +
        val256
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
        ((fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^64 +
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN3QuotientWord bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  let q0 := (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
  let q1 := (fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
  let r0 := (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
  let r1 := (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
  let r2 := (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
  let r3 := (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
  have h_correct := div_correct_n3_no_shift
    (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3)
    (q0 := q0) (q1 := q1) (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
    hbnz (by simpa [q0, q1, r0, r1, r2, r3] using hmulsub)
    (by simpa [q0, q1] using hge)
  delta fullDivN3QuotientWord
  change
    EvmWord.fromLimbs (fun i : Fin 4 =>
      match i with | 0 => q0 | 1 => q1 | 2 => (0 : Word) | 3 => (0 : Word)) =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)
  exact h_correct.1

/-- Pack the four per-limb DIV results from the n=3 v4 call/max path into a
    single `EvmWord`. The top two limbs are `0`, matching the n=3 range. -/
@[irreducible]
def fullDivN3QuotientWordV4 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 => (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 1 => (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 2 => (0 : Word)
    | 3 => (0 : Word))

/-- If `fullDivN3QuotientWordV4 ... = EvmWord.div a b`, then each limb of
    `EvmWord.div a b` matches the corresponding v4 `fullDivN3R{0,1}` result
    (and limbs 2, 3 are zero). -/
theorem fullDivN3V4_hdivs_of_word_eq
    (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hdiv : fullDivN3QuotientWordV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hdiv]
    delta fullDivN3QuotientWordV4
    exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hdiv]
    delta fullDivN3QuotientWordV4
    exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hdiv]
    delta fullDivN3QuotientWordV4
    exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hdiv]
    delta fullDivN3QuotientWordV4
    exact EvmWord.getLimbN_fromLimbs_3

/-- Semantic bridge for the n=3 v4 quotient word once the loop proof supplies
    the accumulated mulsub equation and quotient-overestimate bound. -/
theorem fullDivN3QuotientWordV4_eq_div_of_mulsub_overestimate
    (bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      val256 a0 a1 a2 a3 =
        (((fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^64 +
          ((fullDivN3R0V4 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          val256 b0 b1 b2 b3 +
        val256
          ((fullDivN3R0V4 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN3R0V4 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN3R0V4 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN3R0V4 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
        ((fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^64 +
          ((fullDivN3R0V4 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN3QuotientWordV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  let q0 := (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
  let q1 := (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
  let r0 := (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
  let r1 := (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
  let r2 := (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
  let r3 := (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
  have h_correct := div_correct_n3_no_shift
    (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3)
    (q0 := q0) (q1 := q1) (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
    hbnz (by simpa [q0, q1, r0, r1, r2, r3] using hmulsub)
    (by simpa [q0, q1] using hge)
  delta fullDivN3QuotientWordV4
  change
    EvmWord.fromLimbs (fun i : Fin 4 =>
      match i with | 0 => q0 | 1 => q1 | 2 => (0 : Word) | 3 => (0 : Word)) =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)
  exact h_correct.1

/-- Four-limb n=3 v4 division witness from the accumulated mulsub equation and
    quotient-overestimate hypothesis. -/
theorem fullDivN3V4_getLimbN_of_mulsub_overestimate
    (bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      val256 a0 a1 a2 a3 =
        (((fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^64 +
          ((fullDivN3R0V4 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          val256 b0 b1 b2 b3 +
        val256
          ((fullDivN3R0V4 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN3R0V4 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN3R0V4 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN3R0V4 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
        ((fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^64 +
          ((fullDivN3R0V4 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    let a := EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  intro a b
  have hdiv :=
    fullDivN3QuotientWordV4_eq_div_of_mulsub_overestimate
      bltu_1 bltu_0 hbnz hmulsub hge
  exact fullDivN3V4_hdivs_of_word_eq bltu_1 bltu_0
    a b a0 a1 a2 a3 b0 b1 b2 b3 hdiv

end EvmAsm.Evm64
