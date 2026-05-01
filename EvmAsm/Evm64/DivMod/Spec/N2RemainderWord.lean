/-
  EvmAsm.Evm64.DivMod.Spec.N2RemainderWord

  Remainder-word helper for the n=2 MOD path. Mirrors the n=1 helper bundle
  in `Spec.Dispatcher` (`fullModN1RemainderWord` and friends) and the n=2
  quotient-word bundle in `Spec.N2QuotientWord` (`fullDivN2QuotientWord` and
  friends): packages the four per-limb denormalized remainder limbs from
  `fullDivN2R0` into a single `EvmWord`, and provides the standard
  structural lemmas (per-limb extraction, `BitVec.eq_of_toNat_eq` bridge,
  `toNat`-as-`val256`, and a `val256`-equality bridge to `EvmWord.mod`).

  The four remainder limbs come from denormalizing the final un-values
  `r0.2.1 .. r0.2.2.2.2.1` (which are u0..u3 at the end of the j=0
  iteration) by `fullDivN2Shift b1`. Concretely:

      u0' = (u0 >>> shift) ||| (u1 <<< antiShift)
      u1' = (u1 >>> shift) ||| (u2 <<< antiShift)
      u2' = (u2 >>> shift) ||| (u3 <<< antiShift)
      u3' = u3 >>> shift

  These will be consumed by a follow-up slice that introduces
  `evm_mod_n2_stack_spec_within_word`, mirroring
  `evm_mod_n1_stack_spec_within_word`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

  See beads `evm-asm-0j4w`, parent `evm-asm-kxrl` (#61 slice 2c).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Base

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Pack the four per-limb denormalized MOD remainders from the n=2 path
    into a single `EvmWord`. -/
@[irreducible]
def fullModN2RemainderWord (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 =>
        (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
    | 1 =>
        (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
    | 2 =>
        (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
    | 3 =>
        ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN2Shift b1).toNat % 64)))

/-- If `fullModN2RemainderWord ... = EvmWord.mod a b`, then each limb of
    `EvmWord.mod a b` matches the corresponding denormalized expression. -/
theorem fullModN2_hmods_of_word_eq
    (bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hmod : fullModN2RemainderWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN2Shift b1).toNat % 64)) |||
        ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN2Shift b1).toNat % 64)) |||
        ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN2Shift b1).toNat % 64)) |||
        ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN2Shift b1).toNat % 64)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmod]
    delta fullModN2RemainderWord
    exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hmod]
    delta fullModN2RemainderWord
    exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hmod]
    delta fullModN2RemainderWord
    exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hmod]
    delta fullModN2RemainderWord
    exact EvmWord.getLimbN_fromLimbs_3

/-- BitVec extensionality bridge: a `toNat` equality lifts to an `EvmWord`
    equality. -/
theorem fullModN2RemainderWord_eq_mod_of_toNat_eq
    (bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hmod_toNat :
      (fullModN2RemainderWord bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).toNat = (EvmWord.mod a b).toNat) :
    fullModN2RemainderWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b :=
  BitVec.eq_of_toNat_eq hmod_toNat

/-- The `toNat` of the packed remainder word equals the four-limb
    `EvmWord.val256` of the denormalized remainder limbs. -/
theorem fullModN2RemainderWord_toNat
    (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullModN2RemainderWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3).toNat =
    EvmWord.val256
      (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN2Shift b1).toNat % 64)) |||
        ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
      (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN2Shift b1).toNat % 64)) |||
        ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
      (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN2Shift b1).toNat % 64)) |||
        ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
      ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN2Shift b1).toNat % 64)) := by
  delta fullModN2RemainderWord
  rw [EvmWord.fromLimbs_toNat]
  rfl

/-- `val256`-equality bridge: if the `EvmWord.val256` of the four
    denormalized remainder limbs equals `a.toNat % b.toNat` (computed via
    `EvmWord.val256` of the inputs), then the `toNat` of the remainder word
    equals `(EvmWord.mod a b).toNat`. Mirrors
    `fullModN1RemainderWord_toNat_eq_mod_toNat_of_val256_eq`. -/
theorem fullModN2RemainderWord_toNat_eq_mod_toNat_of_val256_eq
    (bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hrem :
      EvmWord.val256
        (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
        (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
        (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
        ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN2Shift b1).toNat % 64)) =
      EvmWord.val256 a0 a1 a2 a3 % EvmWord.val256 b0 b1 b2 b3) :
    (fullModN2RemainderWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3).toNat = (EvmWord.mod a b).toNat := by
  have ha_val : EvmWord.val256 a0 a1 a2 a3 = a.toNat := by
    rw [← ha0, ← ha1, ← ha2, ← ha3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : EvmWord.val256 b0 b1 b2 b3 = b.toNat := by
    rw [← hb0, ← hb1, ← hb2, ← hb3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  have hb_pos : 0 < b.toNat := by
    rw [← hb_val]
    exact EvmWord.val256_pos_of_or_ne_zero hbnz
  have hb_ne : b ≠ 0 := by
    intro hb_zero
    have hb_toNat_zero : b.toNat = 0 := by simp [hb_zero]
    omega
  have hmod_toNat : (EvmWord.mod a b).toNat = a.toNat % b.toNat := by
    unfold EvmWord.mod
    rw [if_neg hb_ne]
    exact BitVec.toNat_umod
  rw [fullModN2RemainderWord_toNat, hrem, ha_val, hb_val, hmod_toNat]

end EvmAsm.Evm64
