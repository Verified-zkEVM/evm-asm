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
import EvmAsm.Evm64.EvmWordArith.Div
import EvmAsm.Evm64.EvmWordArith.DivLimbBridge

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

end EvmAsm.Evm64
