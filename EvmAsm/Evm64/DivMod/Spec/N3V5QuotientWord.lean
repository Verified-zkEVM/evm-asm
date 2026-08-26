/-
  EvmAsm.Evm64.DivMod.Spec.N3V5QuotientWord

  N3 V5 quotient word: packs the two v5 n=3 digit results
  (`fullDivN3R0V5`, `fullDivN3R1V5`) into an `EvmWord` (limbs 2,3 zero), plus the
  `_hdivs_of_word_eq` projector deriving the per-limb `EvmWord.div a b` facts from
  the word equality.  N=3 analog of `fullDivN3QuotientWordV4` /
  `fullDivN2QuotientWordV5`.  Foundational for the v5 n=3 DIV lane's post bridge.
  Bead `evm-asm-wbc4i.9.3`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5Families
public import EvmAsm.Evm64.EvmWordArith.DivLimbBridge

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v5 n=3 quotient, packed into an `EvmWord`: limb 0 = digit-0 result,
    limb 1 = digit-1 result, limbs 2,3 = 0. -/
def fullDivN3QuotientWordV5 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 => (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 1 => (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 2 => (0 : Word)
    | 3 => (0 : Word))

/-- If `fullDivN3QuotientWordV5 ... = EvmWord.div a b`, then each limb of
    `EvmWord.div a b` matches the corresponding v5 `fullDivN3R{0,1}V5` result
    (and limbs 2, 3 are zero). -/
theorem fullDivN3V5_hdivs_of_word_eq
    (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hdiv : fullDivN3QuotientWordV5 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hdiv]; delta fullDivN3QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hdiv]; delta fullDivN3QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hdiv]; delta fullDivN3QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hdiv]; delta fullDivN3QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
