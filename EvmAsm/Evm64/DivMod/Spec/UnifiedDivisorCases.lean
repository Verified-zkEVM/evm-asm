/-
  EvmAsm.Evm64.DivMod.Spec.UnifiedDivisorCases

  Top-level divisor limb classification for the public unconditional DIV stack
  spec assembly.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivLimbBridge

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Public DIV top-level divisor cases, ordered by the highest nonzero divisor
    limb. Nonzero branches also carry the existing OR-reduced nonzero witness
    consumed by lower-level DivMod stack wrappers. -/
inductive DivisorLimbCase (b : EvmWord) : Prop where
  | bzero (hbz : b = 0)
  | n1 (hbnz : b ≠ 0)
      (hbnzOr : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
      (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
      (hb1z : b.getLimbN 1 = 0) (hb0nz : b.getLimbN 0 ≠ 0)
  | n2 (hbnz : b ≠ 0)
      (hbnzOr : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
      (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
      (hb1nz : b.getLimbN 1 ≠ 0)
  | n3 (hbnz : b ≠ 0)
      (hbnzOr : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
      (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
  | n4 (hbnz : b ≠ 0)
      (hbnzOr : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
      (hb3nz : b.getLimbN 3 ≠ 0)

/-- Split an arbitrary divisor into the branch shape used by the final public
    DIV stack spec. The split is proof-internal: callers get shape facts from
    the returned case rather than taking limb nonzero premises publicly. -/
theorem divisorLimbCase (b : EvmWord) : DivisorLimbCase b := by
  by_cases hbz : b = 0
  · exact DivisorLimbCase.bzero hbz
  · have hbnzOr : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
      (EvmWord.ne_zero_iff_getLimbN_or).mp hbz
    by_cases hb3z : b.getLimbN 3 = 0
    · by_cases hb2z : b.getLimbN 2 = 0
      · by_cases hb1z : b.getLimbN 1 = 0
        · have hb0nz : b.getLimbN 0 ≠ 0 := by
            intro hb0z
            apply hbnzOr
            simp [hb0z, hb1z, hb2z, hb3z]
          exact DivisorLimbCase.n1 hbz hbnzOr hb3z hb2z hb1z hb0nz
        · exact DivisorLimbCase.n2 hbz hbnzOr hb3z hb2z hb1z
      · exact DivisorLimbCase.n3 hbz hbnzOr hb3z hb2z
    · exact DivisorLimbCase.n4 hbz hbnzOr hb3z

end EvmAsm.Evm64
