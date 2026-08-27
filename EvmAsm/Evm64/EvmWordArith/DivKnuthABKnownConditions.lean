/-
  EvmAsm.Evm64.EvmWordArith.DivKnuthABKnownConditions

  Named bundles for the substantive arithmetic frontiers gating
  `evm_div_stack_spec_unconditional`:

    * `DivKnuthABKnownConditions` — concrete normalisation + call-regime
      side-conditions under which `DivKTrialCallV4QHatLeFloorPlusOne`
      and `Knuth128_64TopWindowLeVal256DivPlusOne` are expected to hold.

  This is a structural target: downstream beads can attack the
  predicate `DivKnuthABKnownConditions → DivKTrialCallV4QHatLeFloorPlusOne`
  (and the Knuth-A analog) as a single named target rather than chasing
  the discharge case-by-case.

  The conditions track the bead `7.1.4.1` description:
    > under uHi < vTop and normalisation conditions, by case-splitting on
    > un21 < vTop and using the v4 Phase-2 2-correction exactness in the
    > corner cases.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivV4TrialVal256Composition

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Bundle of call-regime + normalisation side-conditions on `(uHi, uLo, vTop)`
    expected to discharge the Knuth-A v4 +1 trial bound. -/
structure DivKnuthABKnownConditions (uHi uLo vTop : Word) : Prop where
  /-- The dividend top window is strictly smaller than the divisor top —
      the call regime that guarantees the 128/64 quotient fits in 64 bits. -/
  hCallRegime : uHi.toNat < vTop.toNat
  /-- The divisor top is normalised — its high bit is set. -/
  hVTopNormalised : 2^63 ≤ vTop.toNat

namespace DivKnuthABKnownConditions

/-- Projector for the call-regime condition. -/
theorem callRegime {uHi uLo vTop : Word}
    (h : DivKnuthABKnownConditions uHi uLo vTop) :
    uHi.toNat < vTop.toNat := h.hCallRegime

/-- Projector for the normalisation condition. -/
theorem vTopNormalised {uHi uLo vTop : Word}
    (h : DivKnuthABKnownConditions uHi uLo vTop) :
    2^63 ≤ vTop.toNat := h.hVTopNormalised

end DivKnuthABKnownConditions

end EvmAsm.Evm64
