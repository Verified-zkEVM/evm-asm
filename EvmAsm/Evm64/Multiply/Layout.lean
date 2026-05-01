/-
  EvmAsm.Evm64.Multiply.Layout

  Pilot for the scratchpad-layout abstraction (GH #334, beads evm-asm-1d1o).

  Per `docs/scratchpad-layout-design.md` §3.2, the Multiply routine does NOT
  use `sp + signExtend12 N` internal scratch cells — its `sp + 0/8/.../56`
  inputs and below-sp partials (`sp + 0..24`) are stack slots fixed by the
  EVM calling convention, not configurable internal scratch. Consequently
  the Multiply layout is **empty**: there are no offsets to parameterize.

  This file still defines `MultiplyScratchpadLayout`, `MultiplyScratchpadLayout.Valid`,
  and `canonicalMultiplyScratchpadLayout` so that:

  1. The naming + file convention is established (`Multiply/Layout.lean`,
     `XxxScratchpadLayout`, `XxxScratchpadLayout.Valid`,
     `canonicalXxxScratchpadLayout`, `canonicalXxxScratchpadLayout_valid`).
  2. Slice 4 (DivMod / Byte / Shift, evm-asm-vst1) has a working template
     to copy.
  3. Downstream consumers — including any future caller that wants to
     compose Multiply with another routine that DOES carry an internal
     scratchpad (e.g. EXP via #92) — can already write `(L : MultiplyScratchpadLayout)
     (hL : L.Valid)` parameters in their own preconditions without churn
     once Multiply gains real scratch later.

  No code change to existing Multiply specs in this PR — the layout
  abstraction is purely additive. See §7 of the design doc.
-/

import EvmAsm.Evm64.Multiply.Spec

namespace EvmAsm.Evm64

/-- Layout of the Multiply routine's `sp`-relative internal scratch cells.

    Multiply has none — see file-level doc-comment. The struct is empty
    (one constructor with zero fields) and exists to fix the naming /
    parameter-passing convention shared with `DivModScratchpadLayout`,
    `ByteScratchpadLayout`, etc.

    Note: the `sp + 0..56` cells touched by `evm_mul`'s bytecode are part
    of the EVM stack frame supplied by the caller, not part of the
    routine's internal scratchpad. They are described by the precondition
    of `evm_mul_stack_spec_within` (`evmWordIs sp a ** evmWordIs (sp+32) b`)
    and the postcondition `evmMulStackPost` directly, and remain unaffected
    by any choice of `MultiplyScratchpadLayout`. -/
structure MultiplyScratchpadLayout : Type where
  deriving Repr

/-- Validity bundle for `MultiplyScratchpadLayout`.

    With zero fields the layout has nothing to constrain; `Valid` is
    trivially derivable. Slice 4's `DivModScratchpadLayout.Valid` will
    carry alignment / disjointness / algebraic-relationship obligations
    in this same shape. -/
structure MultiplyScratchpadLayout.Valid (_L : MultiplyScratchpadLayout) : Prop where

/-- The canonical Multiply scratchpad layout.

    Trivial: there is nothing to choose, so canonical = the unique value. -/
def canonicalMultiplyScratchpadLayout : MultiplyScratchpadLayout := {}

/-- The canonical Multiply scratchpad layout is `Valid`. Discharged by
    `decide` once slice 4's analogue carries real obligations. -/
theorem canonicalMultiplyScratchpadLayout_valid :
    canonicalMultiplyScratchpadLayout.Valid := {}

-- ============================================================================
-- Layout-parameterized variant of evm_mul_stack_spec_within
-- ============================================================================

open EvmAsm.Rv64

/-- Layout-parameterized restatement of `evm_mul_stack_spec_within`.

    Identical contract — Multiply's stack pre/post depend only on the
    caller-supplied stack frame, not on any internal scratchpad. The `L`
    and `hL` parameters are placeholders that establish the convention
    shared with `DivModScratchpadLayout`, etc. (slice 4); a future caller
    composing Multiply with a routine that DOES use an internal scratchpad
    can already pass an `L` through without conditioning on whether
    Multiply itself uses it.

    Reduces to `evm_mul_stack_spec_within` by `exact`; the canonical-shim
    pattern from §4 of the design doc is therefore degenerate here. -/
theorem evm_mul_stack_spec_within_layout
    (_L : MultiplyScratchpadLayout) (_hL : _L.Valid)
    (sp base : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word) :
    cpsTripleWithin 63 base (base + 252) (evm_mul_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (evmMulStackPost sp a b) :=
  evm_mul_stack_spec_within sp base a b v5 v6 v7 v10 v11

end EvmAsm.Evm64
