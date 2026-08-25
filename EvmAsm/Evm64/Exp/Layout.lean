/-
  EvmAsm.Evm64.Exp.Layout

  Empty-layout placeholder for the EXP routine's scratchpad-layout
  abstraction (GH #334 / parent `evm-asm-4mka`, slice `evm-asm-i6oz6`).

  Per `AGENTS.md` ("Scratchpad Layout (#334)") and `EvmAsm/Evm64/OPCODE_TEMPLATE.md`,
  any new opcode subtree that will carry internal `sp`-relative scratch
  cells should define a `XxxScratchpadLayout` structure from day one —
  even if it starts empty — to avoid the retrofit tax once the routine
  gains real scratch later. The canonical empty-layout pilot is
  `EvmAsm/Evm64/Multiply/Layout.lean` (slice 3, beads `evm-asm-1d1o`).

  EXP today holds its 256-bit running accumulator `result` in the local
  scratch frame at `sp + 0 .. sp + 24` (see `exp_prologue` and
  `exp_epilogue` in `EvmAsm/Evm64/Exp/Program.lean`). Those four cells
  are consumed and produced by the EXP iteration scaffold but are not
  yet exposed as a parameterized layout — the per-iteration limb specs
  (slice `evm-asm-mtj3`) and the full-loop composition (slice
  `evm-asm-w5mk`) reference them inline as `sp + 0 .. sp + 24`.

  This file establishes the naming convention so that:

  1. The naming + file convention is mirrored from `Multiply/Layout.lean`
     (`ExpScratchpadLayout`, `ExpScratchpadLayout.Valid`,
     `canonicalExpScratchpadLayout`, `canonicalExpScratchpadLayout_valid`).
  2. Slice 4 (`evm-asm-vst1`, broadening parameterization to DivMod /
     Shift) and any future EXP-internal-scratchpad work has a working
     template to extend.
  3. Downstream consumers can already write
     `(L : ExpScratchpadLayout) (hL : L.Valid)` parameters in their own
     preconditions without churn once EXP's per-iteration / full-loop
     specs land and are migrated to the layout abstraction.

  No code change to existing EXP specs in this PR — the layout
  abstraction is purely additive. See §7 of `docs/scratchpad-layout-design.md`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

module

@[expose] public section
namespace EvmAsm.Evm64

/-- Layout of the EXP routine's `sp`-relative internal scratch cells.

    Empty placeholder — see file-level doc-comment. The struct has zero
    fields and exists to fix the naming / parameter-passing convention
    shared with `MultiplyScratchpadLayout`, the future
    `DivModScratchpadLayout`, and so on.

    Note: the `sp + 0 .. sp + 24` cells touched today by `exp_prologue`
    and `exp_epilogue` (storing the running 256-bit accumulator across
    the 256-iteration square-and-multiply loop) are part of the EXP
    routine's *future* internal scratchpad. They are referenced inline
    by the per-iteration limb specs (slice `evm-asm-mtj3`) and the
    full-loop composition (slice `evm-asm-w5mk`) and remain unaffected
    by any choice of `ExpScratchpadLayout` until those specs land and
    are migrated to the layout abstraction.

    Mirrors `MultiplyScratchpadLayout` exactly, with the rename
    `Multiply → Exp`. -/
structure ExpScratchpadLayout : Type where
  deriving Repr

/-- Validity bundle for `ExpScratchpadLayout`.

    With zero fields the layout has nothing to constrain; `Valid` is
    trivially derivable. Once EXP's per-iteration / full-loop specs are
    migrated to the layout abstraction, this will carry alignment /
    disjointness / algebraic-relationship obligations on the four
    accumulator-limb cells (currently inlined as `sp + 0 .. sp + 24`). -/
structure ExpScratchpadLayout.Valid (_L : ExpScratchpadLayout) : Prop where

/-- Every current EXP scratchpad layout is valid.

    This is a convenience wrapper for downstream specs that already take an
    `ExpScratchpadLayout` parameter while the layout is still empty. -/
theorem ExpScratchpadLayout.valid_any_empty
    (L : ExpScratchpadLayout) :
    L.Valid := {}

/-- The current empty EXP scratchpad layout validity predicate is trivial. -/
theorem ExpScratchpadLayout.valid_iff_true
    (L : ExpScratchpadLayout) :
    L.Valid ↔ True := by
  constructor
  · intro _h
    trivial
  · intro _h
    exact L.valid_any_empty

/-- The canonical EXP scratchpad layout.

    Trivial: there is nothing to choose, so canonical = the unique value.
    Once EXP gains real scratch, this will be the placement matching
    today's hardcoded `sp + 0 .. sp + 24` accumulator cells. -/
def canonicalExpScratchpadLayout : ExpScratchpadLayout := {}

/-- Every current EXP scratchpad layout is the canonical empty layout. -/
theorem ExpScratchpadLayout.eq_canonical
    (L : ExpScratchpadLayout) :
    L = canonicalExpScratchpadLayout := by
  cases L
  rfl

/-- The canonical EXP scratchpad layout is `Valid`. Trivially discharged
    because the layout struct is empty. -/
theorem canonicalExpScratchpadLayout_valid :
    canonicalExpScratchpadLayout.Valid := {}

/-- A layout equal to the current canonical EXP scratchpad layout is valid. -/
theorem ExpScratchpadLayout.valid_of_eq_canonical
    {L : ExpScratchpadLayout}
    (h_eq : L = canonicalExpScratchpadLayout) :
    L.Valid := by
  subst h_eq
  exact canonicalExpScratchpadLayout_valid

/-- For the current empty EXP scratchpad layout, validity is equivalent to
    being the canonical layout. -/
theorem ExpScratchpadLayout.valid_iff_eq_canonical
    (L : ExpScratchpadLayout) :
    L.Valid ↔ L = canonicalExpScratchpadLayout := by
  constructor
  · intro _h
    exact L.eq_canonical
  · exact L.valid_of_eq_canonical

/-- The canonical EXP scratchpad layout validity predicate is trivial. -/
theorem canonicalExpScratchpadLayout_valid_iff_true :
    canonicalExpScratchpadLayout.Valid ↔ True :=
  ExpScratchpadLayout.valid_iff_true canonicalExpScratchpadLayout

end EvmAsm.Evm64
