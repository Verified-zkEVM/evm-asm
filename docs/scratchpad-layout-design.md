# Scratchpad-Layout Abstraction — Design Note (Issue #334)

This document proposes the abstraction shape for "make scratchpad
locations variable" (GH #334). It builds directly on the offset/role
catalogue in `docs/scratchpad-layout-survey.md` (slice 1, evm-asm-l9g1)
and on the named-PC-offset convention introduced for #301
(`clzOff`, `addbackBeqOff`, … in `EvmAsm/Evm64/DivMod/Spec/Base.lean`).

Beads: evm-asm-86d1 (slice 2 of evm-asm-4mka / GH #334). Docs only — no
code in this PR.

## 1. Goal

Today every `sp`-relative scratch cell in DivMod (and a few in Byte /
Shift / SignExtend) is wired into specs as a hardcoded
`signExtend12 N` literal. That bakes the layout into the verified
program, which:

- forces every caller to surrender the same 4 KiB sp-window in the
  same internal arrangement, and
- makes it impossible to reuse one routine inside a different scratch
  arrangement (e.g. composing `BYTE` with `DIV` would today alias the
  0..56 block by accident — see survey §4).

Goal: **the scratchpad arrangement becomes an explicit parameter**, so
that callers supply a `XxxScratchpadLayout` value and the existing
proofs go through unchanged when supplied with the canonical layout.

## 2. Where the layout lives

**Per-routine, not shared.** Each routine that uses an internal scratch
block defines its own layout struct in the routine's `Spec/` directory:

```
EvmAsm/Evm64/Multiply/Spec/Layout.lean   -- MultiplyScratchpadLayout
EvmAsm/Evm64/DivMod/Spec/Layout.lean     -- DivModScratchpadLayout
EvmAsm/Evm64/Byte/Spec/Layout.lean       -- ByteScratchpadLayout
EvmAsm/Evm64/Shift/Spec/Layout.lean      -- ShiftScratchpadLayout (1 cell)
EvmAsm/Evm64/SignExtend/Spec/Layout.lean -- SignExtendScratchpadLayout (alias)
```

Rationale:

- The DivMod layout has ~10 named roles; Byte has a separate 0..56
  block; Shift uses a single cell. Forcing them into a common struct
  produces an awkward sum/`Option` shape and prevents `divmod_addr` /
  `bv_addr` from indexing on a small set of fixed fields.
- A common parent type (e.g. `class HasScratchpad`) can be added later
  if a real cross-routine caller needs it. **YAGNI for slice 2** — the
  pilot in slice 3 (Multiply) doesn't need it; slice 4 (broaden to
  DivMod/Shift) will revisit.

The layout struct lives in `Spec/Layout.lean` rather than
`LoopDefs/Bundle.lean` so the assertion bundles can `import` the
layout without circularity.

## 3. Struct shape

Layout records hold **byte offsets relative to a layout-supplied
base register**, not absolute addresses. Validity and disjointness are
properties of the *layout* (proved once for the canonical instance);
the body proofs depend only on offset *relationships*, never on
particular numerical values.

### 3.1 DivMod (the hot case)

```lean
/-- Layout of the DivMod scratchpad.
    All fields are byte offsets from `base`, intended to be added as
    `signExtend12` so that bv_omega + divmod_addr keep working. -/
structure DivModScratchpadLayout where
  -- v[]: divisor limbs (normalized), 4 contiguous 8-byte cells
  vOff   : BitVec 12      -- vOff, vOff+8, vOff+16, vOff+24
  -- u[]: dividend limbs, 5 contiguous cells with the j-shift convention
  -- uOff  is u[0]; uOff - 8 is u[1]; ... uOff - 32 is u_top
  uOff   : BitVec 12
  -- q[]: quotient limbs, 4 contiguous cells, q[0] at qOff, ... q[3] at qOff-24
  qOff   : BitVec 12
  -- single-cell scratch slots
  retOff : BitVec 12
  dOff   : BitVec 12
  dloOff : BitVec 12
  un0Off : BitVec 12
  jOff   : BitVec 12
  nOff   : BitVec 12
  -- caller-saved-frame block (4000..4016 in the survey + epilogue at 3992)
  frameOff : BitVec 12
  deriving DecidableEq, Repr
```

Plus a single `Prop`-valued bundle of validity / disjointness
obligations:

```lean
/-- Layout obligations: each cell is 8-aligned and disjoint from every
    other named cell. The j-window slots are bound by uOff/qOff plus
    the algebraic constraints `qOff = uOff + 32` and `vOff = uOff - 4024`
    (see survey §3); the canonical layout discharges these by `decide`. -/
structure DivModScratchpadLayout.Valid (L : DivModScratchpadLayout) : Prop where
  align_v   : (L.vOff &&& 7) = 0
  align_u   : (L.uOff &&& 7) = 0
  align_q   : (L.qOff &&& 7) = 0
  -- … (one per single-cell slot)
  -- algebraic relationships preserved by the proofs:
  q_eq_u_plus_32 : L.qOff = L.uOff + 32   -- so u[3]@j ≡ u_top@(j-1) still holds
  v_eq_u_minus   : L.vOff + 4024 = L.uOff
  -- pairwise disjointness of single-cell slots and the v/u/q windows:
  disjoint_pairs : ∀ (i j : DivModSlotName), i ≠ j → DisjointSlot L i j
```

The existing concrete-offset specs become the canonical instance:

```lean
def canonicalDivModScratchpadLayout : DivModScratchpadLayout where
  vOff     := 32
  uOff     := signExtend12 4056
  qOff     := signExtend12 4088
  retOff   := signExtend12 3968
  dOff     := signExtend12 3960
  dloOff   := signExtend12 3952
  un0Off   := signExtend12 3944
  jOff     := signExtend12 3976
  nOff     := signExtend12 3984
  frameOff := signExtend12 3992

theorem canonicalDivModScratchpadLayout_valid :
    canonicalDivModScratchpadLayout.Valid := by
  refine ⟨?_, ?_, ?_, …⟩ <;> decide
```

### 3.2 Multiply (the pilot, slice 3)

Multiply does not currently use `sp + signExtend12 N` cells (see survey
§1) — its scratch is reached via `.x12 ↦ᵣ ptr`. So the Multiply pilot
is *not* about migrating literals; it is about (a) defining the same
struct shape, (b) proving the canonical instance valid, and (c)
demonstrating that downstream callers can swap layouts and still
compose with the existing Multiply spec. This makes Multiply a clean
test of the abstraction without the cost of touching 91 files.

### 3.3 Byte / Shift / SignExtend

- `ByteScratchpadLayout` has two named blocks (idx 0..24, result
  32..56). Cheap.
- `ShiftScratchpadLayout` has a single field (`limbOff`). Trivial.
- `SignExtendScratchpadLayout = ShiftScratchpadLayout` (same single
  cell convention).

These are deferred to a follow-up of slice 4.

## 4. How specs consume the layout

A migrated spec takes a layout-and-validity pair as a *parameter*:

```lean
theorem divmod_loop_body_spec
    (L : DivModScratchpadLayout) (hL : L.Valid)
    (sp base : Word) … :
    cpsTriple … := by
  -- existing proof body, with literal offsets replaced by L-projections
  -- and concrete address-equalities discharged via hL plus divmod_addr.
```

Existing call sites continue to work via a thin shim:

```lean
@[deprecated divmod_loop_body_spec]
theorem divmod_loop_body_spec_canonical sp base … :
    cpsTriple … :=
  divmod_loop_body_spec canonicalDivModScratchpadLayout
    canonicalDivModScratchpadLayout_valid sp base …
```

The slice-3 PR introduces *only* the layout struct, the canonical
instance, the `_canonical` shim alias, and the Multiply pilot — every
existing proof keeps the same name and signature, and downstream
clients are not touched.

## 5. Interaction with `divmod_addr`

The grindset in `EvmAsm/Evm64/DivMod/AddrNorm.lean` closes equalities
like `(sp + 4056) - 8 = sp + 4048`. After parameterization the same
equalities become `(sp + L.uOff) - 8 = sp + L.uOff - 8`, which
`bv_addr`/`bv_omega` already handle generically — no `divmod_addr`
entries need to change. New layout-aware lemmas (e.g.
`uOff_minus_8_eq_uOff_4048` *for the canonical layout*) live in a
sibling `LayoutAddrNorm.lean`, registered under `divmod_addr` so that
canonical-layout call sites continue to fold without manual proof.

This means the slice-3 PR can land **without retiring any existing
`divmod_addr` entry** — the abstraction is additive.

## 6. Validity vs disjointness — single bundle

Slice-1 question (b) was: do we state validity per-cell and disjointness
once, or fuse them?

**Answer: fuse them** into the `L.Valid` bundle described in §3. The
proofs need both at once anyway (every memory write requires
`isValidDwordAccess` of *that* cell **and** disjointness from every
other cell already owned), and threading two arguments through every
spec doubles the call-site noise without adding flexibility. A single
bundle that the canonical instance discharges by `decide` is strictly
better for the migration cost.

## 7. Migration plan

```
slice 3  (this design's exit criterion):
  EvmAsm/Evm64/Multiply/Spec/Layout.lean        +new
  + Multiply pilot: layout-parameterized variant of multiply_spec,
    canonical instance, deprecated shim. Existing proofs untouched.
  + lake build green; no behavior change.

slice 4:
  EvmAsm/Evm64/DivMod/Spec/Layout.lean          +new
  + parameterize DivMod loop body, then full path, then dispatcher.
    Each step: introduce L parameter, replace literal offsets with
    L.projections, prove canonical-shim alias.
  + Shift/SignExtend single-cell layouts in the same PR family.

slice 5:
  AGENTS.md / TACTICS.md note: scratchpad-layout convention,
  how to add a new routine's layout, where validity is discharged.
```

No CI gate change. No `divmod_addr` removals.

## 8. Open questions (non-blockers)

1. **Sign of the high-numbered offsets.** Survey §2 notes the
   `+ signExtend12 4088` vs `sp - 8` choice. The struct stores
   `BitVec 12` so both encodings round-trip; the canonical layout uses
   the `+ signExtend12 …` form to match today's proofs. A cleanup PR
   could move to `sp - k` later (issue #265 area).
2. **Cross-routine layout class.** Once Multiply, DivMod, Byte all
   have layouts, a `class HasScratchpad (α : Type) where layout : α →
   ScratchpadLayoutSig` may pay off. Defer until at least one caller
   actually composes two routines (e.g. EXP calling MUL).
3. **Layout polymorphism for stacked DivMod calls.** A future caller
   that runs DivMod twice with different `base` registers can already
   pass two distinct `(L₁, L₂)` pairs — no extra abstraction needed.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
