/-
  EvmAsm.Stateless.Crypto.FieldAssertions

  Assertion vocabulary for the precompile field towers (GH #11574).

  ## ⚠️ Read this before reaching for the LE form

  #11574 asks for `fpLimbsIs`, *"a fixed-width little-endian limb buffer"*, and
  names `blsg_lt_p` / `bnf_lt_p` as its first consumers. **Those two things are
  inconsistent**, which is why this module leads with the big-endian form:
  `scripts/asm-fixtures/bls12G1LtPFunction.s` is a byte-at-a-time MSB-first
  `lbu`/`bltu` scan against `blsg_p_be` — no `ld`, no 8-byte stride, no alignment
  requirement. Both `lt_p` triples state their post over `beBytesToNat`.

  The LE 6×64 / 4×64 layout is real, but its consumers are the *converters*
  (`blsg_be_to_le` writes limb `i` at `base + 8i`, LSB first) and the accelerator
  point forms. So `fpLimbsIs` is here too, and is genuinely useful — but as the
  companion to the BE form rather than as the prerequisite it was filed as.

  ## Why this is core and not `Codegen/RegionPredicates.lean`

  `check-layering` L1 makes `EvmAsm/Codegen` a **pure sink**: 19 files under
  `Codegen/**` import `SpecRef`, and 0 files under `Stateless/**` or `EL/**`
  import `Codegen`. A crypto field predicate has to be consumable by a
  **core-side** bridge against `bytes_to_fq`, so it cannot live under `Codegen`.

  ⭐ The same rule sends `balEntriesFrom` (#10817) the other way, and the pair is
  consistent rather than contradictory: *same rule, opposite consequence*.
  #10817's obligation is about the **emitted program**, so its predicate lives
  Codegen-side and may cite SpecRef freely; this one must be visible from core.

  ## The primes are the ones the routines actually compare against

  ⚠️ `blsg_lt_p` compares against `blsg_p_be`, the **base field** prime
  (`Bls12.blsP`, 381-bit). #11574 and `docs/leaf-routine-targets.md` both paired
  it with `Kzg.bytes_to_bls_field` / `BLS_MODULUS`, which is the **scalar field
  order** (255-bit) — a different prime, and a different guest routine
  (`blsk_lt_be`).
-/

import EvmAsm.Crypto.BeBytesBridge
import EvmAsm.Rv64.SAsm.AccelStep
import EvmAsm.Stateless.SpecRef.PrecompilesBls
import EvmAsm.Stateless.SpecRef.PrecompilesKzg

namespace EvmAsm.Stateless.Crypto

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Crypto (beBytesToNat)

/-! ## The big-endian form — what the `lt_p` routines actually read -/

/-- **A big-endian field element in memory.** `width` bytes at `base`, decoding
    to `v`, with `v < p` carried as part of the resource.

    Shape follows `accountRlpIs` (`Stateless/State/AccountAssertions.lean:118`):
    a value-carrying `…Is` whose well-formedness sits beside the `bytesRegion`
    rather than being left to the caller. `…Is` is the right name per
    `RegionPredicates`' convention — this pins the *whole* region, so the name
    stays true. -/
def fpBeBytesIs (width p : Nat) (base : Word) (v : Nat) : Assertion :=
  fun ps => ∃ bs : List (BitVec 8),
    bs.length = width ∧ beBytesToNat bs = v ∧ v < p ∧ bytesRegion base bs ps

theorem pcFree_fpBeBytesIs (width p : Nat) (base : Word) (v : Nat) :
    (fpBeBytesIs width p base v).pcFree := by
  intro ps h
  obtain ⟨bs, -, -, -, hreg⟩ := h
  exact bytesRegion_pcFree base bs ps hreg

/-- BLS12-381 base field element: 48 big-endian bytes, `< blsP`. This is the
    exact resource `blsgLtP_spec` holds as `bytesRegion inPtr xs` plus
    `xs.length = 48`. -/
def blsFpBeIs (base : Word) (v : Nat) : Assertion :=
  fpBeBytesIs 48 SpecRef.Bls12.blsP base v

/-- BN254 base field element: 32 big-endian bytes, `< fieldModulus`. -/
def bnFpBeIs (base : Word) (v : Nat) : Assertion :=
  fpBeBytesIs 32 SpecRef.Bn128.fieldModulus base v

/-! ## The little-endian limb form — the converters' and accelerators' view

    Defined over the **existing** `wsNat` / `leBytesN` (`Rv64/SAsm/AccelStep.lean`)
    rather than a fresh limb decoder: `wsNat nl ws k` is already "the `nl` limbs
    at byte offset `k` read little-endian", and `nl = 6` is already documented
    there as the BLS12-381 view. -/

/-- **A little-endian limb-buffer field element.** `nl` 64-bit limbs at `base`,
    LSB limb first, decoding to `v < p`. -/
def fpLimbsIs (nl p : Nat) (base : Word) (v : Nat) : Assertion :=
  fun ps => v < p ∧ bytesRegion base (leBytesN nl v) ps

theorem pcFree_fpLimbsIs (nl p : Nat) (base : Word) (v : Nat) :
    (fpLimbsIs nl p base v).pcFree := by
  intro ps h
  exact bytesRegion_pcFree base (leBytesN nl v) ps h.2

/-- BLS12-381 base field element as six LE limbs — the shape `blsg_be_to_le`
    writes and `blsg_le_add` consumes. -/
def blsFpLimbsIs (base : Word) (v : Nat) : Assertion :=
  fpLimbsIs 6 SpecRef.Bls12.blsP base v

/-- BN254 base field element as four LE limbs. -/
def bnFpLimbsIs (base : Word) (v : Nat) : Assertion :=
  fpLimbsIs 4 SpecRef.Bn128.fieldModulus base v

/-! ## Point records

    ⚠️ **The two families' contents types are genuinely different and are kept
    so.** BLS G1 is `Bn128.Proj Nat` — a projective triple, with `z = 0` meaning
    infinity (`PrecompilesBls.lean:98`). BN254 is `Weier.Pt = Option (Nat × Nat)`
    — an affine option, with `none` meaning infinity
    (`PrecompilesCurve.lean:35`, `:91`). Forcing a shared contents type would
    only move the case split somewhere less honest. -/

/-- On-curve for BLS12-381 G1, **stated, not proven** — `y² = x³ + 4 (mod p)`,
    mirroring `PrecompilesBls.lean:100`. Per #11574 item 2 this is a
    well-formedness proposition the vocabulary carries, not an obligation this
    module discharges. -/
def blsG1OnCurve (x y : Nat) : Prop :=
  (y * y) % SpecRef.Bls12.blsP = (x * x * x + 4) % SpecRef.Bls12.blsP

/-- On-curve for BN254 G1 — `y² = x³ + 3 (mod p)`, mirroring
    `PrecompilesCurve.lean:92`. Stated, not proven. -/
def bnG1OnCurve (x y : Nat) : Prop :=
  (y * y) % SpecRef.Bn128.fieldModulus
    = (x * x * x + 3) % SpecRef.Bn128.fieldModulus

/-- **A BLS12-381 G1 affine point in the guest's compact BE layout**: `x` at
    `base`, `y` at `base + 48`, both `< p`, with the on-curve side condition
    carried as a proposition. -/
def g1AffineIs (base : Word) (x y : Nat) : Assertion :=
  fun ps => blsG1OnCurve x y ∧
    (blsFpBeIs base x ** blsFpBeIs (base + BitVec.ofNat 64 48) y) ps

/-- **A BN254 G1 point in the guest's compact BE layout**: `x` at `base`, `y` at
    `base + 32`. -/
def bnPointIs (base : Word) (x y : Nat) : Assertion :=
  fun ps => bnG1OnCurve x y ∧
    (bnFpBeIs base x ** bnFpBeIs (base + BitVec.ofNat 64 32) y) ps

/-! ## Satisfiability witnesses

    ⚠️ Required rather than decorative. `RegionPredicates.lean:518-522` records
    the #10688 lesson: *a predicate no state can satisfy proves nothing about the
    region, and a bundled hypothesis can make a theorem vacuous without saying
    so.* `g1AffineIs` bundles an on-curve condition, which is exactly the shape
    that can be accidentally unsatisfiable — so the generators below are checked
    rather than assumed.

    The BN254 generator `(1, 2)` is on-curve: `2² = 4 = 1³ + 3`. -/

example : bnG1OnCurve 1 2 := by unfold bnG1OnCurve; decide

/-- The point at infinity's coordinates are **not** on the curve, and the port
    handles it by a separate `x == 0 && y == 0` branch rather than by the curve
    equation (`PrecompilesCurve.lean:91`). Pinned so nobody folds the infinity
    case into `bnG1OnCurve` and makes the predicate accept a non-point. -/
example : ¬ bnG1OnCurve 0 0 := by unfold bnG1OnCurve; decide

/-- Both moduli really are distinct from the scalar order that #11574 named —
    the correction this module's header records. -/
theorem blsP_ne_blsModulus : SpecRef.Bls12.blsP ≠ SpecRef.Kzg.BLS_MODULUS := by
  decide

end EvmAsm.Stateless.Crypto
