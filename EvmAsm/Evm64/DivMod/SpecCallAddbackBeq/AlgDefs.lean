/-
  EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.AlgDefs

  Word-level `@[irreducible]` def bundles for the call+addback BEQ
  algorithm's intermediate values, plus their unfold lemmas, cross-bridge
  equivalences (single-addback ⟷ double-addback), parent_64ms_form
  reductions, and val256 bounds.

  Contents (high-level):
  - `addbackN4_carry_le_one` — structural bound on the addback carry.
  - Bundle defs: `algCallAddbackBeqCarry`, `algCallAddbackBeqMsC3`,
    `algCallAddbackBeqU4`, `algCallAddbackBeqPost1Val`,
    `algCallAddbackBeqPost1Limb{0..3}`, `algCallAddbackBeqUn{0..3}Out`,
    `algCallAddbackBeqAbPrimeLimb{0..3}`, `algCallAddbackBeqAbPrimeVal`,
    `algCallAddbackBeqMsLowVal`.
  - Their `_unfold` lemmas (rfl-style let-chain expansions).
  - Cross-bridge: `algCallAddbackBeqUn{0..3}Out_eq_post1Limb{0..3}_of_single_addback`
    and `_eq_abPrimeLimb{0..3}_of_double_addback`.
  - `_eq_parent_64ms_form` reductions (folding into `mulsubN4`/`addbackN4_64ms`).
  - `_eq_val256_limbs` aggregations.
  - val256 bounds: `algCallAddbackBeqPost1Val_lt_pow256`,
    `algCallAddbackBeqAbPrimeVal_lt_pow256`,
    `algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s`.

  Extracted from `SpecCallAddbackBeq.lean` (2026-04-28) to ease the
  file-size guardrail. Issue #1338 / #61.
-/

import EvmAsm.Evm64.DivMod.SpecCall

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- **Sub-stub: addbackN4_carry returns 0 or 1.** Pure structural fact about
    `addbackN4_carry` — the output is `aco3 = ac1_3 ||| ac2_3` where each
    is 0 or 1, so `aco3 ∈ {0, 1}`. -/
theorem addbackN4_carry_le_one (un0 un1 un2 un3 v0 v1 v2 v3 : Word) :
    (addbackN4_carry un0 un1 un2 un3 v0 v1 v2 v3).toNat ≤ 1 := by
  unfold addbackN4_carry
  simp only []
  split_ifs <;> decide

/-- **Irreducible bundle: the call+addback BEQ algorithm's first-addback carry.**

    Bundles the full let-chain (shift, antiShift, b0'..b3', u0..u4, qHat, ms) into
    an opaque `Word` value. Used by callers that need to talk about the carry
    without paying the let-chain elaboration cost.

    The body uses the same `% 64` form as `n4CallAddbackBeqSemanticHolds_def`,
    so consumers get a consistent shape. Use `algCallAddbackBeqCarry_unfold`
    to expose the let-chain when needed in proofs. -/
@[irreducible]
def algCallAddbackBeqCarry (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'

/-- **Irreducible bundle: the call+addback BEQ algorithm's mulsub borrow c3.**

    Parallel to `algCallAddbackBeqCarry`. Encapsulates the deep let-chain
    needed to talk about the c3 = mulsub borrow at normalized limbs as a
    single opaque Word value, sidestepping let-chain elaboration cost. -/
@[irreducible]
def algCallAddbackBeqMsC3 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  ms.2.2.2.2

/-- **Irreducible bundle: the call+addback BEQ algorithm's u4 (overflow limb).** -/
@[irreducible]
def algCallAddbackBeqU4 (a b : EvmWord) : Word :=
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  (a.getLimbN 3) >>> antiShift

/-- Unfolding lemma for `algCallAddbackBeqCarry`. -/
theorem algCallAddbackBeqCarry_unfold {a b : EvmWord} :
    algCallAddbackBeqCarry a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3') := by
  show algCallAddbackBeqCarry a b = _
  unfold algCallAddbackBeqCarry
  rfl

/-- **Irreducible bundle: val256 of post1 limbs at normalized inputs.**

    Captures the val256 of the 4 low outputs of `addbackN4 ms.1 ms.2.1
    ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'` (i.e., the first-addback result
    at carry-input 0). When the first-addback carry is 1 (single-addback
    branch), this Nat value is exactly `val256(a)%val256(b) * 2^s` per
    `post1_val_eq_amod_pow_s_pure_nat`.

    Encapsulates the deep let-chain so consumers can talk about the
    addback post1 val256 as a single opaque Nat, sidestepping the
    elaboration-cost penalty observed in the parent adapter. -/
@[irreducible]
def algCallAddbackBeqPost1Val (a b : EvmWord) : Nat :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let post1 := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1

/-- Unfolding lemma for `algCallAddbackBeqPost1Val`. -/
theorem algCallAddbackBeqPost1Val_unfold {a b : EvmWord} :
    algCallAddbackBeqPost1Val a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let post1 := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
     val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1) := by
  show algCallAddbackBeqPost1Val a b = _
  unfold algCallAddbackBeqPost1Val
  rfl

/-- **Irreducible bundles: per-limb post1 outputs at normalized inputs.**

    4 individual Word-valued bundles capturing the low 4 outputs of
    `addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'` — same
    expression as `algCallAddbackBeqPost1Val`'s underlying val256. Used
    to keep the goal manageable when reasoning per-limb (avoids huge
    inline `mulsubN4 ...` expressions). -/
@[irreducible]
def algCallAddbackBeqPost1Limb0 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').1

@[irreducible]
def algCallAddbackBeqPost1Limb1 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.1

@[irreducible]
def algCallAddbackBeqPost1Limb2 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.1

@[irreducible]
def algCallAddbackBeqPost1Limb3 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.2.1

/-- **Packaging: `algCallAddbackBeqPost1Val = val256 of irreducible limbs`** (CLOSED).

    Bridges the val256-level `algCallAddbackBeqPost1Val` to the per-limb
    irreducible bundles. By definition both unfold to the same thing —
    proof is rfl after unfolding both sides. Useful when applying
    `denorm_4limb_eq_mod_of_val256_eq_amod_pow_s` with the irreducible
    Limb0..Limb3 as X1..X4: the goal stays small. -/
theorem algCallAddbackBeqPost1Val_eq_val256_limbs (a b : EvmWord) :
    algCallAddbackBeqPost1Val a b =
    val256 (algCallAddbackBeqPost1Limb0 a b)
           (algCallAddbackBeqPost1Limb1 a b)
           (algCallAddbackBeqPost1Limb2 a b)
           (algCallAddbackBeqPost1Limb3 a b) := by
  unfold algCallAddbackBeqPost1Val
    algCallAddbackBeqPost1Limb0 algCallAddbackBeqPost1Limb1
    algCallAddbackBeqPost1Limb2 algCallAddbackBeqPost1Limb3
  rfl

/-- **Irreducible bundles: per-limb un{i}Out (the if-then-else outputs).**

    These are the parent adapter's per-limb output values: `un{i}Out :=
    if carry = 0 then ab'.{i_low} else ab.{i_low}`. Wrapping them as
    irreducible defs keeps the parent's goal manageable. -/
@[irreducible]
def algCallAddbackBeqUn0Out (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  if carry = 0 then ab'.1 else ab.1

@[irreducible]
def algCallAddbackBeqUn1Out (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  if carry = 0 then ab'.2.1 else ab.2.1

@[irreducible]
def algCallAddbackBeqUn2Out (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  if carry = 0 then ab'.2.2.1 else ab.2.2.1

@[irreducible]
def algCallAddbackBeqUn3Out (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1

/-- Unfolding lemmas for un{i}Out irreducibles (used by the parent to fold). -/
theorem algCallAddbackBeqUn0Out_unfold {a b : EvmWord} :
    algCallAddbackBeqUn0Out a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     if carry = 0 then ab'.1 else ab.1) := by
  show algCallAddbackBeqUn0Out a b = _; unfold algCallAddbackBeqUn0Out; rfl

theorem algCallAddbackBeqUn1Out_unfold {a b : EvmWord} :
    algCallAddbackBeqUn1Out a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     if carry = 0 then ab'.2.1 else ab.2.1) := by
  show algCallAddbackBeqUn1Out a b = _; unfold algCallAddbackBeqUn1Out; rfl

theorem algCallAddbackBeqUn2Out_unfold {a b : EvmWord} :
    algCallAddbackBeqUn2Out a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     if carry = 0 then ab'.2.2.1 else ab.2.2.1) := by
  show algCallAddbackBeqUn2Out a b = _; unfold algCallAddbackBeqUn2Out; rfl

theorem algCallAddbackBeqUn3Out_unfold {a b : EvmWord} :
    algCallAddbackBeqUn3Out a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1) := by
  show algCallAddbackBeqUn3Out a b = _; unfold algCallAddbackBeqUn3Out; rfl

/-- **Bridge: `algCallAddbackBeqUn0Out = algCallAddbackBeqPost1Limb0` in single-addback** (CLOSED). -/
theorem algCallAddbackBeqUn0Out_eq_post1Limb0_of_single_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqUn0Out a b = algCallAddbackBeqPost1Limb0 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn0Out algCallAddbackBeqPost1Limb0
  simp only []
  rw [if_neg hcarry]
  -- Now LHS = ab.1, RHS = post1.1 (with input 0). Equal via low-4-indep.
  rfl

theorem algCallAddbackBeqUn1Out_eq_post1Limb1_of_single_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqUn1Out a b = algCallAddbackBeqPost1Limb1 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn1Out algCallAddbackBeqPost1Limb1
  simp only []
  rw [if_neg hcarry]
  rfl

theorem algCallAddbackBeqUn2Out_eq_post1Limb2_of_single_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqUn2Out a b = algCallAddbackBeqPost1Limb2 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn2Out algCallAddbackBeqPost1Limb2
  simp only []
  rw [if_neg hcarry]
  rfl

theorem algCallAddbackBeqUn3Out_eq_post1Limb3_of_single_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqUn3Out a b = algCallAddbackBeqPost1Limb3 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn3Out algCallAddbackBeqPost1Limb3
  simp only []
  rw [if_neg hcarry]
  rfl

/-- **Irreducible bundles: per-limb second-addback (ab') outputs.**

    Mirror of `algCallAddbackBeqPost1Limb{i}` for the **double-addback**
    branch (carry = 0): wraps the second `addbackN4` call's per-limb low
    outputs (ab'.{i_low}). Used to keep the double-addback parent goal
    manageable when reasoning per-limb.

    Issue #1338 (Phase B.4 mechanical infrastructure).  -/
@[irreducible]
def algCallAddbackBeqAbPrimeLimb0 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').1

@[irreducible]
def algCallAddbackBeqAbPrimeLimb1 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.1

@[irreducible]
def algCallAddbackBeqAbPrimeLimb2 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.2.1

@[irreducible]
def algCallAddbackBeqAbPrimeLimb3 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.2.2.1

/-- **Bridge: Un{i}Out = AbPrimeLimb{i} in double-addback** (Phase B.6, CLOSED).

    When the first addback's carry is zero, the algorithm runs a second
    addback. This bridge folds the parent's `un{i}Out` to the irreducible
    `AbPrimeLimb{i}` form. Issue #1338. -/
theorem algCallAddbackBeqUn0Out_eq_abPrimeLimb0_of_double_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqUn0Out a b = algCallAddbackBeqAbPrimeLimb0 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn0Out algCallAddbackBeqAbPrimeLimb0
  simp only []
  rw [if_pos hcarry]

theorem algCallAddbackBeqUn1Out_eq_abPrimeLimb1_of_double_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqUn1Out a b = algCallAddbackBeqAbPrimeLimb1 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn1Out algCallAddbackBeqAbPrimeLimb1
  simp only []
  rw [if_pos hcarry]

theorem algCallAddbackBeqUn2Out_eq_abPrimeLimb2_of_double_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqUn2Out a b = algCallAddbackBeqAbPrimeLimb2 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn2Out algCallAddbackBeqAbPrimeLimb2
  simp only []
  rw [if_pos hcarry]

theorem algCallAddbackBeqUn3Out_eq_abPrimeLimb3_of_double_addback
    (a b : EvmWord) (hcarry : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqUn3Out a b = algCallAddbackBeqAbPrimeLimb3 a b := by
  show _ = _
  rw [algCallAddbackBeqCarry_unfold] at hcarry
  unfold algCallAddbackBeqUn3Out algCallAddbackBeqAbPrimeLimb3
  simp only []
  rw [if_pos hcarry]

/-- **Irreducible bundle: val256 of ab' (second-addback) limbs at normalized inputs.**

    Captures the val256 of the 4 low outputs of the **second** addback
    `addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'`,
    which fires in the double-addback branch (carry = 0).

    Mirrors `algCallAddbackBeqPost1Val` for the double-addback path. The
    Word-level wrapper `algCallAddbackBeqAbPrimeVal_eq_amod_pow_s_of_double_addback`
    (Phase B.5, blocked on Knuth-B #1337) will tie this Nat to
    `val256(a) % val256(b) * 2^s` via the c3 = 1 derivation.

    Issue #1338 (Phase B.4 mechanical infrastructure). -/
@[irreducible]
def algCallAddbackBeqAbPrimeVal (a b : EvmWord) : Nat :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  let abPrime := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  val256 abPrime.1 abPrime.2.1 abPrime.2.2.1 abPrime.2.2.2.1

/-- Unfolding lemma for `algCallAddbackBeqAbPrimeVal`. -/
theorem algCallAddbackBeqAbPrimeVal_unfold {a b : EvmWord} :
    algCallAddbackBeqAbPrimeVal a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     let abPrime := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
     val256 abPrime.1 abPrime.2.1 abPrime.2.2.1 abPrime.2.2.2.1) := by
  show algCallAddbackBeqAbPrimeVal a b = _
  unfold algCallAddbackBeqAbPrimeVal
  rfl

/-- **Packaging: `algCallAddbackBeqAbPrimeVal = val256 of irreducible AbPrimeLimb`** (CLOSED).

    Mirrors `algCallAddbackBeqPost1Val_eq_val256_limbs` for the double-
    addback path. By definition both unfold to the same val256 expression
    over the second-addback's low 4 outputs. Used when applying
    `denorm_4limb_eq_mod_of_val256_eq_amod_pow_s` with the irreducible
    AbPrimeLimb0..AbPrimeLimb3 limbs as X1..X4 (keeps the goal small). -/
theorem algCallAddbackBeqAbPrimeVal_eq_val256_limbs (a b : EvmWord) :
    algCallAddbackBeqAbPrimeVal a b =
    val256 (algCallAddbackBeqAbPrimeLimb0 a b)
           (algCallAddbackBeqAbPrimeLimb1 a b)
           (algCallAddbackBeqAbPrimeLimb2 a b)
           (algCallAddbackBeqAbPrimeLimb3 a b) := by
  unfold algCallAddbackBeqAbPrimeVal
    algCallAddbackBeqAbPrimeLimb0 algCallAddbackBeqAbPrimeLimb1
    algCallAddbackBeqAbPrimeLimb2 algCallAddbackBeqAbPrimeLimb3
  rfl

/-- **Bridge: `algCallAddbackBeqPost1Limb0` in parent-friendly `(64 - s)` form** (CLOSED). -/
theorem algCallAddbackBeqPost1Limb0_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqPost1Limb0 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').1) := by
  show algCallAddbackBeqPost1Limb0 a b = _
  unfold algCallAddbackBeqPost1Limb0
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bridge: `algCallAddbackBeqPost1Limb1` in parent-friendly `(64 - s)` form** (CLOSED). -/
theorem algCallAddbackBeqPost1Limb1_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqPost1Limb1 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.1) := by
  show algCallAddbackBeqPost1Limb1 a b = _
  unfold algCallAddbackBeqPost1Limb1
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bridge: `algCallAddbackBeqPost1Limb2` in parent-friendly `(64 - s)` form** (CLOSED). -/
theorem algCallAddbackBeqPost1Limb2_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqPost1Limb2 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.1) := by
  show algCallAddbackBeqPost1Limb2 a b = _
  unfold algCallAddbackBeqPost1Limb2
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bridge: `algCallAddbackBeqPost1Limb3` in parent-friendly `(64 - s)` form** (CLOSED). -/
theorem algCallAddbackBeqPost1Limb3_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqPost1Limb3 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.2.1) := by
  show algCallAddbackBeqPost1Limb3 a b = _
  unfold algCallAddbackBeqPost1Limb3
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bridges: `algCallAddbackBeqAbPrimeLimb{i}` in parent-friendly `(64 - s)`
    form** (Phase B.4 mechanical, CLOSED).

    Mirror of `algCallAddbackBeqPost1Limb{i}_eq_parent_64ms_form` for the
    double-addback's second-addback per-limb output. Same `simp_only`
    proof pattern: rewrite the antiShift to `64 - s` and the `s % 64`
    to `s`, both under `hshift_nz`.

    Issue #1338. -/
theorem algCallAddbackBeqAbPrimeLimb0_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqAbPrimeLimb0 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').1) := by
  show algCallAddbackBeqAbPrimeLimb0 a b = _
  unfold algCallAddbackBeqAbPrimeLimb0
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

theorem algCallAddbackBeqAbPrimeLimb1_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqAbPrimeLimb1 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.1) := by
  show algCallAddbackBeqAbPrimeLimb1 a b = _
  unfold algCallAddbackBeqAbPrimeLimb1
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

theorem algCallAddbackBeqAbPrimeLimb2_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqAbPrimeLimb2 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.2.1) := by
  show algCallAddbackBeqAbPrimeLimb2 a b = _
  unfold algCallAddbackBeqAbPrimeLimb2
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

theorem algCallAddbackBeqAbPrimeLimb3_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqAbPrimeLimb3 a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let c3 := ms.2.2.2.2
     let u4_new := u4 - c3
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
     (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.2.2.1) := by
  show algCallAddbackBeqAbPrimeLimb3 a b = _
  unfold algCallAddbackBeqAbPrimeLimb3
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bridge: `algCallAddbackBeqPost1Val` in parent-friendly `(64 - s)` form** (CLOSED).

    Parallel to `algCallAddbackBeqCarry_eq_parent_64ms_form`. Equates the
    irreducible def's antiShift-form body with the parent's local
    `64 - s` form, so the parent can rewrite its local val256 of the
    addback post1 limbs to `algCallAddbackBeqPost1Val a b`. -/
theorem algCallAddbackBeqPost1Val_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqPost1Val a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let post1 := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
     val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1) := by
  rw [algCallAddbackBeqPost1Val_unfold]
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bridge: `algCallAddbackBeqCarry` in parent-friendly `(64 - s)` form** (CLOSED).

    The irreducible def's body uses antiShift form `(signExtend12 0 -
    clz).toNat % 64`. The parent adapter's local `set` lines use the
    Nat-subtraction form `64 - s` (matching what the runtime emits via
    bit-shift instructions). This bridge equates the two forms under
    `hshift_nz`, so the parent can use `algCallAddbackBeqCarry a b ≠ 0`
    directly from its local `carry_word ≠ 0` hypothesis. -/
theorem algCallAddbackBeqCarry_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqCarry a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3') := by
  rw [algCallAddbackBeqCarry_unfold]
  -- Convert antiShift form to (64 - s) form via hanti_toNat_mod.
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Irreducible bundle: val256 of ms low 4 outputs at normalized inputs.**

    Captures `val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1` where `ms = mulsubN4
    qHat b0' b1' b2' b3' u0 u1 u2 u3` at the algorithm's normalized limbs.
    Used as `ms_val` in `post1_val_eq_amod_pow_s_pure_nat` and the addback
    Euclidean (h_addback) and mulsub Euclidean (h_mulsub) preconditions. -/
@[irreducible]
def algCallAddbackBeqMsLowVal (a b : EvmWord) : Nat :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1

/-- Unfolding lemma for `algCallAddbackBeqMsLowVal`. -/
theorem algCallAddbackBeqMsLowVal_unfold {a b : EvmWord} :
    algCallAddbackBeqMsLowVal a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1) := by
  show algCallAddbackBeqMsLowVal a b = _
  unfold algCallAddbackBeqMsLowVal
  rfl

/-- **Bridge: `algCallAddbackBeqMsLowVal` in parent-friendly `(64 - s)` form** (CLOSED).

    Parallel to the carry/post1Val bridges. Equates the irreducible def's
    antiShift-form body with the parent's local `64 - s` form for the
    val256 of mulsub low 4 outputs. -/
theorem algCallAddbackBeqMsLowVal_eq_parent_64ms_form
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    algCallAddbackBeqMsLowVal a b =
    (let s := (clzResult (b.getLimbN 3)).1.toNat % 64
     let b0' := (b.getLimbN 0) <<< s
     let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
     let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
     let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
     let u0 := (a.getLimbN 0) <<< s
     let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
     let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
     let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
     let u4 := (a.getLimbN 3) >>> (64 - s)
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1) := by
  rw [algCallAddbackBeqMsLowVal_unfold]
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  simp only [h_anti_eq, h_s_eq]

/-- **Bound: `algCallAddbackBeqPost1Val a b < 2^256`** (CLOSED).

    Trivial: the addback's low 4 outputs are 4 `Word`s, so their `val256` is
    bounded by `2^256` regardless of inputs. Useful as the `h_post1_lt`
    precondition of `post1_val_eq_amod_pow_s_pure_nat` when closing the
    `algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback` wrapper. -/
theorem algCallAddbackBeqPost1Val_lt_pow256 (a b : EvmWord) :
    algCallAddbackBeqPost1Val a b < 2 ^ 256 := by
  rw [algCallAddbackBeqPost1Val_unfold]
  simp only []
  exact EvmWord.val256_bound _ _ _ _

/-- **AbPrimeVal val256 bound** (Phase B.4 mechanical, CLOSED).

    Mirror of `algCallAddbackBeqPost1Val_lt_pow256` for the
    double-addback's second-addback val256. Used as the
    `h_abPrime_lt` precondition of `abPrime_val_eq_amod_pow_s_pure_nat`
    (B.3) when closing B.5.

    Issue #1338. -/
theorem algCallAddbackBeqAbPrimeVal_lt_pow256 (a b : EvmWord) :
    algCallAddbackBeqAbPrimeVal a b < 2 ^ 256 := by
  rw [algCallAddbackBeqAbPrimeVal_unfold]
  simp only []
  exact EvmWord.val256_bound _ _ _ _

/-- **Bound: `algCallAddbackBeqU4 * 2^256 ≤ val256(a) * 2^s`** (CLOSED).

    Uses `u4 = a3 >>> antiShift = a3 / 2^(64-s)` so `u4 * 2^(64-s) ≤ a3`,
    then multiplies by `2^(192+s)` and uses `val256(a) ≥ a3 * 2^192` to
    yield `u4 * 2^256 ≤ val256(a) * 2^s`.

    Useful as the `h_u4_le` precondition of `post1_val_eq_amod_pow_s_pure_nat`
    when closing the `algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback`
    wrapper. -/
theorem algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s
    (a b : EvmWord) (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    (algCallAddbackBeqU4 a b).toNat * 2 ^ 256 ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
  -- Unfold the irreducible u4 to expose `(a.getLimbN 3) >>> antiShift`.
  rw [show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl]
  -- Setup: clz bounds and antiShift conversion.
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  -- u4 toNat = a3 / 2^(64-s).
  have h_u4_toNat : ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64)).toNat =
      (a.getLimbN 3).toNat / 2 ^ ((signExtend12 (0 : BitVec 12) -
        (clzResult (b.getLimbN 3)).1).toNat % 64) := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  -- val256(a) ≥ a3 * 2^192.
  have h_a3_val_ge :
      (a.getLimbN 3).toNat * 2 ^ 192 ≤
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) := by
    unfold val256; nlinarith [(a.getLimbN 0).isLt, (a.getLimbN 1).isLt, (a.getLimbN 2).isLt]
  -- u4 * 2^(64-s) ≤ a3 via Nat.div_mul_le_self.
  rw [h_u4_toNat, h_anti_eq]
  set s := (clzResult (b.getLimbN 3)).1.toNat
  have h_u4_mul : (a.getLimbN 3).toNat / 2 ^ (64 - s) * 2 ^ (64 - s)
      ≤ (a.getLimbN 3).toNat :=
    Nat.div_mul_le_self _ _
  -- Split 2^256 = 2^(64-s) * (2^192 * 2^s).
  rw [h_s_eq]
  have h_pow_split : (2 : Nat) ^ 256 = 2 ^ (64 - s) * (2 ^ 192 * 2 ^ s) := by
    rw [show (2 : Nat) ^ 192 * 2 ^ s = 2 ^ (192 + s) from by rw [pow_add],
        show (2 : Nat) ^ (64 - s) * 2 ^ (192 + s) = 2 ^ ((64 - s) + (192 + s)) from
          (pow_add 2 (64-s) (192+s)).symm,
        show (64 - s) + (192 + s) = 256 from by omega]
  rw [h_pow_split]
  calc (a.getLimbN 3).toNat / 2 ^ (64 - s) * (2 ^ (64 - s) * (2 ^ 192 * 2 ^ s))
      = ((a.getLimbN 3).toNat / 2 ^ (64 - s) * 2 ^ (64 - s)) * (2 ^ 192 * 2 ^ s) := by ring
    _ ≤ (a.getLimbN 3).toNat * (2 ^ 192 * 2 ^ s) :=
        Nat.mul_le_mul_right _ h_u4_mul
    _ = (a.getLimbN 3).toNat * 2 ^ 192 * 2 ^ s := by ring
    _ ≤ val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) * 2 ^ s :=
        Nat.mul_le_mul_right _ h_a3_val_ge

end EvmAsm.Evm64
