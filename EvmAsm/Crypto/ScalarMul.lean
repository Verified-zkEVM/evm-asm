/-
  EvmAsm.Crypto.ScalarMul

  The double-and-add scalar-multiplication skeleton (bead
  evm-asm-4ch8f.11.13, crypto-strategy §6 label `.11.9`): the MSB-first
  double-and-add ladder shape every guest curve scalar-mul routine
  implements (`secp256k1_scalar_mul` over the `0x803/0x804` accelerator
  handles, and the BN254/BLS12-381 G1 analogues of `.58c`), stated over an
  ABSTRACT `(add, zero, dbl)` triple so all three curves instantiate one
  correctness theorem.

  The software infinity flag: the guest keeps the identity out of the
  accelerator (the chord/tangent ids trap on `x₁ = x₂` / `y = 0`) by
  carrying a separate flag word next to the raw point buffer.  At spec
  level that flag IS the `Option` layer: instantiations take the carrier
  `α := Option β` with `zero := none` (exactly the `.38.1` reference's
  convention), and `add`/`dbl` are the software case-splits around the
  accelerator ops.  The skeleton never needs to know — `α` is abstract.

  Division of labor with `.38.1` (SpecRef/Secp256k1Recover.lean):
  * `.38.1`'s `scalarMulAux` is the LSB-first Nat reference recovery is
    specified against — a fuel-indexed, kernel-reducible fold.
  * The GUEST ladders are MSB-first.  `dblAdd` below is their shape; the
    bit-order bridge (`dblAdd_eq_binMulAux` + `scalarMulAux_eq_binMulAux`)
    is the `.11.9` deliverable that lets `.38b`/`.58c` state a guest
    triple's post as `dblAdd …` and rewrite it to the `.38.1` reference.

  What is (deliberately) hypothesis, not theorem: the abelian-monoid laws
  `AddLaws` for the instantiated `(add, zero)` — e.g. `pointAdd` on
  ON-CURVE points.  On the raw carrier `Option (Nat × Nat)` the laws are
  FALSE (the chord/tangent formulas are garbage off-curve), so no
  unconditional secp corollary is stated here; the per-curve consumer
  beads discharge `AddLaws` on their on-curve subtype (or reachable
  domain).  This is the additive analogue of the pow ladder's
  load-bearing `1 < m` gate (the `.11.5` corner class); the OTHER
  degenerate cases of that class — zero scalar, identity input point —
  are theorems here (`dblAdd_zero_scalar`, `dblAdd_zero_point`): the
  additive ladder starts at the true identity `zero`, so unlike the
  multiplicative ladder's unreduced `acc₀ = 1 (mod 1)` there is no
  modulus corner, and the identity is never silently dropped.

  Kernel KATs at the bottom pin `dblAdd` against `.38.1`'s
  `scalarMul` on real secp256k1 points (`decide +kernel`; a wrong bit
  order, skipped doubling, or dropped infinity flag fails them).
-/

import EvmAsm.Crypto.PowLadder
import EvmAsm.Stateless.SpecRef.Secp256k1Recover

namespace EvmAsm.Crypto

-- ============================================================================
-- The abstract group interface
-- ============================================================================

/-- The abelian-monoid laws an instantiation must supply for its
    `(add, zero)` pair (e.g. `pointAdd`/`none` restricted to on-curve
    points).  Deliberately a plain `Prop` structure over the carrier —
    no type-class machinery, matching the Nat-modular spec vocabulary
    (crypto-strategy §2). -/
structure AddLaws {α : Type _} (add : α → α → α) (zero : α) : Prop where
  zero_add : ∀ x, add zero x = x
  add_zero : ∀ x, add x zero = x
  assoc : ∀ x y z, add (add x y) z = add x (add y z)
  comm : ∀ x y, add x y = add y x

/-- Iterated addition — the abstract scalar multiplication `k · P` every
    ladder post is stated against. -/
def nsmul {α : Type _} (add : α → α → α) (zero : α) : Nat → α → α
  | 0, _ => zero
  | k + 1, P => add (nsmul add zero k P) P

@[simp] theorem nsmul_zero {α : Type _} (add : α → α → α) (zero : α)
    (P : α) : nsmul add zero 0 P = zero := rfl

theorem nsmul_succ {α : Type _} (add : α → α → α) (zero : α) (k : Nat)
    (P : α) : nsmul add zero (k + 1) P = add (nsmul add zero k P) P := rfl

theorem nsmul_one {α : Type _} {add : α → α → α} {zero : α}
    (h : AddLaws add zero) (P : α) : nsmul add zero 1 P = P :=
  h.zero_add P

/-- `(m + n) · P = m · P + n · P` (needs only `assoc` + `add_zero`). -/
theorem nsmul_add_distrib {α : Type _} {add : α → α → α} {zero : α}
    (h : AddLaws add zero) (m n : Nat) (P : α) :
    nsmul add zero (m + n) P
      = add (nsmul add zero m P) (nsmul add zero n P) := by
  induction n with
  | zero => exact (h.add_zero _).symm
  | succ n ih =>
      show add (nsmul add zero (m + n) P) P = _
      rw [ih, h.assoc]
      rfl

/-- `k · zero = zero`: the identity input point is preserved (the
    software infinity flag is never dropped). -/
theorem nsmul_zero_point {α : Type _} {add : α → α → α} {zero : α}
    (h : AddLaws add zero) (k : Nat) :
    nsmul add zero k zero = zero := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show add (nsmul add zero k zero) zero = zero
      rw [ih, h.add_zero]

/-- `k · (P + P) = (2k) · P`. -/
theorem nsmul_two_mul {α : Type _} {add : α → α → α} {zero : α}
    (h : AddLaws add zero) (k : Nat) (P : α) :
    nsmul add zero k (add P P) = nsmul add zero (2 * k) P := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show add (nsmul add zero k (add P P)) (add P P) = _
      rw [ih, show 2 * (k + 1) = (2 * k + 1) + 1 from by omega,
        nsmul_succ, nsmul_succ, h.assoc]

-- ============================================================================
-- The MSB-first double-and-add ladder (the guest shape)
-- ============================================================================

/-- One MSB-first double-and-add step over abstract `add`/`dbl`: double
    the accumulator, and add the base point iff the scalar bit is set —
    the loop body of every guest curve scalar-mul routine. -/
def dblAddStep {α : Type _} (add : α → α → α) (dbl : α → α)
    (P acc : α) (b : Bool) : α :=
  if b then add (dbl acc) P else dbl acc

/-- `i` MSB-first double-and-add steps over the big-endian scalar bytes
    `bs`, from `acc₀ = zero` (the software infinity flag: instantiations
    take `α := Option β`, `zero := none`).  The additive-group analogue
    of `Crypto.ladder`. -/
def dblAdd {α : Type _} (add : α → α → α) (zero : α) (dbl : α → α)
    (P : α) (bs : List (BitVec 8)) : Nat → α
  | 0 => zero
  | i + 1 => dblAddStep add dbl P (dblAdd add zero dbl P bs i) (beBit bs i)

/-- Peeling one bit off a right shift (additive copy of the pow-ladder's
    private helper). -/
private theorem shiftRight_pred (e k : Nat) (hk : 0 < k) :
    e >>> (k - 1) = 2 * (e >>> k) + (e.testBit (k - 1)).toNat := by
  have hsplit : 2 ^ k = 2 ^ (k - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hsplit,
    ← Nat.div_div_eq_div_mul, Nat.testBit_eq_decide_div_mod_eq]
  generalize e / 2 ^ (k - 1) = q
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> simp [h] <;> omega

/-- The ladder invariant: after `i` MSB-first steps the accumulator is
    the top-`i`-bits prefix of the scalar times `P`. -/
theorem dblAdd_inv {α : Type _} {add : α → α → α} {zero : α} {dbl : α → α}
    (h : AddLaws add zero) (hdbl : ∀ x, dbl x = add x x)
    (P : α) (bs : List (BitVec 8)) (i : Nat) (hi : i ≤ 8 * bs.length) :
    dblAdd add zero dbl P bs i
      = nsmul add zero (beBytesToNat bs >>> (8 * bs.length - i)) P := by
  induction i with
  | zero =>
      have h0 : beBytesToNat bs >>> (8 * bs.length - 0) = 0 := by
        rw [Nat.sub_zero, Nat.shiftRight_eq_div_pow]
        exact Nat.div_eq_of_lt (beBytesToNat_lt bs)
      rw [h0]
      rfl
  | succ i ih =>
      have hiN : i < 8 * bs.length := by omega
      have ihv := ih (by omega)
      have hstep : beBytesToNat bs >>> (8 * bs.length - (i + 1))
          = 2 * (beBytesToNat bs >>> (8 * bs.length - i))
            + ((beBytesToNat bs).testBit (8 * bs.length - 1 - i)).toNat := by
        have h1 := shiftRight_pred (beBytesToNat bs) (8 * bs.length - i)
          (by omega)
        have h2 : 8 * bs.length - (i + 1) = 8 * bs.length - i - 1 := by omega
        have h3 : 8 * bs.length - i - 1 = 8 * bs.length - 1 - i := by omega
        rw [h3] at h1
        rw [h2, h3, h1]
      have hbit := beBytesToNat_testBit bs i hiN
      show dblAddStep add dbl P (dblAdd add zero dbl P bs i) (beBit bs i) = _
      rw [hstep, ihv, ← hbit]
      cases hb : (beBytesToNat bs).testBit (8 * bs.length - 1 - i) with
      | false =>
          simp only [dblAddStep, Bool.false_eq_true, if_false,
            Bool.toNat_false, Nat.add_zero]
          rw [hdbl, Nat.two_mul, nsmul_add_distrib h]
      | true =>
          simp only [dblAddStep, if_true, Bool.toNat_true]
          rw [hdbl, nsmul_succ, Nat.two_mul, nsmul_add_distrib h]

/-- **The skeleton's headline post**: the full MSB-first double-and-add
    ladder over the big-endian scalar bytes computes `k · P` in the
    abstract group, `k = beBytesToNat bs` — every leading-zero bit is a
    harmless doubling of `zero`. -/
theorem dblAdd_correct {α : Type _} {add : α → α → α} {zero : α}
    {dbl : α → α}
    (h : AddLaws add zero) (hdbl : ∀ x, dbl x = add x x)
    (P : α) (bs : List (BitVec 8)) :
    dblAdd add zero dbl P bs (8 * bs.length)
      = nsmul add zero (beBytesToNat bs) P := by
  have hres := dblAdd_inv h hdbl P bs (8 * bs.length) (Nat.le_refl _)
  simpa using hres

/-- Zero scalar ⇒ the ladder returns the identity (never a garbage
    point) — one `.11.5`-class corner, closed. -/
theorem dblAdd_zero_scalar {α : Type _} {add : α → α → α} {zero : α}
    {dbl : α → α}
    (h : AddLaws add zero) (hdbl : ∀ x, dbl x = add x x)
    (P : α) (bs : List (BitVec 8)) (hz : beBytesToNat bs = 0) :
    dblAdd add zero dbl P bs (8 * bs.length) = zero := by
  rw [dblAdd_correct h hdbl, hz]
  rfl

/-- Identity input point ⇒ identity output (the software infinity flag
    survives the whole ladder) — the other `.11.5`-class corner. -/
theorem dblAdd_zero_point {α : Type _} {add : α → α → α} {zero : α}
    {dbl : α → α}
    (h : AddLaws add zero) (hdbl : ∀ x, dbl x = add x x)
    (bs : List (BitVec 8)) :
    dblAdd add zero dbl zero bs (8 * bs.length) = zero := by
  rw [dblAdd_correct h hdbl]
  exact nsmul_zero_point h _

-- ============================================================================
-- The LSB-first reference shape (the `.38.1` bridge)
-- ============================================================================

/-- Fuel-indexed LSB-first double-and-add — the `.38.1`
    `Secp256k1.scalarMulAux` shape, abstracted over the group op.
    `binMulAux add fuel k P acc = acc + k · P` for `k < 2^fuel`
    (`binMulAux_eq`). -/
def binMulAux {α : Type _} (add : α → α → α) : Nat → Nat → α → α → α
  | 0, _, _, acc => acc
  | fuel + 1, k, pt, acc =>
      if k = 0 then acc
      else
        binMulAux add fuel (k / 2) (add pt pt)
          (if k % 2 = 1 then add acc pt else acc)

/-- The LSB-first fold is `acc + k · P` (needs `comm`: the low-bit
    contributions are accumulated in the reverse group order). -/
theorem binMulAux_eq {α : Type _} {add : α → α → α} {zero : α}
    (h : AddLaws add zero) :
    ∀ (fuel k : Nat), k < 2 ^ fuel → ∀ (pt acc : α),
      binMulAux add fuel k pt acc = add acc (nsmul add zero k pt) := by
  intro fuel
  induction fuel with
  | zero =>
      intro k hk pt acc
      obtain rfl : k = 0 := by omega
      exact (h.add_zero acc).symm
  | succ fuel ih =>
      intro k hk pt acc
      by_cases hk0 : k = 0
      · subst hk0
        show acc = add acc (nsmul add zero 0 pt)
        exact (h.add_zero acc).symm
      · have hhalf : k / 2 < 2 ^ fuel := by
          have h2 : 2 ^ (fuel + 1) = 2 ^ fuel * 2 := Nat.pow_succ ..
          omega
        show (if k = 0 then acc else _) = _
        rw [if_neg hk0, ih (k / 2) hhalf (add pt pt) _,
          nsmul_two_mul h]
        rcases Nat.mod_two_eq_zero_or_one k with hpar | hpar
        · rw [if_neg (by omega), show 2 * (k / 2) = k from by omega]
        · rw [if_pos hpar, h.assoc]
          congr 1
          rw [h.comm]
          have hk' : k = 2 * (k / 2) + 1 := by omega
          have hs : nsmul add zero (2 * (k / 2) + 1) pt
              = nsmul add zero k pt := by rw [← hk']
          rw [← hs]
          exact (nsmul_succ ..).symm

/-- **The bit-order bridge** (`.11.9` → `.38.1`): the guest-shaped
    MSB-first ladder value equals the LSB-first reference fold started
    at the identity, for any sufficient fuel. -/
theorem dblAdd_eq_binMulAux {α : Type _} {add : α → α → α} {zero : α}
    {dbl : α → α}
    (h : AddLaws add zero) (hdbl : ∀ x, dbl x = add x x)
    (P : α) (bs : List (BitVec 8)) (fuel : Nat)
    (hfuel : beBytesToNat bs < 2 ^ fuel) :
    dblAdd add zero dbl P bs (8 * bs.length)
      = binMulAux add fuel (beBytesToNat bs) P zero := by
  rw [dblAdd_correct h hdbl, binMulAux_eq h fuel _ hfuel, h.zero_add]

/-- `.38.1`'s `scalarMulAux` IS `binMulAux` at `pointAdd`
    (definitional shape bridge, no group laws needed): a guest triple's
    `dblAdd` post rewrites to the recovery reference through this and
    `dblAdd_eq_binMulAux` once the consumer bead supplies `AddLaws` on
    its on-curve domain. -/
theorem scalarMulAux_eq_binMulAux :
    ∀ (fuel k : Nat) (pt acc : Option Stateless.SpecRef.Secp256k1.Point),
      Stateless.SpecRef.Secp256k1.scalarMulAux fuel k pt acc
        = binMulAux Stateless.SpecRef.Secp256k1.pointAdd fuel k pt acc := by
  intro fuel
  induction fuel with
  | zero => intro k pt acc; rfl
  | succ fuel ih =>
      intro k pt acc
      show (if k = 0 then acc else _) = (if k = 0 then acc else _)
      by_cases hk0 : k = 0
      · rw [if_pos hk0, if_pos hk0]
      · rw [if_neg hk0, if_neg hk0]
        exact ih ..

-- ============================================================================
-- Kernel-checked shape guards (secp256k1, against the `.38.1` reference)
-- ============================================================================

open Stateless.SpecRef.Secp256k1 in
/-- MSB ladder vs the `.38.1` LSB reference on a real point: `5 · G`
    (an asymmetric bit pattern — a reversed bit order fails). -/
example :
    dblAdd pointAdd (none : Option Point) (fun q => pointAdd q q)
      (some (gx, gy)) [0x05] 8
      = scalarMul 5 (some (gx, gy)) := by decide +kernel

open Stateless.SpecRef.Secp256k1 in
/-- Two-byte scalar `0x0123 · G`: exercises the byte boundary of the
    MSB bit fetch. -/
example :
    dblAdd pointAdd (none : Option Point) (fun q => pointAdd q q)
      (some (gx, gy)) [0x01, 0x23] 16
      = scalarMul 0x123 (some (gx, gy)) := by decide +kernel

open Stateless.SpecRef.Secp256k1 in
/-- Zero scalar returns the identity, not a garbage point. -/
example :
    dblAdd pointAdd (none : Option Point) (fun q => pointAdd q q)
      (some (gx, gy)) [0x00] 8
      = none := by decide +kernel

open Stateless.SpecRef.Secp256k1 in
/-- The software infinity flag survives: `k · 𝒪 = 𝒪`. -/
example :
    dblAdd pointAdd (none : Option Point) (fun q => pointAdd q q)
      none [0xA7] 8
      = none := by decide +kernel

end EvmAsm.Crypto
