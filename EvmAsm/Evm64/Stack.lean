/-
  EvmAsm.Evm64.Stack

  Separation logic assertions for 256-bit EVM values stored as
  4 little-endian 64-bit limbs in consecutive doubleword-aligned memory.
-/

import EvmAsm.Evm64.Basic
import EvmAsm.Evm64.SpAddr
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

open EvmWord

/-- Assert that 4 consecutive memory doublewords hold the limbs of an EvmWord.
    The limbs are stored little-endian: addr+0 is the LSB limb, addr+24 is the MSB limb. -/
def evmWordIs (addr : Word) (v : EvmWord) : Assertion :=
  (addr ↦ₘ v.getLimbN 0) **
  ((addr + 8) ↦ₘ v.getLimbN 1) **
  ((addr + 16) ↦ₘ v.getLimbN 2) **
  ((addr + 24) ↦ₘ v.getLimbN 3)

/-- Assert an EVM stack starting at sp. Each element is 32 bytes (4 × 8-byte limbs). -/
def evmStackIs (sp : Word) (values : List EvmWord) : Assertion :=
  match values with
  | [] => empAssertion
  | v :: vs => evmWordIs sp v ** evmStackIs (sp + 32) vs

theorem pcFree_evmWordIs (addr : Word) (v : EvmWord) :
    (evmWordIs addr v).pcFree := by
  unfold evmWordIs; pcFree

theorem pcFree_evmStackIs (sp : Word) (values : List EvmWord) :
    (evmStackIs sp values).pcFree := by
  induction values generalizing sp with
  | nil => exact pcFree_emp
  | cons v vs ih => exact pcFree_sepConj (pcFree_evmWordIs sp v) (ih (sp + 32))

instance (addr : Word) (v : EvmWord) : Assertion.PCFree (evmWordIs addr v) :=
  ⟨pcFree_evmWordIs addr v⟩

instance (sp : Word) (values : List EvmWord) : Assertion.PCFree (evmStackIs sp values) :=
  ⟨pcFree_evmStackIs sp values⟩

theorem evmStackIs_cons (sp : Word) (v : EvmWord) (vs : List EvmWord) :
    evmStackIs sp (v :: vs) = (evmWordIs sp v ** evmStackIs (sp + 32) vs) := rfl

/-- Mid-tree variant of `evmStackIs_cons`: threads a remainder `Q` through
    the equality so `rw ←` can fold `evmWordIs sp v ** evmStackIs (sp+32) vs`
    back into `evmStackIs sp (v :: vs)` even when those atoms sit in the
    middle of a longer sepConj chain. Parallels the `_right` family on
    `evmStackIs_{single,pair,triple,append}`. -/
theorem evmStackIs_cons_right (sp : Word) (v : EvmWord) (vs : List EvmWord)
    (Q : Assertion) :
    ((evmWordIs sp v ** evmStackIs (sp + 32) vs) ** Q) =
    (evmStackIs sp (v :: vs) ** Q) := rfl

theorem evmStackIs_nil (sp : Word) :
    evmStackIs sp [] = empAssertion := rfl

/-- Two-element stack: `evmStackIs sp [a, b]` unfolds to
    `evmWordIs sp a ** evmWordIs (sp + 32) b ** empAssertion`. The
    trailing `** empAssertion` comes from the single-element recursion
    hitting `evmStackIs_nil` — `sepConj_empAssertion_right` eliminates it
    at call sites. Provided as a named rewrite since the 2-element case
    is what DIV/MOD/MUL/ADD/etc. stack specs all consume. -/
theorem evmStackIs_cons_cons_nil (sp : Word) (a b : EvmWord) :
    evmStackIs sp [a, b] =
    (evmWordIs sp a ** evmWordIs (sp + 32) b ** empAssertion) := rfl

/-- Singleton stack: `evmStackIs sp [v]` unfolds to
    `evmWordIs sp v ** empAssertion`. Useful for post-pop states. -/
theorem evmStackIs_cons_nil (sp : Word) (v : EvmWord) :
    evmStackIs sp [v] = (evmWordIs sp v ** empAssertion) := rfl

/-- Three-element stack: `evmStackIs sp [a, b, c]` unfolds to nested
    `evmWordIs` atoms at `sp`, `sp+32`, `sp+64` plus `empAssertion`.
    Useful for trinary ops like ADDMOD / MULMOD. -/
theorem evmStackIs_cons_cons_cons_nil (sp : Word) (a b c : EvmWord) :
    evmStackIs sp [a, b, c] =
    (evmWordIs sp a ** evmWordIs (sp + 32) b **
     evmWordIs (sp + 32 + 32) c ** empAssertion) := rfl

/-- Two-element stack unfold without the trailing `empAssertion`:
    `evmStackIs sp [a, b] = evmWordIs sp a ** evmWordIs (sp + 32) b`.
    Derived from `evmStackIs_cons_cons_nil` by applying
    `sepConj_emp_right'`. Most binary-op stack specs want this cleaner
    2-atom form rather than the raw definition. -/
theorem evmStackIs_pair (sp : Word) (a b : EvmWord) :
    evmStackIs sp [a, b] = (evmWordIs sp a ** evmWordIs (sp + 32) b) := by
  rw [evmStackIs_cons_cons_nil, sepConj_emp_right']

/-- Symmetric companion of `evmStackIs_pair`: singleton stack collapses to a
    single `evmWordIs`. -/
theorem evmStackIs_single (sp : Word) (v : EvmWord) :
    evmStackIs sp [v] = evmWordIs sp v := by
  rw [evmStackIs_cons_nil, sepConj_emp_right']

/-- Three-element stack unfold without the trailing `empAssertion`:
    `evmStackIs sp [a, b, c] = evmWordIs sp a ** evmWordIs (sp+32) b **
    evmWordIs (sp+64) c`. Derived from `evmStackIs_cons_cons_cons_nil` by
    applying `sepConj_emp_right'`. Ternary-op stack specs (ADDMOD /
    MULMOD) want this cleaner 3-atom form rather than the raw definition.
    Parallels `evmStackIs_pair` / `evmStackIs_single`. -/
theorem evmStackIs_triple (sp : Word) (a b c : EvmWord) :
    evmStackIs sp [a, b, c] =
    (evmWordIs sp a ** evmWordIs (sp + 32) b **
     evmWordIs (sp + 32 + 32) c) := by
  rw [evmStackIs_cons_cons_cons_nil, sepConj_emp_right']

/-- Flattened-offset variant of `evmStackIs_triple`: the third address is
    `sp + 64` instead of `sp + 32 + 32`. Those are *not* definitionally equal
    for `Word = BitVec 64` (the addition associates around `sp`), so call
    sites that want the flat `sp + 64` form reach for this variant. -/
theorem evmStackIs_triple_flat (sp : Word) (a b c : EvmWord) :
    evmStackIs sp [a, b, c] =
    (evmWordIs sp a ** evmWordIs (sp + 32) b ** evmWordIs (sp + 64) c) := by
  rw [evmStackIs_triple]
  rw [show (sp + 32 + 32 : Word) = sp + 64 from by bv_omega]

/-- Mid-tree variant of `evmStackIs_pair`: threads a remainder `Q` so
    `rw ←` can fold two `evmWordIs` atoms into an `evmStackIs [a, b]`
    bundle **even when they sit in the middle of a longer sepConj chain**.
    Parallels the `_right` family on `evmWordIs_sp*_limbs_eq`. -/
theorem evmStackIs_pair_right (sp : Word) (a b : EvmWord) (Q : Assertion) :
    ((evmWordIs sp a ** evmWordIs (sp + 32) b) ** Q) =
    (evmStackIs sp [a, b] ** Q) := by
  rw [evmStackIs_pair]

/-- Mid-tree variant of `evmStackIs_single`: threads a remainder `Q` so
    `rw ←` can fold a single `evmWordIs` atom into an `evmStackIs [v]`
    bundle mid-chain. Parallel to `evmStackIs_pair_right`. -/
theorem evmStackIs_single_right (sp : Word) (v : EvmWord) (Q : Assertion) :
    (evmWordIs sp v ** Q) = (evmStackIs sp [v] ** Q) := by
  rw [evmStackIs_single]

/-- Mid-tree variant of `evmStackIs_triple`: threads a remainder `Q` so
    `rw ←` can fold three `evmWordIs` atoms into an `evmStackIs [a, b, c]`
    bundle mid-chain. Third address is in the non-flat `sp + 32 + 32`
    form — use `evmStackIs_triple_flat_right` for the `sp + 64` form. -/
theorem evmStackIs_triple_right (sp : Word) (a b c : EvmWord) (Q : Assertion) :
    ((evmWordIs sp a ** evmWordIs (sp + 32) b **
      evmWordIs (sp + 32 + 32) c) ** Q) =
    (evmStackIs sp [a, b, c] ** Q) := by
  rw [evmStackIs_triple]

/-- Mid-tree variant of `evmStackIs_triple_flat`: same as
    `evmStackIs_triple_right` but with the flat `sp + 64` offset for the
    third address. -/
theorem evmStackIs_triple_flat_right (sp : Word) (a b c : EvmWord)
    (Q : Assertion) :
    ((evmWordIs sp a ** evmWordIs (sp + 32) b **
      evmWordIs (sp + 64) c) ** Q) =
    (evmStackIs sp [a, b, c] ** Q) := by
  rw [evmStackIs_triple_flat]

-- ============================================================================
-- evmWordIs unfold and limb-equality bridges
-- ============================================================================

/-- Unfold `evmWordIs sp v` into four limb-level memory atoms at
    `sp, sp+8, sp+16, sp+24`. Trivial rewrite of the definition; provided as a
    named lemma for readability at call sites in stack-level specs. -/
theorem evmWordIs_sp_unfold (sp : Word) (v : EvmWord) :
    evmWordIs sp v =
    ((sp ↦ₘ v.getLimbN 0) ** ((sp + 8) ↦ₘ v.getLimbN 1) **
     ((sp + 16) ↦ₘ v.getLimbN 2) ** ((sp + 24) ↦ₘ v.getLimbN 3)) := rfl

/-- Unfold `evmWordIs (sp+32) v` into four limb-level memory atoms at the
    absolute stack addresses `sp+32, sp+40, sp+48, sp+56`. Bridges the
    separation-logic `evmWordIs` predicate and the raw limb atoms that the
    limb-level specs produce for the `b`-operand on the EVM stack. -/
theorem evmWordIs_sp32_unfold (sp : Word) (v : EvmWord) :
    evmWordIs (sp + 32) v =
    (((sp + 32) ↦ₘ v.getLimbN 0) ** ((sp + 40) ↦ₘ v.getLimbN 1) **
     ((sp + 48) ↦ₘ v.getLimbN 2) ** ((sp + 56) ↦ₘ v.getLimbN 3)) := by
  unfold evmWordIs
  rw [spAddr32_8, spAddr32_16, spAddr32_24]

/-- Unfold `evmWordIs (sp+64) v` into four limb-level memory atoms at the
    absolute stack addresses `sp+64, sp+72, sp+80, sp+88`. Third-slot
    counterpart to `evmWordIs_sp32_unfold` — useful for ternary-op stack
    specs (ADDMOD / MULMOD) whose third operand lives at `sp + 64`. -/
theorem evmWordIs_sp64_unfold (sp : Word) (v : EvmWord) :
    evmWordIs (sp + 64) v =
    (((sp + 64) ↦ₘ v.getLimbN 0) ** ((sp + 72) ↦ₘ v.getLimbN 1) **
     ((sp + 80) ↦ₘ v.getLimbN 2) ** ((sp + 88) ↦ₘ v.getLimbN 3)) := by
  unfold evmWordIs
  rw [spAddr64_8, spAddr64_16, spAddr64_24]

/-- Rewrite `evmWordIs sp v` to four limb atoms given explicit getLimbN
    equalities. Decouples the caller's representation of `v` from the limb
    form — works uniformly whether the equalities come from
    `getLimbN_fromLimbs_*`, per-op bridge lemmas, or `by decide` facts. -/
theorem evmWordIs_sp_limbs_eq (sp : Word) (v : EvmWord) (w0 w1 w2 w3 : Word)
    (h0 : v.getLimbN 0 = w0) (h1 : v.getLimbN 1 = w1)
    (h2 : v.getLimbN 2 = w2) (h3 : v.getLimbN 3 = w3) :
    evmWordIs sp v =
    ((sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
     ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3)) := by
  rw [evmWordIs_sp_unfold, h0, h1, h2, h3]

/-- Rewrite `evmWordIs (sp+32) v` to four limb atoms given explicit getLimbN
    equalities. Companion to `evmWordIs_sp_limbs_eq` for the `b`-operand slot. -/
theorem evmWordIs_sp32_limbs_eq (sp : Word) (v : EvmWord) (w0 w1 w2 w3 : Word)
    (h0 : v.getLimbN 0 = w0) (h1 : v.getLimbN 1 = w1)
    (h2 : v.getLimbN 2 = w2) (h3 : v.getLimbN 3 = w3) :
    evmWordIs (sp + 32) v =
    (((sp + 32) ↦ₘ w0) ** ((sp + 40) ↦ₘ w1) **
     ((sp + 48) ↦ₘ w2) ** ((sp + 56) ↦ₘ w3)) := by
  rw [evmWordIs_sp32_unfold, h0, h1, h2, h3]

/-- Rewrite `evmWordIs (sp+64) v` to four limb atoms given explicit getLimbN
    equalities. Third-slot companion to `evmWordIs_sp32_limbs_eq`. -/
theorem evmWordIs_sp64_limbs_eq (sp : Word) (v : EvmWord) (w0 w1 w2 w3 : Word)
    (h0 : v.getLimbN 0 = w0) (h1 : v.getLimbN 1 = w1)
    (h2 : v.getLimbN 2 = w2) (h3 : v.getLimbN 3 = w3) :
    evmWordIs (sp + 64) v =
    (((sp + 64) ↦ₘ w0) ** ((sp + 72) ↦ₘ w1) **
     ((sp + 80) ↦ₘ w2) ** ((sp + 88) ↦ₘ w3)) := by
  rw [evmWordIs_sp64_unfold, h0, h1, h2, h3]

/-- Mid-tree variant of `evmWordIs_sp_limbs_eq`: fold four limb atoms into
    `evmWordIs sp v` **even when they sit in the middle of a sepConj chain**,
    by explicitly threading the rest of the chain (`Q`) through the equality.

    The plain `evmWordIs_sp_limbs_eq`'s RHS is a four-atom right-terminal
    sub-tree; `rw ←` finds it only when the last of those four atoms has no
    right neighbor. When the four atoms live mid-chain (e.g. in the unfolded
    `fullDivN4MaxSkipPost`'s post), Lean's syntactic matcher can't find that
    sub-tree — folding fails. This variant makes the "rest of chain" explicit
    so the pattern `atoms ** Q` matches wherever the atoms appear. -/
theorem evmWordIs_sp_limbs_eq_right (sp : Word) (v : EvmWord) (w0 w1 w2 w3 : Word)
    (Q : Assertion)
    (h0 : v.getLimbN 0 = w0) (h1 : v.getLimbN 1 = w1)
    (h2 : v.getLimbN 2 = w2) (h3 : v.getLimbN 3 = w3) :
    ((sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
     ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3) ** Q) =
    (evmWordIs sp v ** Q) := by
  rw [evmWordIs_sp_limbs_eq sp v w0 w1 w2 w3 h0 h1 h2 h3]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

/-- Mid-tree variant of `evmWordIs_sp32_limbs_eq`. Same purpose as
    `evmWordIs_sp_limbs_eq_right` but for the `b`-operand slot at `sp+32`. -/
theorem evmWordIs_sp32_limbs_eq_right (sp : Word) (v : EvmWord) (w0 w1 w2 w3 : Word)
    (Q : Assertion)
    (h0 : v.getLimbN 0 = w0) (h1 : v.getLimbN 1 = w1)
    (h2 : v.getLimbN 2 = w2) (h3 : v.getLimbN 3 = w3) :
    (((sp + 32) ↦ₘ w0) ** ((sp + 40) ↦ₘ w1) **
     ((sp + 48) ↦ₘ w2) ** ((sp + 56) ↦ₘ w3) ** Q) =
    (evmWordIs (sp + 32) v ** Q) := by
  rw [evmWordIs_sp32_limbs_eq sp v w0 w1 w2 w3 h0 h1 h2 h3]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

/-- Mid-tree variant of `evmWordIs_sp64_limbs_eq`. Third-slot companion
    to `evmWordIs_sp_limbs_eq_right` / `evmWordIs_sp32_limbs_eq_right`,
    for ternary-op stack specs (ADDMOD / MULMOD) whose third operand
    lives at `sp + 64`. -/
theorem evmWordIs_sp64_limbs_eq_right (sp : Word) (v : EvmWord) (w0 w1 w2 w3 : Word)
    (Q : Assertion)
    (h0 : v.getLimbN 0 = w0) (h1 : v.getLimbN 1 = w1)
    (h2 : v.getLimbN 2 = w2) (h3 : v.getLimbN 3 = w3) :
    (((sp + 64) ↦ₘ w0) ** ((sp + 72) ↦ₘ w1) **
     ((sp + 80) ↦ₘ w2) ** ((sp + 88) ↦ₘ w3) ** Q) =
    (evmWordIs (sp + 64) v ** Q) := by
  rw [evmWordIs_sp64_limbs_eq sp v w0 w1 w2 w3 h0 h1 h2 h3]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

/-- `evmWordIs addr (0 : EvmWord)` unfolds to four zero-valued memIs atoms.
    Thin wrapper around `evmWordIs_sp_limbs_eq` / the definitional unfold
    specialized to `v = 0` — saves callers from inlining four
    `(0 : EvmWord).getLimbN k = 0` facts on every zero-path spec. Applies at
    arbitrary `addr`, so it covers both the `sp` and `sp+32` positions uniformly. -/
theorem evmWordIs_zero (addr : Word) :
    evmWordIs addr (0 : EvmWord) =
    ((addr ↦ₘ (0 : Word)) ** ((addr + 8) ↦ₘ (0 : Word)) **
     ((addr + 16) ↦ₘ (0 : Word)) ** ((addr + 24) ↦ₘ (0 : Word))) := by
  unfold evmWordIs
  rw [EvmWord.getLimbN_zero 0, EvmWord.getLimbN_zero 1,
      EvmWord.getLimbN_zero 2, EvmWord.getLimbN_zero 3]

/-- `evmWordIs addr (1 : EvmWord)` unfolds to one non-zero memIs atom
    (at the LSB) and three zero memIs atoms (at the higher limbs).
    Thin wrapper around the definitional unfold specialized to `v = 1` —
    saves callers from inlining four `(1 : EvmWord).getLimbN k` facts
    on every IsZero-path spec. Applies at arbitrary `addr`. -/
theorem evmWordIs_one (addr : Word) :
    evmWordIs addr (1 : EvmWord) =
    ((addr ↦ₘ (1 : Word)) ** ((addr + 8) ↦ₘ (0 : Word)) **
     ((addr + 16) ↦ₘ (0 : Word)) ** ((addr + 24) ↦ₘ (0 : Word))) := by
  unfold evmWordIs
  rw [EvmWord.getLimbN_one_zero, EvmWord.getLimbN_one_one,
      EvmWord.getLimbN_one_two, EvmWord.getLimbN_one_three]

/-- `evmWordIs addr (EvmWord.fromLimbs (fun _ => w))` unfolds to four
    identical-valued memIs atoms. Specializes the generic
    `evmWordIs_sp_limbs_eq` to the uniform-limb constant case; covers
    both the all-zero (`evmWordIs_zero`) and all-ones (e.g. `-1` in
    two's complement) patterns uniformly. -/
theorem evmWordIs_fromLimbs_const (addr : Word) (w : Word) :
    evmWordIs addr (EvmWord.fromLimbs (fun _ => w)) =
    ((addr ↦ₘ w) ** ((addr + 8) ↦ₘ w) **
     ((addr + 16) ↦ₘ w) ** ((addr + 24) ↦ₘ w)) := by
  unfold evmWordIs
  rw [EvmWord.getLimbN_fromLimbs_const_0, EvmWord.getLimbN_fromLimbs_const_1,
      EvmWord.getLimbN_fromLimbs_const_2, EvmWord.getLimbN_fromLimbs_const_3]

/-- Mid-tree variant of `evmWordIs_fromLimbs_const`: threads a remainder
    `Q` so `rw ←` can fold four identical-valued memIs atoms back into
    `evmWordIs addr (fromLimbs (fun _ => w))` even when they sit in the
    middle of a longer sepConj chain. -/
theorem evmWordIs_fromLimbs_const_right (addr : Word) (w : Word) (Q : Assertion) :
    ((addr ↦ₘ w) ** ((addr + 8) ↦ₘ w) **
     ((addr + 16) ↦ₘ w) ** ((addr + 24) ↦ₘ w) ** Q) =
    (evmWordIs addr (EvmWord.fromLimbs (fun _ => w)) ** Q) := by
  rw [evmWordIs_fromLimbs_const]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

/-- Mid-tree variant of `evmWordIs_zero`: threads a remainder `Q` so
    `rw ←` can fold four zero memIs atoms back into `evmWordIs addr 0`
    even when they sit in the middle of a longer sepConj chain. -/
theorem evmWordIs_zero_right (addr : Word) (Q : Assertion) :
    ((addr ↦ₘ (0 : Word)) ** ((addr + 8) ↦ₘ (0 : Word)) **
     ((addr + 16) ↦ₘ (0 : Word)) ** ((addr + 24) ↦ₘ (0 : Word)) ** Q) =
    (evmWordIs addr (0 : EvmWord) ** Q) := by
  rw [evmWordIs_zero]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

/-- Mid-tree variant of `evmWordIs_one`: threads a remainder `Q` so
    `rw ←` can fold `(addr ↦ₘ 1) ** (addr+8 ↦ₘ 0) ** (addr+16 ↦ₘ 0) **
    (addr+24 ↦ₘ 0)` back into `evmWordIs addr 1` mid-chain. -/
theorem evmWordIs_one_right (addr : Word) (Q : Assertion) :
    ((addr ↦ₘ (1 : Word)) ** ((addr + 8) ↦ₘ (0 : Word)) **
     ((addr + 16) ↦ₘ (0 : Word)) ** ((addr + 24) ↦ₘ (0 : Word)) ** Q) =
    (evmWordIs addr (1 : EvmWord) ** Q) := by
  rw [evmWordIs_one]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

-- ============================================================================
-- Shared infrastructure for stack operation specs
-- ============================================================================

@[simp] theorem EvmWord.getLimb_zero (i : Fin 4) : (0 : EvmWord).getLimb i = 0 := by
  have h : ∀ j : Fin 4, (0 : EvmWord).getLimb j = 0 := by decide
  exact h i

@[simp] theorem signExtend12_neg32 : signExtend12 (-32 : BitVec 12) = (-32 : Word) := by
  decide

/-- Sign-extend a small non-negative 12-bit value to 64 bits.
    The MSB is clear when m < 2^11 = 2048, so signExtend = zeroExtend = identity. -/
theorem signExtend12_ofNat_small (m : Nat) (hm : m < 2048) :
    signExtend12 (BitVec.ofNat 12 m) = BitVec.ofNat 64 m := by
  unfold signExtend12
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact BitVec.setWidth_ofNat_of_le_of_lt (by omega) (by omega)
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp [BitVec.toNat_ofNat]; omega

/-- Concatenation: `evmStackIs sp (xs ++ ys)` splits into `xs` at `sp` and
    `ys` at `sp + 32 * xs.length`. Companion to `evmStackIs_split_at` —
    where `split_at` isolates the kth element, `append` composes two
    contiguous stack segments. Useful for "preserve some cells, append
    a new element" stack transitions (PUSH / stack extension specs). -/
theorem evmStackIs_append (sp : Word) (xs ys : List EvmWord) :
    evmStackIs sp (xs ++ ys) =
    (evmStackIs sp xs ** evmStackIs (sp + BitVec.ofNat 64 (xs.length * 32)) ys) := by
  induction xs generalizing sp with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_mul,
               evmStackIs_nil, sepConj_emp_left']
    rw [show (BitVec.ofNat 64 0 : Word) = 0 from rfl]
    rw [show sp + (0 : Word) = sp from by bv_omega]
  | cons v vs ih =>
    have hshift : sp + (32 : Word) + BitVec.ofNat 64 (vs.length * 32) =
                  sp + BitVec.ofNat 64 ((vs.length + 1) * 32) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    simp only [List.cons_append, evmStackIs_cons, List.length_cons]
    rw [ih (sp + 32), hshift, sepConj_assoc']

/-- Snoc: `evmStackIs sp (xs ++ [v]) = evmStackIs sp xs **
    evmWordIs (sp + 32 * xs.length) v`. Specialized corollary of
    `evmStackIs_append` with `ys = [v]` — PUSH-style stack extensions
    that tack exactly one element onto the top reach for this variant. -/
theorem evmStackIs_snoc (sp : Word) (xs : List EvmWord) (v : EvmWord) :
    evmStackIs sp (xs ++ [v]) =
    (evmStackIs sp xs ** evmWordIs (sp + BitVec.ofNat 64 (xs.length * 32)) v) := by
  rw [evmStackIs_append, evmStackIs_single]

/-- Mid-tree variant of `evmStackIs_append`: threads a remainder `Q` so
    `rw ←` can fold two contiguous `evmStackIs` segments back into a single
    `evmStackIs sp (xs ++ ys)` bundle even when they sit in the middle of a
    longer sepConj chain. Parallels the `_right` family on the other
    `evmStackIs` unfolds. -/
theorem evmStackIs_append_right (sp : Word) (xs ys : List EvmWord)
    (Q : Assertion) :
    ((evmStackIs sp xs **
      evmStackIs (sp + BitVec.ofNat 64 (xs.length * 32)) ys) ** Q) =
    (evmStackIs sp (xs ++ ys) ** Q) := by
  rw [evmStackIs_append]

/-- Split evmStackIs at position k: extract the kth element (0-indexed). -/
theorem evmStackIs_split_at (sp : Word) (stack : List EvmWord) (k : Nat)
    (hk : k < stack.length) :
    evmStackIs sp stack =
      (evmStackIs sp (stack.take k) **
       evmWordIs (sp + BitVec.ofNat 64 (k * 32)) (stack[k]'hk) **
       evmStackIs (sp + BitVec.ofNat 64 ((k + 1) * 32)) (stack.drop (k + 1))) := by
  induction k generalizing sp stack with
  | zero =>
    cases stack with
    | nil => simp at hk
    | cons v vs =>
      simp only [Nat.zero_mul, List.take_zero,
                 List.drop_succ_cons, List.drop_zero, List.getElem_cons_zero,
                 evmStackIs_cons, evmStackIs_nil, sepConj_emp_left', BitVec.add_zero]
      congr 1
  | succ k ih =>
    cases stack with
    | nil => simp at hk
    | cons v vs =>
      have hk' : k < vs.length := by simp at hk; omega
      have a1 : sp + (32 : Word) + BitVec.ofNat 64 (k * 32) =
                sp + BitVec.ofNat 64 ((k + 1) * 32) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have a2 : sp + (32 : Word) + BitVec.ofNat 64 ((k + 1) * 32) =
                sp + BitVec.ofNat 64 ((k + 2) * 32) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [evmStackIs_cons, ih (sp + 32) vs hk', a1, a2]
      simp only [List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ]
      simp only [evmStackIs_cons, sepConj_assoc']

end EvmAsm.Evm64
