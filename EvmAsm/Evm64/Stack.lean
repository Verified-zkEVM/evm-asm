/-
  EvmAsm.Evm64.Stack

  Separation logic assertions for 256-bit EVM values stored as
  4 little-endian 64-bit limbs in consecutive doubleword-aligned memory.
-/

import EvmAsm.Evm64.Basic
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

theorem evmStackIs_nil (sp : Word) :
    evmStackIs sp [] = empAssertion := rfl

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
  rw [show (sp + 32 : Word) + 8 = sp + 40 from by bv_omega,
      show (sp + 32 : Word) + 16 = sp + 48 from by bv_omega,
      show (sp + 32 : Word) + 24 = sp + 56 from by bv_omega]

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
