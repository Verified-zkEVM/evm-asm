/-
  EvmAsm.Evm64.DivMod.Spec

  Stack-level specs for the 256-bit EVM DIV and MOD programs using evmWordIs.

  Currently covers:
  - Zero divisor path (b = 0): evm_div_bzero_stack_spec, evm_mod_bzero_stack_spec
  - Normal path (b ≠ 0): infrastructure complete; final composition pending.

  Stack-spec infrastructure (for the n=4 max+skip sub-path and its symmetric
  MOD counterpart):

  * Precondition bundle: `divN4StackPre` (`modN4StackPre`) — `@[irreducible]`,
    bundles 9 registers + `evmWordIs sp a` + `evmWordIs (sp+32) b` +
    `divScratchValues` starting state. Unfold helpers: `_unfold`,
    `_unfold_atoms`, `_unfold_atoms_right`.
  * Postcondition bundle: `divN4MaxSkipStackPost` (`modN4MaxSkipStackPost`) —
    `@[irreducible]`, bundles 9 registers (7 weakened to `regOwn`) +
    `evmWordIs sp a` (preserved) + `evmWordIs (sp+32) (EvmWord.div a b)`
    (`EvmWord.mod a b` for MOD) + `divScratchOwn`. Unfold helpers: `_unfold`,
    `_unfold_atoms`, `_unfold_atoms_right`.
  * Runtime condition wrappers (EvmWord form): `isMaxTrialN4Evm`,
    `isSkipBorrowN4MaxEvm`, `isCallTrialN4Evm`, `isSkipBorrowN4CallEvm`,
    `isAddbackBorrowN4CallEvm`. Each is a thin shim over the Word-level
    predicate plus a `_def` `rfl` lemma.
  * Semantic-correctness predicates: `n4MaxSkipSemanticHolds`,
    `n4MaxAddbackSemanticHolds`, `n4MaxDoubleAddbackSemanticHolds` — package
    the un-normalized `mulsubN4`-carry hypotheses that
    `n4_max_skip_div_mod_getLimbN` / `n4_max_addback_div_mod_getLimbN` /
    `n4_max_double_addback_div_mod_getLimbN` consume.
  * Weakeners: `div_n4_max_skip_stack_weaken`, `mod_n4_max_skip_stack_weaken` —
    turn specific register values + `evmWordIs` operand atoms + `divScratchValues`
    into `divN4MaxSkipStackPost` / `modN4MaxSkipStackPost`.
  * `pcFree` instances for the stack-pre/post bundles defined here
    (`divN4StackPre`, `modN4StackPre`, `divN4MaxSkipStackPost`,
    `modN4MaxSkipStackPost`). `pcFree` instances for the post bundles
    defined in `Compose/Base.lean` (`divScratchOwn`, `denormDivPost`,
    `denormModPost`, `loopSetupPost`, `normBPost`) live next to their
    defs, as does `pcFree_fullDivN4MaxSkipPost` in
    `Compose/FullPathN4.lean`.
  * Pre-wrapper: `evm_div_n4_full_max_skip_stack_pre_spec` and its bundled
    variant `evm_div_n4_full_max_skip_stack_pre_spec_bundled` — wrap the
    limb-level full-path spec in the EvmWord-level pre shape.
-/

import EvmAsm.Evm64.DivMod.Compose
import EvmAsm.Evm64.DivMod.Compose.FullPathN4
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Beq
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4
import EvmAsm.Evm64.EvmWordArith

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- `evmWordIs addr (EvmWord.div a 0) = evmWordIs addr 0`. Specialized
    rewrite for the zero-divisor path, bundling `evmWordIs_congr` +
    `EvmWord.div_zero_right` into a single named lemma. Saves the inline
    `rw [evmWordIs_congr addr (EvmWord.div_zero_right a)]` idiom at each
    bzero spec's postcondition site. -/
theorem evmWordIs_div_zero_right (addr : Word) (a : EvmWord) :
    evmWordIs addr (EvmWord.div a 0) = evmWordIs addr (0 : EvmWord) :=
  evmWordIs_congr addr (EvmWord.div_zero_right a)

/-- MOD counterpart of `evmWordIs_div_zero_right`. -/
theorem evmWordIs_mod_zero_right (addr : Word) (a : EvmWord) :
    evmWordIs addr (EvmWord.mod a 0) = evmWordIs addr (0 : EvmWord) :=
  evmWordIs_congr addr (EvmWord.mod_zero_right a)

/-- Full unfold of `evmWordIs addr (EvmWord.div a 0)` straight to four zero
    memIs atoms, bundling `evmWordIs_div_zero_right` + `evmWordIs_zero`
    into a single rewrite. -/
theorem evmWordIs_div_zero_right_atoms (addr : Word) (a : EvmWord) :
    evmWordIs addr (EvmWord.div a 0) =
    ((addr ↦ₘ (0 : Word)) ** ((addr + 8) ↦ₘ (0 : Word)) **
     ((addr + 16) ↦ₘ (0 : Word)) ** ((addr + 24) ↦ₘ (0 : Word))) := by
  rw [evmWordIs_div_zero_right, evmWordIs_zero]

/-- MOD counterpart of `evmWordIs_div_zero_right_atoms`. -/
theorem evmWordIs_mod_zero_right_atoms (addr : Word) (a : EvmWord) :
    evmWordIs addr (EvmWord.mod a 0) =
    ((addr ↦ₘ (0 : Word)) ** ((addr + 8) ↦ₘ (0 : Word)) **
     ((addr + 16) ↦ₘ (0 : Word)) ** ((addr + 24) ↦ₘ (0 : Word))) := by
  rw [evmWordIs_mod_zero_right, evmWordIs_zero]

-- ============================================================================
-- EvmWord-level runtime condition predicates for the n=4 max path
-- ============================================================================

-- The full-path DIV spec `evm_div_n4_full_max_skip_spec` takes runtime
-- conditions (`isMaxTrialN4`, `isSkipBorrowN4Max`) keyed off eight Word
-- limbs. For the EvmWord-level stack spec, it's more natural to express
-- these on `a b : EvmWord` directly — the wrappers below defer to the
-- Word-level predicates via `a.getLimbN k` / `b.getLimbN k`.

/-- Max trial quotient condition at n=4 in EvmWord form: `u4 ≥ b3'` after
    normalization, i.e., the algorithm uses the maximum trial quotient
    (`signExtend12 4095 = 2^64 - 1`). -/
def isMaxTrialN4Evm (a b : EvmWord) : Prop :=
  isMaxTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)

/-- Skip-addback condition at n=4 max in EvmWord form: the runtime borrow
    check `u4 < mulsubN4_c3` does not fire, so the algorithm skips the
    addback step and uses `qHat` as the quotient digit. -/
def isSkipBorrowN4MaxEvm (a b : EvmWord) : Prop :=
  isSkipBorrowN4Max (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isMaxTrialN4Evm_def (a b : EvmWord) :
    isMaxTrialN4Evm a b =
    isMaxTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) := rfl

theorem isSkipBorrowN4MaxEvm_def (a b : EvmWord) :
    isSkipBorrowN4MaxEvm a b =
    isSkipBorrowN4Max (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- Call trial condition at n=4 in EvmWord form: `u4 < b3'` after
    normalization, i.e., the max trial is too large so the algorithm falls
    through to `div128` for a tighter quotient. -/
def isCallTrialN4Evm (a b : EvmWord) : Prop :=
  isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)

/-- Skip-addback condition at n=4 call path in EvmWord form: the runtime
    borrow check does not fire, so the algorithm skips addback after the
    `div128`-computed trial quotient. -/
def isSkipBorrowN4CallEvm (a b : EvmWord) : Prop :=
  isSkipBorrowN4Call (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                     (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

/-- Addback-needed condition at n=4 call path in EvmWord form: the runtime
    borrow check fires, so the algorithm decrements the trial quotient and
    adds back `v` to the partial remainder. -/
def isAddbackBorrowN4CallEvm (a b : EvmWord) : Prop :=
  isAddbackBorrowN4Call (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isCallTrialN4Evm_def (a b : EvmWord) :
    isCallTrialN4Evm a b =
    isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) := rfl

theorem isSkipBorrowN4CallEvm_def (a b : EvmWord) :
    isSkipBorrowN4CallEvm a b =
    isSkipBorrowN4Call (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                       (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

theorem isAddbackBorrowN4CallEvm_def (a b : EvmWord) :
    isAddbackBorrowN4CallEvm a b =
    isAddbackBorrowN4Call (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- Addback-needed condition at n=4 max path in EvmWord form: the runtime
    borrow check fires (mulsub underflowed), so the algorithm decrements
    the max trial quotient and adds back `b'` to the partial remainder
    (possibly twice — see `isAddbackCarry2NzN4MaxAbEvm`). -/
def isAddbackBorrowN4MaxEvm (a b : EvmWord) : Prop :=
  isAddbackBorrowN4Max (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                       (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isAddbackBorrowN4MaxEvm_def (a b : EvmWord) :
    isAddbackBorrowN4MaxEvm a b =
    isAddbackBorrowN4Max (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                         (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- Double-addback carry2≠0 condition at n=4 max path in EvmWord form: after
    mulsub underflow + first-addback (carry1 = 0), the second addback fires
    (carry2 ≠ 0). Together with `isAddbackBorrowN4MaxEvm` this pins the
    algorithm to the double-addback branch. -/
def isAddbackCarry2NzN4MaxAbEvm (a b : EvmWord) : Prop :=
  isAddbackCarry2NzN4MaxAb (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                           (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isAddbackCarry2NzN4MaxAbEvm_def (a b : EvmWord) :
    isAddbackCarry2NzN4MaxAbEvm a b =
    isAddbackCarry2NzN4MaxAb (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                             (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl


-- ============================================================================
-- Stack-level post state for n=4 max-skip DIV
-- ============================================================================

/-- Semantic-correctness precondition for the n=4 max+skip sub-path: the
    mulsub carry on **un-normalized** `a`, `b` limbs with the maximum trial
    quotient (`signExtend12 4095 = 2^64 - 1`) is zero.

    This is what `n4_max_skip_div_mod_getLimbN` consumes to conclude
    `(EvmWord.div a b).getLimbN k` values. It is distinct from the runtime
    borrow check `isSkipBorrowN4MaxEvm` (which inspects the **normalized**
    mulsub carry), so the forthcoming stack spec takes both as separate
    hypotheses. Packaging the long equality behind a named predicate keeps
    the stack-spec signature readable. -/
def n4MaxSkipSemanticHolds (a b : EvmWord) : Prop :=
  (mulsubN4 (signExtend12 4095)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = 0

theorem n4MaxSkipSemanticHolds_def (a b : EvmWord) :
    n4MaxSkipSemanticHolds a b =
    ((mulsubN4 (signExtend12 4095)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = 0) :=
  rfl

/-- Semantic-correctness precondition for the n=4 max+addback sub-path: on
    **un-normalized** `a`, `b` limbs with the maximum trial quotient, the
    mulsub carry is `1` *and* the addback carry is `1`. Together these two
    facts feed `n4_max_addback_div_mod_getLimbN` to conclude the per-limb
    `EvmWord.div` / `EvmWord.mod` equalities. -/
def n4MaxAddbackSemanticHolds (a b : EvmWord) : Prop :=
  let ms := mulsubN4 (signExtend12 4095)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  ms.2.2.2.2 = 1 ∧
  addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = 1

theorem n4MaxAddbackSemanticHolds_def (a b : EvmWord) :
    n4MaxAddbackSemanticHolds a b =
    (let ms := mulsubN4 (signExtend12 4095)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
     ms.2.2.2.2 = 1 ∧
     addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
       (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = 1) :=
  rfl

/-- Semantic-correctness precondition for the n=4 max+double-addback sub-path:
    on **un-normalized** `a`, `b` limbs with the maximum trial quotient, the
    mulsub carry is `1`, the *first* addback carry is `0` (first addback didn't
    overflow the low 256 bits), and the *second* addback carry is `1`
    (second addback did overflow). Together these three facts feed
    `n4_max_double_addback_div_mod_getLimbN` to conclude the per-limb
    `EvmWord.div` / `EvmWord.mod` equalities for the double-addback path.

    This is distinct from `n4MaxAddbackSemanticHolds` (single-addback: c3=1 ∧
    carry1=1) and fires on the complementary algorithm branch where the first
    addback doesn't correct the borrow but the second one does. -/
def n4MaxDoubleAddbackSemanticHolds (a b : EvmWord) : Prop :=
  let ms := mulsubN4 (signExtend12 4095)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
  ms.2.2.2.2 = 1 ∧
  addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = 0 ∧
  (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).toNat = 1

theorem n4MaxDoubleAddbackSemanticHolds_def (a b : EvmWord) :
    n4MaxDoubleAddbackSemanticHolds a b =
    (let ms := mulsubN4 (signExtend12 4095)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
     let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
       (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
     ms.2.2.2.2 = 1 ∧
     addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
       (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = 0 ∧
     (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1
       (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).toNat = 1) :=
  rfl

/-- Stack-level postcondition shape for the n=4 DIV max+skip path.

    * `.x12 ↦ᵣ (sp+32)` — EVM stack pointer advanced past the popped second operand.
    * `regOwn` for every scratch register the program touches (`x1, x2, x5, x6,
      x7, x10, x11`). Caller has ownership but no knowledge of the final values.
    * `.x0 ↦ᵣ 0` — the zero register is preserved.
    * `evmWordIs sp a` — first operand preserved at its original location.
    * `evmWordIs (sp+32) (EvmWord.div a b)` — DIV result written over the second
      operand slot.
    * `divScratchOwn sp` — ownership of all 15 scratch cells, values unspecified.

    Paired with the forthcoming `evm_div_n4_max_skip_stack_spec` and derived
    from the concrete `fullDivN4MaxSkipPost` via the `n4_max_skip_div_mod_getLimbN`
    semantic bridge + `divScratchValues_implies_divScratchOwn` weakener. -/
@[irreducible]
def divN4MaxSkipStackPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
  divScratchOwn sp

/-- Stack-level precondition shape for the n=4 DIV path. Bundles the 9
    registers (including the pre-execution values of `x1, x2, x6, x7, x11`
    that the algorithm overwrites), the `evmWordIs sp a` / `evmWordIs (sp+32) b`
    operand slots, and the `divScratchValues` starting state into a single
    named assertion.

    Paired with `divN4MaxSkipStackPost` — the forthcoming
    `evm_div_n4_max_skip_stack_spec` will have this as its precondition and
    that as its postcondition. -/
@[irreducible]
def divN4StackPre (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
  (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
  (.x11 ↦ᵣ v11) **
  evmWordIs sp a ** evmWordIs (sp + 32) b **
  divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem

theorem pcFree_divN4StackPre (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word) :
    (divN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem).pcFree := by
  delta divN4StackPre; pcFree

instance (sp : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word) :
    Assertion.PCFree (divN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem) :=
  ⟨pcFree_divN4StackPre sp a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem⟩

/-- Named unfold for `divN4StackPre`. Restores access to the atomic
    components once `@[irreducible]` has made `delta` the only path in. -/
theorem divN4StackPre_unfold (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem : Word) :
    divN4StackPre sp a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem =
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
     (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     (.x11 ↦ᵣ v11) **
     evmWordIs sp a ** evmWordIs (sp + 32) b **
     divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem) := by
  delta divN4StackPre; rfl

/-- Full-depth unfold of `divN4StackPre`: expands the bundle, both `evmWordIs`
    atoms, and `divScratchValues` into primitive `regIs` / `memIs` atoms.
    Parallel to `divN4MaxSkipStackPost_unfold_atoms` — useful when proving
    the stack spec by unfolding the target and matching position-by-position
    against a concrete unfolded hypothesis. -/
theorem divN4StackPre_unfold_atoms (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem : Word) :
    divN4StackPre sp a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem =
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
     (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     (.x11 ↦ᵣ v11) **
     ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
      ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3)) **
     (((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
      ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3)) **
     (((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
      ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
      ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
      ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
      ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4016) ↦ₘ u5) **
      ((sp + signExtend12 4008) ↦ₘ u6) ** ((sp + signExtend12 4000) ↦ₘ u7) **
      ((sp + signExtend12 3992) ↦ₘ shiftMem) **
      ((sp + signExtend12 3984) ↦ₘ nMem) **
      ((sp + signExtend12 3976) ↦ₘ jMem))) := by
  rw [divN4StackPre_unfold, evmWordIs_sp_unfold, evmWordIs_sp32_unfold,
      divScratchValues_unfold]

/-- MOD-side parallel of `divN4StackPre`. Identical content — same registers,
    same operands, same scratch bundle. The name is kept distinct so the
    forthcoming MOD stack spec reads symmetrically with its DIV counterpart.
    Definitionally equal to `divN4StackPre`. -/
@[irreducible]
def modN4StackPre (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
  (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
  (.x11 ↦ᵣ v11) **
  evmWordIs sp a ** evmWordIs (sp + 32) b **
  divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem

theorem pcFree_modN4StackPre (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word) :
    (modN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem).pcFree := by
  delta modN4StackPre; pcFree

instance (sp : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word) :
    Assertion.PCFree (modN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem) :=
  ⟨pcFree_modN4StackPre sp a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem⟩

/-- Named unfold for `modN4StackPre`. Mirror of `divN4StackPre_unfold`. -/
theorem modN4StackPre_unfold (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem : Word) :
    modN4StackPre sp a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem =
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
     (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     (.x11 ↦ᵣ v11) **
     evmWordIs sp a ** evmWordIs (sp + 32) b **
     divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem) := by
  delta modN4StackPre; rfl

/-- Full-depth unfold of `modN4StackPre`: expands the bundle, both
    `evmWordIs` atoms, and `divScratchValues` into primitive `regIs` /
    `memIs` atoms. Mirror of `divN4StackPre_unfold_atoms`. -/
theorem modN4StackPre_unfold_atoms (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem : Word) :
    modN4StackPre sp a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem =
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
     (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     (.x11 ↦ᵣ v11) **
     ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
      ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3)) **
     (((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
      ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3)) **
     (((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
      ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
      ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
      ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
      ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4016) ↦ₘ u5) **
      ((sp + signExtend12 4008) ↦ₘ u6) ** ((sp + signExtend12 4000) ↦ₘ u7) **
      ((sp + signExtend12 3992) ↦ₘ shiftMem) **
      ((sp + signExtend12 3984) ↦ₘ nMem) **
      ((sp + signExtend12 3976) ↦ₘ jMem))) := by
  rw [modN4StackPre_unfold, evmWordIs_sp_unfold, evmWordIs_sp32_unfold,
      divScratchValues_unfold]

/-- Named unfold for `divN4MaxSkipStackPost`. Restores access to the
    underlying definition once the `@[irreducible]` attribute has made
    `delta` the only way in at call sites. -/
theorem divN4MaxSkipStackPost_unfold (sp : Word) (a b : EvmWord) :
    divN4MaxSkipStackPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
     divScratchOwn sp) := by
  delta divN4MaxSkipStackPost; rfl

/-- Full-depth unfold of `divN4MaxSkipStackPost`: expands the bundle, its
    inner `evmWordIs` atoms, and `divScratchOwn` all at once. The final RHS
    has only primitive assertion atoms (`regIs`, `regOwn`, `memIs`, `memOwn`),
    which is the shape a position-by-position weakening proof wants to match
    against. Companion to the partial `_unfold` variant; both coexist because
    some call sites want the `evmWordIs` / `divScratchOwn` bundles kept. -/
theorem divN4MaxSkipStackPost_unfold_atoms (sp : Word) (a b : EvmWord) :
    divN4MaxSkipStackPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
      ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3)) **
     (((sp + 32) ↦ₘ (EvmWord.div a b).getLimbN 0) **
      ((sp + 40) ↦ₘ (EvmWord.div a b).getLimbN 1) **
      ((sp + 48) ↦ₘ (EvmWord.div a b).getLimbN 2) **
      ((sp + 56) ↦ₘ (EvmWord.div a b).getLimbN 3)) **
     (memOwn (sp + signExtend12 4088) ** memOwn (sp + signExtend12 4080) **
      memOwn (sp + signExtend12 4072) ** memOwn (sp + signExtend12 4064) **
      memOwn (sp + signExtend12 4056) ** memOwn (sp + signExtend12 4048) **
      memOwn (sp + signExtend12 4040) ** memOwn (sp + signExtend12 4032) **
      memOwn (sp + signExtend12 4024) ** memOwn (sp + signExtend12 4016) **
      memOwn (sp + signExtend12 4008) ** memOwn (sp + signExtend12 4000) **
      memOwn (sp + signExtend12 3992) ** memOwn (sp + signExtend12 3984) **
      memOwn (sp + signExtend12 3976))) := by
  rw [divN4MaxSkipStackPost_unfold, evmWordIs_sp_unfold, evmWordIs_sp32_unfold,
      divScratchOwn_unfold]

theorem pcFree_divN4MaxSkipStackPost (sp : Word) (a b : EvmWord) :
    (divN4MaxSkipStackPost sp a b).pcFree := by
  rw [divN4MaxSkipStackPost_unfold]; pcFree

instance (sp : Word) (a b : EvmWord) :
    Assertion.PCFree (divN4MaxSkipStackPost sp a b) :=
  ⟨pcFree_divN4MaxSkipStackPost sp a b⟩

/-- Weakening bridge from a concrete post state (specific register values +
    concrete scratch cells via `divScratchValues`) to `divN4MaxSkipStackPost`.
    Parallels the `mul_stack_weaken` helper in `Multiply/Spec.lean`. Weakens
    the 7 scratch registers from `regIs` to `regOwn` and the 15 scratch cells
    from `memIs` to `memOwn`; the two `evmWordIs` atoms, `.x12`, and `.x0`
    pass through unchanged. -/
theorem div_n4_max_skip_stack_weaken
    (sp : Word) (a b : EvmWord)
    (v1_p v2_p v5_p v6_p v7_p v10_p v11_p : Word)
    (q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
     shift_p n_p j_p : Word) :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x1 ↦ᵣ v1_p) ** (.x2 ↦ᵣ v2_p) **
       (.x5 ↦ᵣ v5_p) ** (.x6 ↦ᵣ v6_p) ** (.x7 ↦ᵣ v7_p) **
       (.x10 ↦ᵣ v10_p) ** (.x11 ↦ᵣ v11_p) **
       (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
       divScratchValues sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p
         u5_p u6_p u7_p shift_p n_p j_p) h →
      divN4MaxSkipStackPost sp a b h := by
  intro h hp
  delta divN4MaxSkipStackPost
  refine sepConj_mono_right ?_ h hp
  iterate 7 apply sepConj_mono (regIs_implies_regOwn _ _)
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact divScratchValues_implies_divScratchOwn
    sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
    shift_p n_p j_p

/-- MOD counterpart of `divN4MaxSkipStackPost`: same structure, same register
    and scratch handling, but the second operand slot holds `EvmWord.mod a b`
    instead of `EvmWord.div a b`. Target shape for the forthcoming MOD stack
    spec on the n=4 max+skip sub-path. -/
@[irreducible]
def modN4MaxSkipStackPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
  divScratchOwn sp

/-- Named unfold for `modN4MaxSkipStackPost`. -/
theorem modN4MaxSkipStackPost_unfold (sp : Word) (a b : EvmWord) :
    modN4MaxSkipStackPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
     divScratchOwn sp) := by
  delta modN4MaxSkipStackPost; rfl

/-- Full-depth unfold of `modN4MaxSkipStackPost`: expands the bundle, its
    inner `evmWordIs` atoms, and `divScratchOwn` all at once. Mirror of
    `divN4MaxSkipStackPost_unfold_atoms`. -/
theorem modN4MaxSkipStackPost_unfold_atoms (sp : Word) (a b : EvmWord) :
    modN4MaxSkipStackPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
      ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3)) **
     (((sp + 32) ↦ₘ (EvmWord.mod a b).getLimbN 0) **
      ((sp + 40) ↦ₘ (EvmWord.mod a b).getLimbN 1) **
      ((sp + 48) ↦ₘ (EvmWord.mod a b).getLimbN 2) **
      ((sp + 56) ↦ₘ (EvmWord.mod a b).getLimbN 3)) **
     (memOwn (sp + signExtend12 4088) ** memOwn (sp + signExtend12 4080) **
      memOwn (sp + signExtend12 4072) ** memOwn (sp + signExtend12 4064) **
      memOwn (sp + signExtend12 4056) ** memOwn (sp + signExtend12 4048) **
      memOwn (sp + signExtend12 4040) ** memOwn (sp + signExtend12 4032) **
      memOwn (sp + signExtend12 4024) ** memOwn (sp + signExtend12 4016) **
      memOwn (sp + signExtend12 4008) ** memOwn (sp + signExtend12 4000) **
      memOwn (sp + signExtend12 3992) ** memOwn (sp + signExtend12 3984) **
      memOwn (sp + signExtend12 3976))) := by
  rw [modN4MaxSkipStackPost_unfold, evmWordIs_sp_unfold, evmWordIs_sp32_unfold,
      divScratchOwn_unfold]

/-- Mid-tree variant of `modN4MaxSkipStackPost_unfold_atoms`. Mirror of
    `divN4MaxSkipStackPost_unfold_atoms_right`. -/
theorem modN4MaxSkipStackPost_unfold_atoms_right (sp : Word) (a b : EvmWord)
    (Q : Assertion) :
    (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3)) **
      (((sp + 32) ↦ₘ (EvmWord.mod a b).getLimbN 0) **
       ((sp + 40) ↦ₘ (EvmWord.mod a b).getLimbN 1) **
       ((sp + 48) ↦ₘ (EvmWord.mod a b).getLimbN 2) **
       ((sp + 56) ↦ₘ (EvmWord.mod a b).getLimbN 3)) **
      (memOwn (sp + signExtend12 4088) ** memOwn (sp + signExtend12 4080) **
       memOwn (sp + signExtend12 4072) ** memOwn (sp + signExtend12 4064) **
       memOwn (sp + signExtend12 4056) ** memOwn (sp + signExtend12 4048) **
       memOwn (sp + signExtend12 4040) ** memOwn (sp + signExtend12 4032) **
       memOwn (sp + signExtend12 4024) ** memOwn (sp + signExtend12 4016) **
       memOwn (sp + signExtend12 4008) ** memOwn (sp + signExtend12 4000) **
       memOwn (sp + signExtend12 3992) ** memOwn (sp + signExtend12 3984) **
       memOwn (sp + signExtend12 3976))) ** Q) =
    (modN4MaxSkipStackPost sp a b ** Q) := by
  rw [modN4MaxSkipStackPost_unfold_atoms]

/-- Mid-tree variant of `modN4StackPre_unfold_atoms`: threads a remainder
    `Q` through the equality so `rw ←` can fold atoms back into the MOD stack
    pre bundle even when they sit mid-chain. Mirror of
    `divN4StackPre_unfold_atoms_right`. -/
theorem modN4StackPre_unfold_atoms_right (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word)
    (Q : Assertion) :
    (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
      (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
      (.x11 ↦ᵣ v11) **
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3)) **
      (((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
       ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3)) **
      (((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4016) ↦ₘ u5) **
       ((sp + signExtend12 4008) ↦ₘ u6) ** ((sp + signExtend12 4000) ↦ₘ u7) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem))) ** Q) =
    (modN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem ** Q) := by
  rw [modN4StackPre_unfold_atoms]

/-- Mid-tree variant of `divN4StackPre_unfold_atoms`: threads a remainder
    `Q` through the equality so `rw ←` can fold atoms back into the stack
    pre bundle even when they sit mid-chain. Parallel to the other `_right`
    fold variants. -/
theorem divN4StackPre_unfold_atoms_right (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word)
    (Q : Assertion) :
    (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
      (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
      (.x11 ↦ᵣ v11) **
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3)) **
      (((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
       ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3)) **
      (((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4016) ↦ₘ u5) **
       ((sp + signExtend12 4008) ↦ₘ u6) ** ((sp + signExtend12 4000) ↦ₘ u7) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem))) ** Q) =
    (divN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem ** Q) := by
  rw [divN4StackPre_unfold_atoms]

/-- Mid-tree variant of the `divN4MaxSkipStackPost_unfold_atoms` family:
    threads a remainder `Q` through the equality so `rw ←` can fold the
    atoms back into the stack post bundle **even when they sit mid-chain**.
    Parallel to `evmWordIs_sp_limbs_eq_right` / `divScratchValues_unfold_right`. -/
theorem divN4MaxSkipStackPost_unfold_atoms_right (sp : Word) (a b : EvmWord)
    (Q : Assertion) :
    (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3)) **
      (((sp + 32) ↦ₘ (EvmWord.div a b).getLimbN 0) **
       ((sp + 40) ↦ₘ (EvmWord.div a b).getLimbN 1) **
       ((sp + 48) ↦ₘ (EvmWord.div a b).getLimbN 2) **
       ((sp + 56) ↦ₘ (EvmWord.div a b).getLimbN 3)) **
      (memOwn (sp + signExtend12 4088) ** memOwn (sp + signExtend12 4080) **
       memOwn (sp + signExtend12 4072) ** memOwn (sp + signExtend12 4064) **
       memOwn (sp + signExtend12 4056) ** memOwn (sp + signExtend12 4048) **
       memOwn (sp + signExtend12 4040) ** memOwn (sp + signExtend12 4032) **
       memOwn (sp + signExtend12 4024) ** memOwn (sp + signExtend12 4016) **
       memOwn (sp + signExtend12 4008) ** memOwn (sp + signExtend12 4000) **
       memOwn (sp + signExtend12 3992) ** memOwn (sp + signExtend12 3984) **
       memOwn (sp + signExtend12 3976))) ** Q) =
    (divN4MaxSkipStackPost sp a b ** Q) := by
  rw [divN4MaxSkipStackPost_unfold_atoms]

theorem pcFree_modN4MaxSkipStackPost (sp : Word) (a b : EvmWord) :
    (modN4MaxSkipStackPost sp a b).pcFree := by
  rw [modN4MaxSkipStackPost_unfold]; pcFree

instance (sp : Word) (a b : EvmWord) :
    Assertion.PCFree (modN4MaxSkipStackPost sp a b) :=
  ⟨pcFree_modN4MaxSkipStackPost sp a b⟩

-- ============================================================================
-- pcFree for DivMod post bundles
-- ============================================================================

/-- MOD counterpart of `div_n4_max_skip_stack_weaken`. Same pattern, same
    register/memory weakenings — only the result-slot `evmWordIs` holds
    `EvmWord.mod a b` instead of `EvmWord.div a b`. -/
theorem mod_n4_max_skip_stack_weaken
    (sp : Word) (a b : EvmWord)
    (v1_p v2_p v5_p v6_p v7_p v10_p v11_p : Word)
    (q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
     shift_p n_p j_p : Word) :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x1 ↦ᵣ v1_p) ** (.x2 ↦ᵣ v2_p) **
       (.x5 ↦ᵣ v5_p) ** (.x6 ↦ᵣ v6_p) ** (.x7 ↦ᵣ v7_p) **
       (.x10 ↦ᵣ v10_p) ** (.x11 ↦ᵣ v11_p) **
       (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
       divScratchValues sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p
         u5_p u6_p u7_p shift_p n_p j_p) h →
      modN4MaxSkipStackPost sp a b h := by
  intro h hp
  delta modN4MaxSkipStackPost
  refine sepConj_mono_right ?_ h hp
  iterate 7 apply sepConj_mono (regIs_implies_regOwn _ _)
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact divScratchValues_implies_divScratchOwn
    sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
    shift_p n_p j_p

/-- EvmWord-level wrapper around `evm_div_n4_full_max_skip_spec`. Same
    guarantee (full-path DIV from `base` to `base + nopOff` on the n=4 max+skip
    sub-path), but with the operands bundled as `evmWordIs sp a` /
    `evmWordIs (sp+32) b` and the 15 scratch cells bundled as `divScratchValues`.
    The postcondition is still the concrete `fullDivN4MaxSkipPost` — turning
    that into `divN4MaxSkipStackPost` requires the semantic-correctness bridge
    (`hc3_zero`) which is threaded separately in the final stack spec. -/
theorem evm_div_n4_full_max_skip_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isMaxTrialN4Evm a b)
    (hborrow : isSkipBorrowN4MaxEvm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValues sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem)
      (fullDivN4MaxSkipPost sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or b).mp hbnz
  have hraw := evm_div_n4_full_max_skip_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem
    hbnz' hb3nz hshift_nz hbltu hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValues_unfold] at hp
      -- Normalize `sp + 0 ↦ₘ _` in the target side to `sp ↦ₘ _` so xperm finds it.
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Number of scratch memory cells the DIV/MOD program uses. Exposed as a
    named definition so clients can reason about the scratch-region size
    abstractly (e.g. for framing or sizing bounds) without poking into
    `divScratchValues` / `divScratchOwn`'s internals. -/
def divScratchCellCount : Nat := 15

/-- `divScratchCellCount` is concretely 15. Stated as an `rfl` theorem for
    convenient rewriting at call sites. -/
theorem divScratchCellCount_eq : divScratchCellCount = 15 := rfl

/-- `divScratchCellCount` is strictly positive. Useful for discharging
    non-emptiness side conditions when reasoning abstractly about the
    scratch region (e.g. in a size bound `sp + 32 * stack.length ≤
    sp + ... - 32 * divScratchCellCount`). -/
theorem divScratchCellCount_pos : 0 < divScratchCellCount := by decide

/-- Bundled version of `evm_div_n4_full_max_skip_stack_pre_spec`: takes the
    precondition as a single `divN4StackPre` atom. Thin wrapper — unfolds the
    bundle and defers to the unbundled spec. Useful when composing into the
    final `evm_div_n4_max_skip_stack_spec` where the callers think of the
    precondition as one named assertion. -/
theorem evm_div_n4_full_max_skip_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isMaxTrialN4Evm a b)
    (hborrow : isSkipBorrowN4MaxEvm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPre sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem)
      (fullDivN4MaxSkipPost sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_div_n4_full_max_skip_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem hbnz hb3nz hshift_nz hbltu hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [divN4StackPre_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

-- ============================================================================
-- DIV n=4 max+addback BEQ full-path stack-pre wrappers
-- ============================================================================

/-- EvmWord-level wrapper over `evm_div_n4_full_max_addback_beq_spec`: same
    shape as `evm_div_n4_full_max_skip_stack_pre_spec` but for the
    max+addback BEQ sub-path (double-addback included). The extra
    `hvalid : ValidMemRange sp 8` hypothesis is threaded through, along
    with all 20 individual `hv_*` access hypotheses and `hbltu`,
    `hcarry2_nz`, `hborrow`. The postcondition is the concrete
    `fullDivN4MaxAddbackBeqPost` — turning that into a stack post
    requires the semantic-correctness bridge (single-addback or
    double-addback) threaded separately in the final stack spec. -/
theorem evm_div_n4_full_max_addback_beq_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_j  : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (0 + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hbltu : isMaxTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4MaxAbEvm a b)
    (hborrow : isAddbackBorrowN4MaxEvm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValues sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem)
      (fullDivN4MaxAddbackBeqPost sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or b).mp hbnz
  have hraw := evm_div_n4_full_max_addback_beq_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem
    hbnz' hb3nz hshift_nz hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_uhi hv_ulo hv_vtop
    hbltu hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_div_n4_full_max_addback_beq_stack_pre_spec`:
    takes the precondition as a single `divN4StackPre` atom. Parallels
    `evm_div_n4_full_max_skip_stack_pre_spec_bundled`. -/
theorem evm_div_n4_full_max_addback_beq_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_j  : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (0 + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hbltu : isMaxTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4MaxAbEvm a b)
    (hborrow : isAddbackBorrowN4MaxEvm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPre sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem)
      (fullDivN4MaxAddbackBeqPost sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_div_n4_full_max_addback_beq_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem hbnz hb3nz hshift_nz hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_uhi hv_ulo hv_vtop
    hbltu hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [divN4StackPre_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

/-- Stack-level DIV spec for the zero divisor path: when b = 0, result is 0.
    Uses evmWordIs for the b-operand at sp+32. The a-operand at sp is untouched. -/
theorem evm_div_bzero_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) (EvmWord.div a b)) := by
  subst hbz
  -- Normalize (0 : EvmWord).getLimb k to (0 : Word)
  have hg0 := EvmWord.getLimbN_zero 0
  have hg1 := EvmWord.getLimbN_zero 1
  have hg2 := EvmWord.getLimbN_zero 2
  have hg3 := EvmWord.getLimbN_zero 3
  -- Get the limb-level zero-path spec
  have hlimbs_or : (0 : EvmWord).getLimbN 0 ||| (0 : EvmWord).getLimbN 1 |||
      (0 : EvmWord).getLimbN 2 ||| (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
  have h_raw := evm_div_bzero_spec sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or
  simp only [hg0, hg1, hg2, hg3] at h_raw
  -- Bridge: div a 0 = 0, getLimbN (div a 0) k = 0 via the Nat-indexed lemma.
  have hr0 := EvmWord.div_getLimbN_zero_right a 0
  have hr1 := EvmWord.div_getLimbN_zero_right a 1
  have hr2 := EvmWord.div_getLimbN_zero_right a 2
  have hr3 := EvmWord.div_getLimbN_zero_right a 3
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp 0 0 0 0 0 hg0 hg1 hg2 hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      rw [evmWordIs_sp32_limbs_eq sp _ 0 0 0 0 hr0 hr1 hr2 hr3]
      have w0 := sepConj_mono_left (regIs_implies_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

-- ============================================================================
-- MOD: Zero divisor stack spec (b = 0 → result = 0)
-- ============================================================================

/-- Stack-level MOD spec for the zero divisor path: when b = 0, result is 0.
    Uses evmWordIs for the b-operand at sp+32. The a-operand at sp is untouched. -/
theorem evm_mod_bzero_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) (EvmWord.mod a b)) := by
  subst hbz
  have hg0 := EvmWord.getLimbN_zero 0
  have hg1 := EvmWord.getLimbN_zero 1
  have hg2 := EvmWord.getLimbN_zero 2
  have hg3 := EvmWord.getLimbN_zero 3
  have hlimbs_or : (0 : EvmWord).getLimbN 0 ||| (0 : EvmWord).getLimbN 1 |||
      (0 : EvmWord).getLimbN 2 ||| (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
  have h_raw := evm_mod_bzero_spec sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or
  simp only [hg0, hg1, hg2, hg3] at h_raw
  have hr0 := EvmWord.mod_getLimbN_zero_right a 0
  have hr1 := EvmWord.mod_getLimbN_zero_right a 1
  have hr2 := EvmWord.mod_getLimbN_zero_right a 2
  have hr3 := EvmWord.mod_getLimbN_zero_right a 3
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp 0 0 0 0 0 hg0 hg1 hg2 hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      rw [evmWordIs_sp32_limbs_eq sp _ 0 0 0 0 hr0 hr1 hr2 hr3]
      have w0 := sepConj_mono_left (regIs_implies_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

/-- MOD mirror of `evm_div_n4_full_max_skip_stack_pre_spec`.

    EvmWord-level wrapper around `evm_mod_n4_full_max_skip_spec`. Same guarantee
    (full-path MOD from `base` to `base + nopOff` on the n=4 max+skip sub-path),
    but with the operands bundled as `evmWordIs sp a` / `evmWordIs (sp+32) b`
    and the 15 scratch cells bundled as `divScratchValues`. The postcondition
    is still the concrete `fullModN4MaxSkipPost` — turning that into
    `modN4MaxSkipStackPost` requires a denormalization bridge that's deferred
    to the forthcoming MOD stack spec. -/
theorem evm_mod_n4_full_max_skip_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isMaxTrialN4Evm a b)
    (hborrow : isSkipBorrowN4MaxEvm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValues sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem)
      (fullModN4MaxSkipPost sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or b).mp hbnz
  have hraw := evm_mod_n4_full_max_skip_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem
    hbnz' hb3nz hshift_nz hbltu hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled MOD version mirroring `evm_div_n4_full_max_skip_stack_pre_spec_bundled`:
    takes the precondition as a single `modN4StackPre` atom. -/
theorem evm_mod_n4_full_max_skip_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isMaxTrialN4Evm a b)
    (hborrow : isSkipBorrowN4MaxEvm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPre sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem)
      (fullModN4MaxSkipPost sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_mod_n4_full_max_skip_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem hbnz hb3nz hshift_nz hbltu hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [modN4StackPre_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

-- ============================================================================
-- Sublemmas towards evm_div_n4_max_skip_stack_spec (reshape plan)
-- ============================================================================

/-- Output-slot semantic reshape ("S2" from the reshape plan): the four
    output-slot atoms in `fullDivN4MaxSkipPost` carry the concrete values
    `signExtend12 4095 / 0 / 0 / 0`. Under the semantic precondition
    `n4MaxSkipSemanticHolds` (and shift non-zero), those values equal
    `(EvmWord.div a b).getLimbN 0..3`, so the four atoms fold into
    `evmWordIs (sp + 32) (EvmWord.div a b)`. -/
theorem output_slot_to_evmWordIs_div_n4_max_skip (sp : Word) (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0) (hsem : n4MaxSkipSemanticHolds a b) :
    (((sp + 32) ↦ₘ (signExtend12 4095 : Word)) **
     ((sp + 40) ↦ₘ (0 : Word)) **
     ((sp + 48) ↦ₘ (0 : Word)) **
     ((sp + 56) ↦ₘ (0 : Word))) =
    evmWordIs (sp + 32) (EvmWord.div a b) := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3, _, _, _, _⟩ :=
    n4_max_skip_div_mod_getLimbN a b hb3nz hsem
  rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
      hdiv0 hdiv1 hdiv2 hdiv3]

/-- MOD counterpart of `output_slot_to_evmWordIs_div_n4_max_skip`: on the
    max+skip path, the mod result limbs equal the four `mulsubN4` outputs. -/
theorem output_slot_to_evmWordIs_mod_n4_max_skip (sp : Word) (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0) (hsem : n4MaxSkipSemanticHolds a b) :
    let ms := mulsubN4 (signExtend12 4095)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (((sp + 32) ↦ₘ ms.1) **
     ((sp + 40) ↦ₘ ms.2.1) **
     ((sp + 48) ↦ₘ ms.2.2.1) **
     ((sp + 56) ↦ₘ ms.2.2.2.1)) =
    evmWordIs (sp + 32) (EvmWord.mod a b) := by
  obtain ⟨_, _, _, _, hmod0, hmod1, hmod2, hmod3⟩ :=
    n4_max_skip_div_mod_getLimbN a b hb3nz hsem
  intro _
  rw [evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _
      hmod0 hmod1 hmod2 hmod3]

-- ============================================================================
-- DIV: n=4 max+skip stack spec
-- ============================================================================

/-- EVM-stack-level DIV spec on the n=4 max+skip sub-path.

    Consumes runtime conditions (`isMaxTrialN4Evm`, `isSkipBorrowN4MaxEvm`),
    the semantic-correctness fact `n4MaxSkipSemanticHolds`, and the shift
    non-zero condition. Produces the clean
    `divN4StackPre` → `divN4MaxSkipStackPost` shape.

    Reduces to `evm_div_n4_full_max_skip_stack_pre_spec_bundled` + a
    postcondition reshape via `n4_max_skip_div_mod_getLimbN` and
    `div_n4_max_skip_stack_weaken`. See
    `project_div_n4_reshape_plan.md` for the sublemma decomposition. -/
theorem evm_div_n4_max_skip_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isMaxTrialN4Evm a b)
    (hborrow : isSkipBorrowN4MaxEvm a b)
    (hsem : n4MaxSkipSemanticHolds a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPre sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem)
      (divN4MaxSkipStackPost sp a b) := by
  have h_pre := evm_div_n4_full_max_skip_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem
    hbnz hb3nz hshift_nz hbltu hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3, _, _, _, _⟩ :=
    n4_max_skip_div_mod_getLimbN a b hb3nz hsem
  refine cpsTriple_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  -- Flatten the post: both unfolds in one `simp only` pass, which
  -- zeta-reduces through `fullDivN4MaxSkipPost_unfold`'s let-bindings
  -- (unlike `rw`, which gets blocked by them).
  simp only [fullDivN4MaxSkipPost_unfold, denormDivPost_unfold] at hq
  -- Apply the weakener — its input takes a specific explicit atom shape.
  apply div_n4_max_skip_stack_weaken sp a b _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  -- Unfold the `evmWordIs` / `divScratchValues` bundles on the goal side
  -- to expose matching atoms, then normalize addresses and use the
  -- semantic bridge to rewrite the four output-slot atoms.
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold sp a]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ (signExtend12 4095 : Word)) **
       ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) **
       ((sp + 56) ↦ₘ (0 : Word)))
      from by rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
                  hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValues_unfold]
  -- Normalize `sp + 0` on the hypothesis side to match the goal's `sp`.
  rw [word_add_zero] at hq
  xperm_hyp hq

-- ============================================================================
-- MOD: n=4 max+skip stack spec
-- ============================================================================

/-- EVM-stack-level MOD spec on the n=4 max+skip sub-path.

    Mirror of `evm_div_n4_max_skip_stack_spec` but for MOD. Takes the same
    five runtime + semantic conditions as DIV. The CLZ top-limb bound
    `b.getLimbN 3 < 2^(64 - clz(b.getLimbN 3))`, needed internally for
    the post reshape through the denormalization round-trip, is discharged
    via `clzResult_fst_top_bound`.

    Reduces to `evm_mod_n4_full_max_skip_stack_pre_spec_bundled` + a post
    reshape via `output_slot_to_evmWordIs_mod_n4_max_skip_denorm` and
    `mod_n4_max_skip_stack_weaken`. -/
theorem evm_mod_n4_max_skip_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isMaxTrialN4Evm a b)
    (hborrow : isSkipBorrowN4MaxEvm a b)
    (hsem : n4MaxSkipSemanticHolds a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPre sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem)
      (modN4MaxSkipStackPost sp a b) := by
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  have h_pre := evm_mod_n4_full_max_skip_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem
    hbnz hb3nz hshift_nz hbltu hborrow
  -- Shift bound: clzResult.1.toNat ≤ 63, and hshift_nz gives it > 0.
  have hshift_le_63 := clzResult_fst_toNat_le (b.getLimbN 3)
  have hshift_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    by_contra h
    push Not at h
    apply hshift_nz
    apply BitVec.eq_of_toNat_eq
    have h0 : (0 : Word).toNat = 0 := by decide
    omega
  have hshift_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have hmod_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  -- c3_n ≤ uTop from runtime skip borrow, specialized to our shift form.
  have hc3_le := EvmWord.c3_le_u_top_of_skip_borrow
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hborrow
  simp only [] at hc3_le
  -- Normalize `% 64` and `signExtend12 0 - shift` to the `(64 - s)` form
  -- the Lemma G adapter uses.
  have h0se12 : signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1 =
      -((clzResult (b.getLimbN 3)).1) := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    simp
  have hanti_toNat_mod :
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat := by
    rw [h0se12, BitVec.toNat_neg]
    have : ((clzResult (b.getLimbN 3)).1).toNat ≤ 2^64 := by
      have := ((clzResult (b.getLimbN 3)).1).isLt; omega
    have : ((clzResult (b.getLimbN 3)).1).toNat ≤ 63 := hshift_le_63
    omega
  rw [hmod_eq, hanti_toNat_mod] at hc3_le
  -- hsem unfolds to the un-normalized c3 = 0.
  have hc3_un : (mulsubN4 (signExtend12 4095)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = 0 := hsem
  -- Invoke the stack-spec adapter (Lemma G).
  have h_slot := EvmWord.output_slot_to_evmWordIs_mod_n4_max_skip_denorm sp a b
    hb3nz (clzResult (b.getLimbN 3)).1.toNat hshift_pos hshift_lt_64
    hb3_bound hc3_un hc3_le
  refine cpsTriple_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  simp only [fullModN4MaxSkipPost_unfold, denormModPost_unfold] at hq
  apply mod_n4_max_skip_stack_weaken sp a b _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  -- Expose address atoms on the goal side via unfolds.
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold sp a]
  -- Fold the four denorm output slots into `evmWordIs (sp+32) (EvmWord.mod a b)`.
  rw [show evmWordIs (sp + 32) (EvmWord.mod a b) = _ from h_slot.symm]
  rw [divScratchValues_unfold]
  -- Normalize `sp + 0` on the hypothesis side.
  rw [word_add_zero] at hq
  -- Also normalize `shift.toNat % 64` inside hq (the post uses `.toNat % 64`).
  simp only [hmod_eq, hanti_toNat_mod] at hq
  xperm_hyp hq

end EvmAsm.Evm64
