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
    `n4MaxAddbackSemanticHolds` — package the un-normalized `mulsubN4`-carry
    hypotheses `n4_max_skip_div_mod_getLimbN` / `n4_max_addback_div_mod_getLimbN`
    consume.
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
import EvmAsm.Evm64.EvmWordArith

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

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
    addback step and uses `q_hat` as the quotient digit. -/
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
     shift_mem n_mem j_mem : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
  (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
  (.x11 ↦ᵣ v11) **
  evmWordIs sp a ** evmWordIs (sp + 32) b **
  divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shift_mem n_mem j_mem

theorem pcFree_divN4StackPre (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem : Word) :
    (divN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem).pcFree := by
  delta divN4StackPre; pcFree

instance (sp : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem : Word) :
    Assertion.PCFree (divN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem) :=
  ⟨pcFree_divN4StackPre sp a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem⟩

/-- Named unfold for `divN4StackPre`. Restores access to the atomic
    components once `@[irreducible]` has made `delta` the only path in. -/
theorem divN4StackPre_unfold (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shift_mem n_mem j_mem : Word) :
    divN4StackPre sp a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem =
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
     (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     (.x11 ↦ᵣ v11) **
     evmWordIs sp a ** evmWordIs (sp + 32) b **
     divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shift_mem n_mem j_mem) := by
  delta divN4StackPre; rfl

/-- Full-depth unfold of `divN4StackPre`: expands the bundle, both `evmWordIs`
    atoms, and `divScratchValues` into primitive `regIs` / `memIs` atoms.
    Parallel to `divN4MaxSkipStackPost_unfold_atoms` — useful when proving
    the stack spec by unfolding the target and matching position-by-position
    against a concrete unfolded hypothesis. -/
theorem divN4StackPre_unfold_atoms (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shift_mem n_mem j_mem : Word) :
    divN4StackPre sp a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem =
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
      ((sp + signExtend12 3992) ↦ₘ shift_mem) **
      ((sp + signExtend12 3984) ↦ₘ n_mem) **
      ((sp + signExtend12 3976) ↦ₘ j_mem))) := by
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
     shift_mem n_mem j_mem : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
  (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
  (.x11 ↦ᵣ v11) **
  evmWordIs sp a ** evmWordIs (sp + 32) b **
  divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shift_mem n_mem j_mem

theorem pcFree_modN4StackPre (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem : Word) :
    (modN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem).pcFree := by
  delta modN4StackPre; pcFree

instance (sp : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem : Word) :
    Assertion.PCFree (modN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem) :=
  ⟨pcFree_modN4StackPre sp a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem⟩

/-- Named unfold for `modN4StackPre`. Mirror of `divN4StackPre_unfold`. -/
theorem modN4StackPre_unfold (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shift_mem n_mem j_mem : Word) :
    modN4StackPre sp a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem =
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
     (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     (.x11 ↦ᵣ v11) **
     evmWordIs sp a ** evmWordIs (sp + 32) b **
     divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shift_mem n_mem j_mem) := by
  delta modN4StackPre; rfl

/-- Full-depth unfold of `modN4StackPre`: expands the bundle, both
    `evmWordIs` atoms, and `divScratchValues` into primitive `regIs` /
    `memIs` atoms. Mirror of `divN4StackPre_unfold_atoms`. -/
theorem modN4StackPre_unfold_atoms (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shift_mem n_mem j_mem : Word) :
    modN4StackPre sp a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem =
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
      ((sp + signExtend12 3992) ↦ₘ shift_mem) **
      ((sp + signExtend12 3984) ↦ₘ n_mem) **
      ((sp + signExtend12 3976) ↦ₘ j_mem))) := by
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
    (q0_p q1_p q2_p q3_p u0_p u1_p u2_p u3_p u4_p u5_p u6_p u7_p
     shift_p n_p j_p : Word) :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x1 ↦ᵣ v1_p) ** (.x2 ↦ᵣ v2_p) **
       (.x5 ↦ᵣ v5_p) ** (.x6 ↦ᵣ v6_p) ** (.x7 ↦ᵣ v7_p) **
       (.x10 ↦ᵣ v10_p) ** (.x11 ↦ᵣ v11_p) **
       (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
       divScratchValues sp q0_p q1_p q2_p q3_p u0_p u1_p u2_p u3_p u4_p
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
    sp q0_p q1_p q2_p q3_p u0_p u1_p u2_p u3_p u4_p u5_p u6_p u7_p
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
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem : Word)
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
       ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_mem))) ** Q) =
    (modN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem ** Q) := by
  rw [modN4StackPre_unfold_atoms]

/-- Mid-tree variant of `divN4StackPre_unfold_atoms`: threads a remainder
    `Q` through the equality so `rw ←` can fold atoms back into the stack
    pre bundle even when they sit mid-chain. Parallel to the other `_right`
    fold variants. -/
theorem divN4StackPre_unfold_atoms_right (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem : Word)
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
       ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_mem))) ** Q) =
    (divN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem ** Q) := by
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
    (q0_p q1_p q2_p q3_p u0_p u1_p u2_p u3_p u4_p u5_p u6_p u7_p
     shift_p n_p j_p : Word) :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x1 ↦ᵣ v1_p) ** (.x2 ↦ᵣ v2_p) **
       (.x5 ↦ᵣ v5_p) ** (.x6 ↦ᵣ v6_p) ** (.x7 ↦ᵣ v7_p) **
       (.x10 ↦ᵣ v10_p) ** (.x11 ↦ᵣ v11_p) **
       (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
       divScratchValues sp q0_p q1_p q2_p q3_p u0_p u1_p u2_p u3_p u4_p
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
    sp q0_p q1_p q2_p q3_p u0_p u1_p u2_p u3_p u4_p u5_p u6_p u7_p
    shift_p n_p j_p

/-- EvmWord-level wrapper around `evm_div_n4_full_max_skip_spec`. Same
    guarantee (full-path DIV from `base` to `base + nopOff` on the n=4 max+skip
    sub-path), but with the operands bundled as `evmWordIs sp a` /
    `evmWordIs (sp+32) b` and the 15 scratch cells bundled as `divScratchValues`.
    The postcondition is still the concrete `fullDivN4MaxSkipPost` — turning
    that into `divN4MaxSkipStackPost` requires the semantic-correctness bridge
    (`hc3_zero`) which is threaded separately in the final stack spec. -/
theorem evm_div_n4_full_max_skip_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7
     n_mem shift_mem j_mem : Word)
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
       (.x11 ↦ᵣ v11_old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValues sp q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old
         u5 u6 u7 shift_mem n_mem j_mem)
      (fullDivN4MaxSkipPost sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or b).mp hbnz
  have hraw := evm_div_n4_full_max_skip_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11_old
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7
    n_mem shift_mem j_mem
    hbnz' hb3nz hshift_nz hbltu hborrow
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValues_unfold] at hp
      -- Normalize `sp + 0 ↦ₘ _` in the target side to `sp ↦ₘ _` so xperm finds it.
      rw [show (sp + 0 : Word) = sp from by bv_omega]
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
     n_mem shift_mem j_mem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isMaxTrialN4Evm a b)
    (hborrow : isSkipBorrowN4MaxEvm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPre sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shift_mem n_mem j_mem)
      (fullDivN4MaxSkipPost sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_div_n4_full_max_skip_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    n_mem shift_mem j_mem hbnz hb3nz hshift_nz hbltu hborrow
  exact cpsTriple_consequence _ _ _ _ _ _ _
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
  exact cpsTriple_consequence _ _ _ _ _ _ _
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
  exact cpsTriple_consequence _ _ _ _ _ _ _
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

end EvmAsm.Evm64
