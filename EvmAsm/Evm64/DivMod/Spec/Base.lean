/-
  EvmAsm.Evm64.DivMod.Spec.Base

  Base stack-level specs for the 256-bit EVM DIV and MOD programs using
  evmWordIs.

  Currently covers:
  - Zero divisor path (b = 0): evm_div_bzero_stack_spec_within, evm_mod_bzero_stack_spec_within
  - Normal path (b ≠ 0): infrastructure complete; final composition pending.

  Stack-spec infrastructure (for the n=4 max+skip sub-path):

  * Precondition bundle: `divN4StackPre` (`modN4StackPre`) — `@[irreducible]`,
    bundles 9 registers + `evmWordIs sp a` + `evmWordIs (sp+32) b` +
    `divScratchValues` starting state. Unfold helpers: `_unfold`,
    `_unfold_atoms`.
  * Postcondition bundle: `divN4MaxSkipStackPost` — `@[irreducible]`, bundles
    9 registers (7 weakened to `regOwn`) + `evmWordIs sp a` (preserved) +
    `evmWordIs (sp+32) (EvmWord.div a b)` + `divScratchOwn`. Unfold helpers:
    `_unfold`, `_unfold_atoms`. The MOD counterpart lives in
    `Spec.ModMaxSkipV4` because it uses the v4 denormalization bridge.
  * Runtime condition wrappers (EvmWord form): `isMaxTrialN4Evm`,
    `isSkipBorrowN4MaxEvm`, `isCallTrialN4Evm`, `isSkipBorrowN4CallEvm`,
    `isAddbackBorrowN4CallEvm`. Each is a thin shim over the Word-level
    predicate plus a `_def` `rfl` lemma.
  * Semantic-correctness predicate: `n4MaxSkipSemanticHolds` — packages the
    un-normalized `mulsubN4`-carry hypothesis that
    `n4_max_skip_div_mod_getLimbN` consumes.
  * Weakener: `div_n4_max_skip_stack_weaken` — turns specific register values
    + `evmWordIs` operand atoms + `divScratchValues` into
    `divN4MaxSkipStackPost`. The MOD counterpart is
    `mod_n4_max_skip_stack_weaken` in `Spec.ModMaxSkipV4`.
  * `pcFree` instances for the stack-pre/post bundles defined here
    (`divN4StackPre`, `modN4StackPre`, `divN4MaxSkipStackPost`). `pcFree` instances for the post bundles
    defined in `Compose/Base.lean` (`divScratchOwn`, `denormDivPost`,
    `denormModPost`, `loopSetupPost`, `normBPost`) live next to their
    defs, as does `pcFree_fullDivN4MaxSkipPost` in
    `Compose/FullPathN4.lean`.
  * Pre-wrapper: `evm_div_n4_full_max_skip_stack_pre_spec` and its bundled
    variant `evm_div_n4_full_max_skip_stack_pre_spec_bundled` — wrap the
    limb-level full-path spec in the EvmWord-level pre shape.
  * V4 final stack specs are split out of this base module:
    `Spec.DivMaxSkipV4` exposes `evm_div_n4_max_skip_stack_spec_v4`, and
    `Spec.ModMaxSkipV4` exposes `evm_mod_n4_max_skip_stack_spec_within_v4`.
-/

import EvmAsm.Evm64.DivMod.Compose.Div128
import EvmAsm.Evm64.DivMod.Compose.Div128V4
import EvmAsm.Evm64.DivMod.Compose.Div128V5
import EvmAsm.Evm64.DivMod.Compose.Div128V5CodeBridge
import EvmAsm.Evm64.DivMod.Compose.FullPath
import EvmAsm.Evm64.DivMod.Compose.FullPathN1
import EvmAsm.Evm64.DivMod.Compose.FullPathN1NoNop
import EvmAsm.Evm64.DivMod.Compose.FullPathN2
import EvmAsm.Evm64.DivMod.Compose.FullPathN3
import EvmAsm.Evm64.DivMod.Compose.FullPathV4NoNop
import EvmAsm.Evm64.DivMod.Compose.ModFullPath
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN1
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN2
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN3
import EvmAsm.Evm64.DivMod.Compose.PhaseABNoNop
import EvmAsm.Evm64.DivMod.Compose.PhaseABV4NoNop
import EvmAsm.Evm64.DivMod.Compose.V4Code
import EvmAsm.Evm64.DivMod.Compose.V5Code
import EvmAsm.Evm64.DivMod.Compose.V5Code2
import EvmAsm.Evm64.DivMod.Compose.V5NoNop
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4
import EvmAsm.Evm64.DivMod.Compose.FullPathN4NoNop
-- `DivLimbBridge` reached transitively via `DivN4DoubleAddback →
-- DivN4Overestimate → DivAccumulate → DivRemainderBound →
-- DivAddbackLimb → DivMulSubLimb → DivLimbBridge`.
import EvmAsm.Evm64.EvmWordArith.SkipBorrowExtract
import EvmAsm.Evm64.EvmWordArith.ModBridgeAssemble
import EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddback
import EvmAsm.Evm64.EvmWordArith.MaxTrialVacuity
import EvmAsm.Evm64.DivMod.SpecPredicates

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero word_toNat_0)

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

/-- Stack-level postcondition shape for the n=4 DIV max+skip path.

    * `.x12 ↦ᵣ (sp+32)` — EVM stack pointer advanced past the popped second operand.
    * `regOwn` for every scratch register the program touches (`x1, x2, x5, x6,
      x7, x10, x11`). Caller has ownership but no knowledge of the final values.
    * `.x0 ↦ᵣ 0` — the zero register is preserved.
    * `evmWordIs sp a` — first operand preserved at its original location.
    * `evmWordIs (sp+32) (EvmWord.div a b)` — DIV result written over the second
      operand slot.
    * `divScratchOwn sp` — ownership of all 15 scratch cells, values unspecified.

    Paired with `evm_div_n4_max_skip_stack_spec` below and the v4 split
    theorem `evm_div_n4_max_skip_stack_spec_v4` in `Spec.DivMaxSkipV4`.
    Both are derived from the concrete `fullDivN4MaxSkipPost` via the
    `n4_max_skip_div_mod_getLimbN` semantic bridge +
    `divScratchValues_implies_divScratchOwn` weakener. -/
@[irreducible]
def divN4MaxSkipStackPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** regOwn .x9 ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
  divScratchOwn sp

/-- Stack-level precondition shape for the n=4 DIV path. Bundles the 9
    registers (including the pre-execution values of `x1, x2, x6, x7, x11`
    that the algorithm overwrites), the `evmWordIs sp a` / `evmWordIs (sp+32) b`
    operand slots, and the `divScratchValues` starting state into a single
    named assertion.

    Paired with `divN4MaxSkipStackPost` — the legacy
    `evm_div_n4_max_skip_stack_spec` below and the v4 split theorem
    `evm_div_n4_max_skip_stack_spec_v4` both have this as their precondition
    and that as their postcondition. -/
@[irreducible]
def divN4StackPre (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
  (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
  (.x11 ↦ᵣ v11) **
  evmWordIs sp a ** evmWordIs (sp + 32) b **
  divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem

theorem pcFree_divN4StackPre {sp : Word} {a b : EvmWord}
    {v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word} :
    (divN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem).pcFree := by
  delta divN4StackPre; pcFree

instance (sp : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word) :
    Assertion.PCFree (divN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem) :=
  ⟨pcFree_divN4StackPre⟩

/-- Named unfold for `divN4StackPre`. Restores access to the atomic
    components once `@[irreducible]` has made `delta` the only path in. -/
theorem divN4StackPre_unfold {sp : Word} {a b : EvmWord}
    {v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem : Word} :
    divN4StackPre sp a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem =
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
     (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     (.x11 ↦ᵣ v11) **
     evmWordIs sp a ** evmWordIs (sp + 32) b **
     divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem) := by
  delta divN4StackPre; rfl

/-- Call-trial counterpart to `divN4StackPre`. Identical to `divN4StackPre`
    except for the scratch bundle: uses `divScratchValuesCall` (19 cells —
    15 from `divScratchValues` plus 4 extra for the `div128`-subroutine
    call path) instead of `divScratchValues` (15 cells).

    Used as the precondition of the forthcoming
    `evm_div_n4_full_call_{skip,addback}_stack_pre_spec` theorems. -/
@[irreducible]
def divN4StackPreCall (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
  (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
  (.x11 ↦ᵣ v11) **
  evmWordIs sp a ** evmWordIs (sp + 32) b **
  divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0

theorem pcFree_divN4StackPreCall (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    (divN4StackPreCall sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0).pcFree := by
  delta divN4StackPreCall divScratchValuesCall; pcFree

instance (sp : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree (divN4StackPreCall sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0) :=
  ⟨pcFree_divN4StackPreCall sp a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0⟩

/-- Named unfold for `divN4StackPreCall`. -/
theorem divN4StackPreCall_unfold {sp : Word} {a b : EvmWord}
    {v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    divN4StackPreCall sp a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 =
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
     (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     (.x11 ↦ᵣ v11) **
     evmWordIs sp a ** evmWordIs (sp + 32) b **
     divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratch_un0) := by
  delta divN4StackPreCall; rfl

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
  (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
  (.x11 ↦ᵣ v11) **
  evmWordIs sp a ** evmWordIs (sp + 32) b **
  divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem

theorem pcFree_modN4StackPre {sp : Word} {a b : EvmWord}
    {v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word} :
    (modN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem).pcFree := by
  delta modN4StackPre; pcFree

instance (sp : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word) :
    Assertion.PCFree (modN4StackPre sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem) :=
  ⟨pcFree_modN4StackPre⟩

-- `modN4StackPreCall` (MOD-side call-trial pre-bundle) lives in
-- `DivMod/SpecCall.lean` to stay under the Spec.lean file-size guardrail.

/-- Named unfold for `divN4MaxSkipStackPost`. Restores access to the
    underlying definition once the `@[irreducible]` attribute has made
    `delta` the only way in at call sites. -/
theorem divN4MaxSkipStackPost_unfold {sp : Word} {a b : EvmWord} :
    divN4MaxSkipStackPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x9 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
     divScratchOwn sp) := by
  delta divN4MaxSkipStackPost; rfl

theorem pcFree_divN4MaxSkipStackPost {sp : Word} {a b : EvmWord} :
    (divN4MaxSkipStackPost sp a b).pcFree := by
  rw [divN4MaxSkipStackPost_unfold]; pcFree

instance (sp : Word) (a b : EvmWord) :
    Assertion.PCFree (divN4MaxSkipStackPost sp a b) :=
  ⟨pcFree_divN4MaxSkipStackPost⟩

/-- Weakening bridge from a concrete post state (specific register values +
    concrete scratch cells via `divScratchValues`) to `divN4MaxSkipStackPost`.
    Parallels the `mul_stack_weaken` helper in `Multiply/Spec.lean`. Weakens
    the 7 scratch registers from `regIs` to `regOwn` and the 15 scratch cells
    from `memIs` to `memOwn`; the two `evmWordIs` atoms, `.x12`, and `.x0`
    pass through unchanged. -/
theorem div_n4_max_skip_stack_weaken
    (sp : Word) (a b : EvmWord)
    {v1_p v2_p v5_p v6_p v7_p v10_p v11_p : Word}
    {q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
     shift_p n_p j_p : Word} :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x9 ↦ᵣ v1_p) ** (.x2 ↦ᵣ v2_p) **
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
  iterate 7 apply sepConj_mono (regIs_implies_regOwn _)
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
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 76 + 2 + 23 + 10)
      base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValues sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem)
      (fullDivN4MaxSkipPost sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_div_n4_full_max_skip_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem
    hbnz' hb3nz hshift_nz hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValues_unfold] at hp
      -- Normalize `sp + 0 ↦ₘ _` in the target side to `sp ↦ₘ _` so xperm finds it.
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

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
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 76 + 2 + 23 + 10)
      base (base + nopOff) (divCode base)
      (divN4StackPre sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem)
      (fullDivN4MaxSkipPost sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_div_n4_full_max_skip_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem hbnz hb3nz hshift_nz hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun _ hp => by rw [divN4StackPre_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

/-- Stack-level DIV spec for the zero divisor path: when b = 0, result is 0.
    Uses evmWordIs for the b-operand at sp+32. The a-operand at sp is untouched. -/
theorem evm_div_bzero_stack_spec_within (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (8 + 5) base (base + nopOff) (divCode base)
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
  have h_raw := evm_div_bzero_spec_within sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or
  simp only [hg0, hg1, hg2, hg3] at h_raw
  -- Bridge: div a 0 = 0, getLimbN (div a 0) k = 0 via the Nat-indexed lemma.
  have hr0 := EvmWord.div_getLimbN_zero_right a 0
  have hr1 := EvmWord.div_getLimbN_zero_right a 1
  have hr2 := EvmWord.div_getLimbN_zero_right a 2
  have hr3 := EvmWord.div_getLimbN_zero_right a 3
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp 0 0 0 0 0 hg0 hg1 hg2 hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      rw [evmWordIs_sp32_limbs_eq sp _ 0 0 0 0 hr0 hr1 hr2 hr3]
      have w0 := sepConj_mono_left (regIs_implies_regOwn .x5) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x10)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

/-- No-NOP variant of `evm_div_bzero_stack_spec_within`.

    This is the stack-level zero-divisor branch over `divCode_noNop`, used by
    the LP64-callable DIV wrapper whose return instruction replaces the old
    NOP at `base + nopOff`. -/
theorem evm_div_bzero_stack_spec_within_noNop (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (8 + 5) base (base + nopOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) (EvmWord.div a b)) := by
  subst hbz
  have hg0 := EvmWord.getLimbN_zero 0
  have hg1 := EvmWord.getLimbN_zero 1
  have hg2 := EvmWord.getLimbN_zero 2
  have hg3 := EvmWord.getLimbN_zero 3
  have hlimbs_or : (0 : EvmWord).getLimbN 0 ||| (0 : EvmWord).getLimbN 1 |||
      (0 : EvmWord).getLimbN 2 ||| (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
  have h_raw := evm_div_bzero_spec_within_noNop sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or
  simp only [hg0, hg1, hg2, hg3] at h_raw
  have hr0 := EvmWord.div_getLimbN_zero_right a 0
  have hr1 := EvmWord.div_getLimbN_zero_right a 1
  have hr2 := EvmWord.div_getLimbN_zero_right a 2
  have hr3 := EvmWord.div_getLimbN_zero_right a 3
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp 0 0 0 0 0 hg0 hg1 hg2 hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      rw [evmWordIs_sp32_limbs_eq sp _ 0 0 0 0 hr0 hr1 hr2 hr3]
      have w0 := sepConj_mono_left (regIs_implies_regOwn .x5) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x10)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

/-- v4 no-NOP variant of `evm_div_bzero_stack_spec_within`.

    This zero-divisor path only executes phaseA, the taken BEQ, and zeroPath;
    it is therefore valid over the shared v4 no-NOP code surface. -/
theorem evm_div_bzero_stack_spec_within_noNop_v4 (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (8 + 5) base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) (EvmWord.div a b)) := by
  subst hbz
  have hg0 := EvmWord.getLimbN_zero 0
  have hg1 := EvmWord.getLimbN_zero 1
  have hg2 := EvmWord.getLimbN_zero 2
  have hg3 := EvmWord.getLimbN_zero 3
  have hlimbs_or : (0 : EvmWord).getLimbN 0 ||| (0 : EvmWord).getLimbN 1 |||
      (0 : EvmWord).getLimbN 2 ||| (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
  have h_raw := evm_div_bzero_spec_within_noNop_v4 sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or
  simp only [hg0, hg1, hg2, hg3] at h_raw
  have hr0 := EvmWord.div_getLimbN_zero_right a 0
  have hr1 := EvmWord.div_getLimbN_zero_right a 1
  have hr2 := EvmWord.div_getLimbN_zero_right a 2
  have hr3 := EvmWord.div_getLimbN_zero_right a 3
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp 0 0 0 0 0 hg0 hg1 hg2 hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      rw [evmWordIs_sp32_limbs_eq sp _ 0 0 0 0 hr0 hr1 hr2 hr3]
      have w0 := sepConj_mono_left (regIs_implies_regOwn .x5) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x10)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

-- DIV n=4 call+skip full-path stack-pre wrappers live in `DivMod/SpecCall.lean`
-- to stay under the Spec.lean file-size guardrail.

-- ============================================================================
-- MOD: Zero divisor stack spec (b = 0 → result = 0)
-- ============================================================================

/-- Stack-level MOD spec for the zero divisor path: when b = 0, result is 0.
    Uses evmWordIs for the b-operand at sp+32. The a-operand at sp is untouched. -/
theorem evm_mod_bzero_stack_spec_within (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0) :
    cpsTripleWithin 13 base (base + nopOff) (modCode base)
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
  have h_raw := evm_mod_bzero_spec_within sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or
  simp only [hg0, hg1, hg2, hg3] at h_raw
  have hr0 := EvmWord.mod_getLimbN_zero_right a 0
  have hr1 := EvmWord.mod_getLimbN_zero_right a 1
  have hr2 := EvmWord.mod_getLimbN_zero_right a 2
  have hr3 := EvmWord.mod_getLimbN_zero_right a 3
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp 0 0 0 0 0 hg0 hg1 hg2 hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      rw [evmWordIs_sp32_limbs_eq sp _ 0 0 0 0 hr0 hr1 hr2 hr3]
      have w0 := sepConj_mono_left (regIs_implies_regOwn .x5) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x10)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

/-- Stack-level MOD bzero spec over `modCode_noNop`. Mirror of
    `evm_mod_bzero_stack_spec_within` with `modCode_noNop` instead of `modCode`.
    Used by `evm_mod_bzero_stack_spec_within_dispatch_noNop_preserving_x1_uni`
    in `DivMod/Spec/Unified.lean`. -/
theorem evm_mod_bzero_stack_spec_within_noNop (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0) :
    cpsTripleWithin 13 base (base + nopOff) (modCode_noNop base)
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
  have h_raw := evm_mod_bzero_spec_within_noNop sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or
  simp only [hg0, hg1, hg2, hg3] at h_raw
  have hr0 := EvmWord.mod_getLimbN_zero_right a 0
  have hr1 := EvmWord.mod_getLimbN_zero_right a 1
  have hr2 := EvmWord.mod_getLimbN_zero_right a 2
  have hr3 := EvmWord.mod_getLimbN_zero_right a 3
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp 0 0 0 0 0 hg0 hg1 hg2 hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      rw [evmWordIs_sp32_limbs_eq sp _ 0 0 0 0 hr0 hr1 hr2 hr3]
      have w0 := sepConj_mono_left (regIs_implies_regOwn .x5) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x10)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

/-- v4 no-NOP variant of `evm_mod_bzero_stack_spec_within_noNop`.

    This zero-divisor path only executes phaseA, the taken BEQ, and zeroPath;
    it is therefore valid over the shared v4 no-NOP code surface. -/
theorem evm_mod_bzero_stack_spec_within_noNop_v4 (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0) :
    cpsTripleWithin 13 base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
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
  have h_raw := evm_mod_bzero_spec_within_noNop_v4 sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or
  simp only [hg0, hg1, hg2, hg3] at h_raw
  have hr0 := EvmWord.mod_getLimbN_zero_right a 0
  have hr1 := EvmWord.mod_getLimbN_zero_right a 1
  have hr2 := EvmWord.mod_getLimbN_zero_right a 2
  have hr3 := EvmWord.mod_getLimbN_zero_right a 3
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp 0 0 0 0 0 hg0 hg1 hg2 hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      rw [evmWordIs_sp32_limbs_eq sp _ 0 0 0 0 hr0 hr1 hr2 hr3]
      have w0 := sepConj_mono_left (regIs_implies_regOwn .x5) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x10)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

-- ============================================================================
-- Sublemmas towards evm_div_n4_max_skip_stack_spec (reshape plan)
-- ============================================================================

/-- MOD output-slot semantic reshape ("S2" from the reshape plan): on the
    max+skip path, the mod result limbs equal the four `mulsubN4` outputs. -/
theorem output_slot_to_evmWordIs_mod_n4_max_skip {sp : Word} {a b : EvmWord}
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
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 76 + 2 + 23 + 10)
      base (base + nopOff) (divCode base)
      (divN4StackPre sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem)
      (divN4MaxSkipStackPost sp a b) := by
  have h_pre := evm_div_n4_full_max_skip_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem
    hbnz hb3nz hshift_nz hbltu hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3, _, _, _, _⟩ :=
    n4_max_skip_div_mod_getLimbN a b hb3nz hsem
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  -- Flatten the post: both unfolds in one `simp only` pass, which
  -- zeta-reduces through `fullDivN4MaxSkipPost_unfold`'s let-bindings
  -- (unlike `rw`, which gets blocked by them).
  simp only [fullDivN4MaxSkipPost_unfold, denormDivPost_unfold] at hq
  -- Apply the weakener — its input takes a specific explicit atom shape.
  apply div_n4_max_skip_stack_weaken sp a b h
  -- Unfold the `evmWordIs` / `divScratchValues` bundles on the goal side
  -- to expose matching atoms, then normalize addresses and use the
  -- semantic bridge to rewrite the four output-slot atoms.
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
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

end EvmAsm.Evm64
