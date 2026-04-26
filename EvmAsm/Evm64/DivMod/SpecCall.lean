-- file-size-exception: tracked by #66 / #61 (call-trial DIV+MOD specs in progress; further split deferred until both stack specs land).
/-
  EvmAsm.Evm64.DivMod.SpecCall

  Call-trial precondition bundles for the 256-bit EVM DIV and MOD
  programs. Extracted from `Spec.lean` to stay under the 1500-line
  file-size guardrail.

  The call-trial variants use `divScratchValuesCall` (19 cells — the
  base `divScratchValues` 15 cells plus 4 extras for the `div128`
  subroutine call path). Used as preconditions of the forthcoming
  `evm_{div,mod}_n4_full_call_{skip,addback}_stack_pre_spec` theorems.

  `divN4StackPreCall` sits next to `divN4StackPre` in `Spec.lean`; this
  file adds the MOD-side counterpart `modN4StackPreCall`.
-/

import EvmAsm.Evm64.DivMod.Spec
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4Shift0
import EvmAsm.Evm64.EvmWordArith.Div128Shift0
import EvmAsm.Evm64.EvmWordArith.AddbackBorrowExtract

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)

/-- Call-trial counterpart to `modN4StackPre`. Identical to `modN4StackPre`
    except the scratch bundle: uses `divScratchValuesCall` (19 cells)
    instead of `divScratchValues` (15 cells).

    Used as the precondition of the forthcoming
    `evm_mod_n4_full_call_{skip,addback}_stack_pre_spec` theorems.
    Definitionally equal to `divN4StackPreCall`. -/
@[irreducible]
def modN4StackPreCall (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
  (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
  (.x11 ↦ᵣ v11) **
  evmWordIs sp a ** evmWordIs (sp + 32) b **
  divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0

theorem pcFree_modN4StackPreCall (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    (modN4StackPreCall sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0).pcFree := by
  delta modN4StackPreCall divScratchValuesCall; pcFree

instance (sp : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree (modN4StackPreCall sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0) :=
  ⟨pcFree_modN4StackPreCall sp a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0⟩

/-- Named unfold for `modN4StackPreCall`. Mirror of `divN4StackPreCall_unfold`. -/
theorem modN4StackPreCall_unfold {sp : Word} {a b : EvmWord}
    {v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    modN4StackPreCall sp a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 =
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
     (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     (.x11 ↦ᵣ v11) **
     evmWordIs sp a ** evmWordIs (sp + 32) b **
     divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratch_un0) := by
  delta modN4StackPreCall; rfl

/-- Call-trial counterpart to `divN4MaxSkipStackPost`. Identical content
    except for the scratch ownership: uses `divScratchOwnCall` (19 cells)
    instead of `divScratchOwn` (15 cells), reflecting the 4 extra scratch
    slots used by the `div128` subroutine call path.

    Paired with `divN4StackPreCall` for the forthcoming
    `evm_div_n4_call_skip_stack_spec`. -/
@[irreducible]
def divN4CallSkipStackPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
  divScratchOwnCall sp

/-- Named unfold for `divN4CallSkipStackPost`. Mirror of
    `divN4MaxSkipStackPost_unfold` but with `divScratchOwnCall`. -/
theorem divN4CallSkipStackPost_unfold {sp : Word} {a b : EvmWord} :
    divN4CallSkipStackPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
     divScratchOwnCall sp) := by
  delta divN4CallSkipStackPost; rfl

theorem pcFree_divN4CallSkipStackPost (sp : Word) (a b : EvmWord) :
    (divN4CallSkipStackPost sp a b).pcFree := by
  rw [divN4CallSkipStackPost_unfold, divScratchOwnCall_unfold,
      divScratchOwn_unfold]
  pcFree

instance (sp : Word) (a b : EvmWord) :
    Assertion.PCFree (divN4CallSkipStackPost sp a b) :=
  ⟨pcFree_divN4CallSkipStackPost sp a b⟩

/-- Call-trial counterpart to `modN4MaxSkipStackPost`. Identical content
    except for the scratch ownership: uses `divScratchOwnCall` (19 cells).
    Paired with `modN4StackPreCall` for the forthcoming
    `evm_mod_n4_call_skip_stack_spec`. -/
@[irreducible]
def modN4CallSkipStackPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
  divScratchOwnCall sp

/-- Named unfold for `modN4CallSkipStackPost`. -/
theorem modN4CallSkipStackPost_unfold {sp : Word} {a b : EvmWord} :
    modN4CallSkipStackPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
     divScratchOwnCall sp) := by
  delta modN4CallSkipStackPost; rfl

theorem pcFree_modN4CallSkipStackPost (sp : Word) (a b : EvmWord) :
    (modN4CallSkipStackPost sp a b).pcFree := by
  rw [modN4CallSkipStackPost_unfold, divScratchOwnCall_unfold,
      divScratchOwn_unfold]
  pcFree

instance (sp : Word) (a b : EvmWord) :
    Assertion.PCFree (modN4CallSkipStackPost sp a b) :=
  ⟨pcFree_modN4CallSkipStackPost sp a b⟩

/-- Call-path counterpart to `div_n4_max_skip_stack_weaken`. Weakens a
    concrete post state (19-cell `divScratchValuesCall` + 7 register
    values) to `divN4CallSkipStackPost`. Structural mirror of the
    max-path weakener, with `divScratchValuesCall_implies_divScratchOwnCall`
    handling the 19-cell scratch weakening (4 extra cells beyond the 15
    of `divScratchValues`).

    Used by the forthcoming `evm_div_n4_call_skip_stack_spec` — the
    remaining semantic bridge (connecting `div128Quot`'s output to
    `(EvmWord.div a b).getLimbN 0..3`) depends on Knuth B.  -/
theorem div_n4_call_skip_stack_weaken
    (sp : Word) (a b : EvmWord)
    {v1_p v2_p v5_p v6_p v7_p v10_p v11_p : Word}
    {q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
     shift_p n_p j_p retMem_p dMem_p dloMem_p scratch_un0_p : Word} :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x1 ↦ᵣ v1_p) ** (.x2 ↦ᵣ v2_p) **
       (.x5 ↦ᵣ v5_p) ** (.x6 ↦ᵣ v6_p) ** (.x7 ↦ᵣ v7_p) **
       (.x10 ↦ᵣ v10_p) ** (.x11 ↦ᵣ v11_p) **
       (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
       divScratchValuesCall sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p
         u5_p u6_p u7_p shift_p n_p j_p retMem_p dMem_p dloMem_p scratch_un0_p) h →
      divN4CallSkipStackPost sp a b h := by
  intro h hp
  delta divN4CallSkipStackPost
  refine sepConj_mono_right ?_ h hp
  iterate 7 apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact divScratchValuesCall_implies_divScratchOwnCall
    sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
    shift_p n_p j_p retMem_p dMem_p dloMem_p scratch_un0_p

/-- MOD counterpart of `div_n4_call_skip_stack_weaken`. Same structural
    weakening; only the second operand slot holds `EvmWord.mod a b`
    instead of `EvmWord.div a b`. -/
theorem mod_n4_call_skip_stack_weaken
    (sp : Word) (a b : EvmWord)
    {v1_p v2_p v5_p v6_p v7_p v10_p v11_p : Word}
    {q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
     shift_p n_p j_p retMem_p dMem_p dloMem_p scratch_un0_p : Word} :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x1 ↦ᵣ v1_p) ** (.x2 ↦ᵣ v2_p) **
       (.x5 ↦ᵣ v5_p) ** (.x6 ↦ᵣ v6_p) ** (.x7 ↦ᵣ v7_p) **
       (.x10 ↦ᵣ v10_p) ** (.x11 ↦ᵣ v11_p) **
       (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
       divScratchValuesCall sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p
         u5_p u6_p u7_p shift_p n_p j_p retMem_p dMem_p dloMem_p scratch_un0_p) h →
      modN4CallSkipStackPost sp a b h := by
  intro h hp
  delta modN4CallSkipStackPost
  refine sepConj_mono_right ?_ h hp
  iterate 7 apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact divScratchValuesCall_implies_divScratchOwnCall
    sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
    shift_p n_p j_p retMem_p dMem_p dloMem_p scratch_un0_p

-- ============================================================================
-- DIV n=4 call+skip full-path stack-pre wrappers
-- ============================================================================

/-- EvmWord-level wrapper over `evm_div_n4_full_call_skip_spec`: same
    guarantee (full-path DIV from `base` to `base + nopOff` on the n=4 call+skip
    sub-path) but with the operands bundled as `evmWordIs sp a` /
    `evmWordIs (sp+32) b` and the 19 scratch cells bundled as
    `divScratchValuesCall`.

    The postcondition is still the concrete `fullDivN4CallSkipPost` — turning
    that into `divN4CallSkipStackPost` requires the semantic-correctness bridge
    which depends on Knuth B / `div128Quot` correctness (in progress on a
    separate chain).

    The call-trial path needs an extra `halign` hypothesis because the
    `div128` subroutine returns via `JALR` to `base + 516`, and the stack
    spec must account for the alignment requirement on the return address. -/
theorem evm_div_n4_full_call_skip_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_div_n4_full_call_skip_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_nz halign hbltu hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_div_n4_full_call_skip_stack_pre_spec`: takes
    the precondition as a single `divN4StackPreCall` atom. Mirror of
    `evm_div_n4_full_max_skip_stack_pre_spec_bundled`. -/
theorem evm_div_n4_full_call_skip_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_div_n4_full_call_skip_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [divN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper over `evm_mod_n4_full_call_skip_spec`. Same shape
    as `evm_div_n4_full_call_skip_stack_pre_spec` but for the MOD path:
    `divCode → modCode`, `evm_div_n4_full_call_skip_spec →
    evm_mod_n4_full_call_skip_spec`, and `fullDivN4CallSkipPost →
    fullModN4CallSkipPost`. -/
theorem evm_mod_n4_full_call_skip_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_full_call_skip_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_nz halign hbltu hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_mod_n4_full_call_skip_stack_pre_spec`: takes
    the precondition as a single `modN4StackPreCall` atom. Mirror of
    `evm_div_n4_full_call_skip_stack_pre_spec_bundled`. -/
theorem evm_mod_n4_full_call_skip_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_mod_n4_full_call_skip_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [modN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

-- ============================================================================
-- Call-trial addback (BEQ double-addback): EvmWord-level wrappers
-- ============================================================================

/-- EvmWord-level wrapper over `evm_div_n4_full_call_addback_beq_spec`. The
    same shape as `evm_div_n4_full_call_skip_stack_pre_spec` but for the
    addback branch: `hborrow` has the borrow-fires direction
    (`isAddbackBorrowN4CallEvm`) and the BEQ variant also requires the
    `hcarry2_nz` indicator.

    The postcondition is still the concrete `fullDivN4CallAddbackBeqPost`
    — turning that into `divN4CallAddbackBeqStackPost` requires the
    semantic-correctness bridge which depends on Knuth B / `div128Quot`
    correctness (separate chain). -/
theorem evm_div_n4_full_call_addback_beq_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_div_n4_full_call_addback_beq_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_nz hvalid halign hbltu hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_div_n4_full_call_addback_beq_stack_pre_spec`:
    takes the precondition as a single `divN4StackPreCall` atom. Mirror
    of `evm_div_n4_full_call_skip_stack_pre_spec_bundled` for the addback
    branch. -/
theorem evm_div_n4_full_call_addback_beq_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_div_n4_full_call_addback_beq_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz hvalid halign hbltu hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [divN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper over `evm_mod_n4_full_call_addback_beq_spec`. Same
    shape as `evm_div_n4_full_call_addback_beq_stack_pre_spec` but for the
    MOD path: `divCode → modCode`, `evm_div_n4_full_call_addback_beq_spec →
    evm_mod_n4_full_call_addback_beq_spec`, and `fullDivN4CallAddbackBeqPost
    → fullModN4CallAddbackBeqPost`.

    The MOD version does NOT require the `hvalid : ValidMemRange sp 8`
    hypothesis that the DIV variant carries — the MOD preloop+full-path
    specs don't consume validity hypotheses. -/
theorem evm_mod_n4_full_call_addback_beq_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_full_call_addback_beq_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_mod_n4_full_call_addback_beq_stack_pre_spec`:
    takes the precondition as a single `modN4StackPreCall` atom. Mirror
    of `evm_div_n4_full_call_addback_beq_stack_pre_spec_bundled`. -/
theorem evm_mod_n4_full_call_addback_beq_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_mod_n4_full_call_addback_beq_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [modN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

-- ============================================================================
-- Shift = 0 call-trial skip: DIV EvmWord-level wrapper
-- ============================================================================

/-- Skip-addback condition at n=4 shift=0 path in EvmWord form: the runtime
    borrow check doesn't fire, so the algorithm skips addback after the
    `div128`-computed trial quotient. Shift=0 specialization (no
    normalization applied). -/
def isSkipBorrowN4Shift0Evm (a b : EvmWord) : Prop :=
  isSkipBorrowN4Shift0 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                       (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isSkipBorrowN4Shift0Evm_def {a b : EvmWord} :
    isSkipBorrowN4Shift0Evm a b =
    isSkipBorrowN4Shift0 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                         (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- EvmWord-level wrapper over `evm_div_n4_full_shift0_call_skip_spec`.
    Shift=0 specialization: b3 already has its top bit set, so no
    normalization is applied and `u4 = 0` at runtime — the call-trial
    BLTU is always taken (there is no `hbltu` hypothesis here).

    The postcondition is the concrete `fullDivN4Shift0CallSkipPost` —
    turning that into a semantic stack post requires the separate Knuth-B
    / div128Quot-correctness chain. -/
theorem evm_div_n4_full_shift0_call_skip_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hborrow : isSkipBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4Shift0CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_div_n4_full_shift0_call_skip_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_z halign hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_div_n4_full_shift0_call_skip_stack_pre_spec`:
    takes the precondition as a single `divN4StackPreCall` atom. -/
theorem evm_div_n4_full_shift0_call_skip_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hborrow : isSkipBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4Shift0CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_div_n4_full_shift0_call_skip_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [divN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper over `evm_mod_n4_full_shift0_call_skip_spec`.
    MOD counterpart of `evm_div_n4_full_shift0_call_skip_stack_pre_spec`
    with `divCode → modCode` and `fullDivN4Shift0CallSkipPost →
    fullModN4Shift0CallSkipPost`. -/
theorem evm_mod_n4_full_shift0_call_skip_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hborrow : isSkipBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4Shift0CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_full_shift0_call_skip_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_z halign hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_mod_n4_full_shift0_call_skip_stack_pre_spec`:
    takes the precondition as a single `modN4StackPreCall` atom. -/
theorem evm_mod_n4_full_shift0_call_skip_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hborrow : isSkipBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4Shift0CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_mod_n4_full_shift0_call_skip_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [modN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

-- ============================================================================
-- Shift = 0 call-trial addback (BEQ): EvmWord-level wrappers (DIV + MOD)
-- ============================================================================

/-- Addback-needed condition at n=4 shift=0 path in EvmWord form. Borrow
    fires (mulsub underflowed), so the algorithm decrements the
    `div128Quot`-computed trial quotient and adds back. -/
def isAddbackBorrowN4Shift0Evm (a b : EvmWord) : Prop :=
  isAddbackBorrowN4Shift0 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isAddbackBorrowN4Shift0Evm_def {a b : EvmWord} :
    isAddbackBorrowN4Shift0Evm a b =
    isAddbackBorrowN4Shift0 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- Double-addback carry2≠0 condition at n=4 shift=0 path in EvmWord form. -/
def isAddbackCarry2NzN4Shift0Evm (a b : EvmWord) : Prop :=
  isAddbackCarry2NzN4Shift0 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isAddbackCarry2NzN4Shift0Evm_def {a b : EvmWord} :
    isAddbackCarry2NzN4Shift0Evm a b =
    isAddbackCarry2NzN4Shift0 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                              (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- EvmWord-level wrapper over `evm_div_n4_full_shift0_call_addback_beq_spec`. -/
theorem evm_div_n4_full_shift0_call_addback_beq_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0Evm a b)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4Shift0CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_div_n4_full_shift0_call_addback_beq_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_z halign hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_div_n4_full_shift0_call_addback_beq_stack_pre_spec`. -/
theorem evm_div_n4_full_shift0_call_addback_beq_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0Evm a b)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4Shift0CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_div_n4_full_shift0_call_addback_beq_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [divN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper over `evm_mod_n4_full_shift0_call_addback_beq_spec`. -/
theorem evm_mod_n4_full_shift0_call_addback_beq_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0Evm a b)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4Shift0CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_full_shift0_call_addback_beq_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_z halign hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_mod_n4_full_shift0_call_addback_beq_stack_pre_spec`. -/
theorem evm_mod_n4_full_shift0_call_addback_beq_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0Evm a b)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4Shift0CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_mod_n4_full_shift0_call_addback_beq_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [modN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

-- ============================================================================
-- Semantic-correctness predicates for n=4 call+skip (task #66)
-- ============================================================================

/-- Semantic-correctness precondition for the n=4 call+skip sub-path: the
    algorithm's trial quotient `qHat = div128Quot u4 u3 b3'` is at least
    `⌊val256(a)/val256(b)⌋`.

    Under the runtime skip-borrow check (`isSkipBorrowN4CallEvm`), the upper
    bound `qHat ≤ ⌊val256(a)/val256(b)⌋` is automatic (via T3 =
    `div128Quot_call_skip_le_val256_div`). Adding this hypothesis pins down
    the tight equality `qHat = ⌊val256(a)/val256(b)⌋`, which then feeds
    the stack-spec post reshape into `evmWordIs (sp+32) (EvmWord.div a b)`.

    Mirror pattern of `n4MaxSkipSemanticHolds` (Spec.lean:208), which packages
    the analogous `c3 = 0` hypothesis for max-skip. Here the semantic content
    is the algorithmic lower bound rather than a mulsub carry. Proving this
    from first principles is Knuth TAOCP Theorem A (normalized divisor
    version) — deferred to a future task (formerly issue #65). The stack
    spec delegates the proof to callers (e.g., the higher-level EVM semantic
    composition), following the same contract as the max-skip family. -/
def n4CallSkipSemanticHolds (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
    (div128Quot u4 u3 b3').toNat

theorem n4CallSkipSemanticHolds_def {a b : EvmWord} :
    n4CallSkipSemanticHolds a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
       (div128Quot u4 u3 b3').toNat) :=
  rfl

/-- **Call+skip n=4 div/mod getLimbN bridge.** Under the runtime call-path
    conditions + skip-borrow + the semantic-correctness hypothesis
    `n4CallSkipSemanticHolds`, the algorithm's trial quotient
    `qHat = div128Quot u4 u3 b3'` equals `(EvmWord.div a b).getLimbN 0`
    (and the upper three quotient limbs are zero).

    Mirror of `n4_max_skip_div_mod_getLimbN` (DivN4Overestimate.lean:666) for
    the call path. The max version uses `n4MaxSkipSemanticHolds` (= `c3 = 0`
    from mulsub + max overestimate) to close via `div_correct_n4_no_shift`.
    The call version uses `n4CallSkipSemanticHolds` (= the algorithmic lower
    bound `qHat ≥ val256(a)/val256(b)`) combined with T3's upper bound from
    skip-borrow to pin `qHat.toNat = val256(a)/val256(b) = a.toNat/b.toNat`.

    **Proof sketch** (to be filled in):
    1. From T3 (`div128Quot_call_skip_mul_val256_b_le_val256_a`):
       `qHat.toNat * val256(b) ≤ val256(a)`, hence `qHat.toNat ≤ val256(a)/val256(b)`.
    2. From hsem: `val256(a)/val256(b) ≤ qHat.toNat`.
    3. Therefore `qHat.toNat = val256(a)/val256(b) = a.toNat/b.toNat = (EvmWord.div a b).toNat`.
    4. Since `qHat.toNat < 2^64` (Word bound), `(EvmWord.div a b).toNat < 2^64`, so
       upper 3 limbs are 0. The low limb equals `qHat` by Word-equality of toNat. -/
theorem n4_call_skip_div_mod_getLimbN (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallEvm a b)
    (hsem : n4CallSkipSemanticHolds a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let qHat := div128Quot u4 u3 b3'
    (EvmWord.div a b).getLimbN 0 = qHat ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  intro shift antiShift b3' u4 u3 qHat
  rw [isSkipBorrowN4CallEvm_def] at hborrow
  rw [n4CallSkipSemanticHolds_def] at hsem
  have hT3 := div128Quot_call_skip_mul_val256_b_le_val256_a
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hshift_nz hborrow
  change qHat.toNat * val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
         val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) at hT3
  change val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
         qHat.toNat at hsem
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  have hb_pos : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h | h
    · exfalso; apply hbnz; exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  rw [ha_val, hb_val] at hT3 hsem
  have hq_eq : qHat.toNat = a.toNat / b.toNat := by
    have hle : qHat.toNat ≤ a.toNat / b.toNat :=
      (Nat.le_div_iff_mul_le hb_pos).mpr hT3
    omega
  have hdiv_toNat : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div
    rw [if_neg hbnz]
    exact BitVec.toNat_udiv
  set q_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => qHat | 1 => 0 | 2 => 0 | 3 => 0 with hq_target
  have hq_target_toNat : q_target.toNat = qHat.toNat := by
    simp [q_target, EvmWord.fromLimbs_toNat]
  have hq_eq_div : q_target = EvmWord.div a b :=
    BitVec.eq_of_toNat_eq (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_3

/-- **EVM-stack-level DIV spec on the n=4 call+skip sub-path.**

    Scaffold mirror of `evm_div_n4_max_skip_stack_spec`. Consumes runtime
    conditions (`isCallTrialN4Evm`, `isSkipBorrowN4CallEvm`), shift non-zero,
    alignment, and the semantic-correctness fact `n4CallSkipSemanticHolds`.
    Produces the clean `divN4StackPreCall` → `divN4CallSkipStackPost` shape.

    Reduces to `evm_div_n4_full_call_skip_stack_pre_spec_bundled` + a
    postcondition reshape via `n4_call_skip_div_mod_getLimbN` and
    `div_n4_call_skip_stack_weaken`. The post reshape is analogous to the
    max-skip path (Spec.lean:1309) but walks through `fullDivN4CallSkipPost`
    and `denormDivPost` (no dedicated `_unfold` lemma yet — to be added). -/
theorem evm_div_n4_call_skip_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b)
    (hsem : n4CallSkipSemanticHolds a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) := by
  have h_pre := evm_div_n4_full_call_skip_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_call_skip_div_mod_getLimbN a b hbnz hshift_nz hborrow hsem
  refine cpsTriple_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  simp only [fullDivN4CallSkipPost_unfold, denormDivPost_unfold] at hq
  apply div_n4_call_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ (div128Quot ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 3)).1).toNat % 64))
          (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
              (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
              (clzResult (b.getLimbN 3)).1).toNat % 64))))) **
       ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) **
       ((sp + 56) ↦ₘ (0 : Word)))
      from by rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
                  hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

/-- **Generic: `c3_un = 0` follows from `qHat * val256(b) ≤ val256(a)`.**

    Takes only the un-normalized bound from T3 (or equivalent). Works for
    any `qHat`, so it's usable by both max-skip (where the bound comes
    from `isSkipBorrowN4Max`) and call-skip (where T3 supplies it via
    `div128Quot_call_skip_mul_val256_b_le_val256_a`).

    Proof: from `mulsubN4_val256_eq`,
    `val256(a) + c3.toNat * 2^256 = val256(ms) + qHat.toNat * val256(b)`.
    Combined with the hypothesis `qHat * val256(b) ≤ val256(a)` and the
    bound `val256(ms) < 2^256`, we get `c3.toNat * 2^256 < 2^256`, i.e.
    `c3.toNat = 0`. -/
theorem c3_un_zero_of_qHat_mul_le
    {a0 a1 a2 a3 b0 b1 b2 b3 qHat : Word}
    (h : qHat.toNat * val256 b0 b1 b2 b3 ≤ val256 a0 a1 a2 a3) :
    (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 0 := by
  have heuc := mulsubN4_val256_eq qHat b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at heuc
  have hms_lt : val256 (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).1
                       (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.1
                       (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
                       (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1 < 2^256 :=
    EvmWord.val256_bound ..
  have hc3_lt : (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2.toNat < 2^64 :=
    (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2.isLt
  apply BitVec.eq_of_toNat_eq
  rw [show (0 : Word).toNat = 0 from rfl]
  -- c3.toNat * 2^256 + val256(a) = val256(ms) + qHat.toNat * val256(b) ≤ val256(ms) + val256(a)
  -- → c3.toNat * 2^256 ≤ val256(ms) < 2^256
  -- → c3.toNat = 0
  have h_pow : (2:Nat)^256 > 0 := by positivity
  omega

/-- **Generic: `val256(ms_un) = val256(a) % val256(b)` under c3_un=0 + overestimate.**

    Takes the overestimate bound `val256(a)/val256(b) ≤ qHat.toNat` (supplied
    by `n4CallSkipSemanticHolds` for call-skip, or `max_trial_overestimate_n4`
    for max-skip) plus `c3_un = 0`, and concludes that the 4 un-normalized
    mulsub output limbs at the val256 level equal `val256(a) mod val256(b)`.

    Parameterizes `EvmWord.val256_ms_un_eq_val256_mod_max_skip`
    (Val256ModBridge.lean:30) over the trial quotient `qHat`. Proof is the
    same shape: Euclidean equation + `remainder_lt_of_ge_floor`. -/
theorem val256_ms_un_eq_val256_mod_of_overestimate
    {a0 a1 a2 a3 b0 b1 b2 b3 qHat : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hqHat_ge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ qHat.toNat)
    (hc3_zero : (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 0) :
    let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
    val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 =
    val256 a0 a1 a2 a3 % val256 b0 b1 b2 b3 := by
  intro ms
  have hmulsub_raw := mulsubN4_val256_eq qHat b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at hmulsub_raw
  rw [show ms.2.2.2.2 = (0 : Word) from hc3_zero] at hmulsub_raw
  rw [show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]
    at hmulsub_raw
  have hmulsub : val256 a0 a1 a2 a3 =
      qHat.toNat * val256 b0 b1 b2 b3 +
      val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 := by linarith
  have hv := EvmWord.val256_pos_of_or_ne_zero hbnz
  have ⟨hq, _hr_lt⟩ := EvmWord.remainder_lt_of_ge_floor hv hmulsub hqHat_ge
  rw [hq] at hmulsub
  have := Nat.div_add_mod (val256 a0 a1 a2 a3) (val256 b0 b1 b2 b3)
  have : val256 b0 b1 b2 b3 * (val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3) =
      (val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3) * val256 b0 b1 b2 b3 := Nat.mul_comm _ _
  omega

/-- **Generic `uTop = c3_n` invariant under the overestimate + skip-borrow bounds.**

    Parameterized analog of `EvmWord.u_top_eq_c3_n_max_skip` (ModBridgeUtop.lean:159).
    Takes the T3-shape bound `qHat * val256(b) ≤ val256(a)` (for c3_un = 0),
    the overestimate `val256(a)/val256(b) ≤ qHat.toNat` (for val256(ms_un) <
    val256(b)), and the skip-borrow-derived `c3_n ≤ a3 >>> (64 - s)`
    (= u_top in max-skip / = u4 in call-skip — same thing since
    `antiShift = 64 - s` for `0 < s < 64`).

    Delegates to the already-parameterized `u_top_eq_c3_nat_form`
    (ModBridgeUtop.lean:112), so the whole proof is short. Usable for
    both max-skip (with qHat = signExtend12 4095 + appropriate bounds)
    and call-skip (with qHat = div128Quot u4 u3 b3' + T3 + hsem). -/
theorem u_top_eq_c3_n_of_overestimate
    {a0 a1 a2 a3 b0 b1 b2 b3 qHat : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    {s : Nat} (hs0 : 0 < s) (hs : s < 64)
    (hb3_bound : b3.toNat < 2 ^ (64 - s))
    (hqHat_mul_le : qHat.toNat * val256 b0 b1 b2 b3 ≤ val256 a0 a1 a2 a3)
    (hqHat_ge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ qHat.toNat)
    (hc3_n_le_u_top :
        (mulsubN4 qHat
          (b0 <<< s)
          ((b1 <<< s) ||| (b0 >>> (64 - s)))
          ((b2 <<< s) ||| (b1 >>> (64 - s)))
          ((b3 <<< s) ||| (b2 >>> (64 - s)))
          (a0 <<< s)
          ((a1 <<< s) ||| (a0 >>> (64 - s)))
          ((a2 <<< s) ||| (a1 >>> (64 - s)))
          ((a3 <<< s) ||| (a2 >>> (64 - s)))).2.2.2.2.toNat ≤
        (a3 >>> (64 - s)).toNat) :
    (a3 >>> (64 - s)).toNat =
    (mulsubN4 qHat
      (b0 <<< s)
      ((b1 <<< s) ||| (b0 >>> (64 - s)))
      ((b2 <<< s) ||| (b1 >>> (64 - s)))
      ((b3 <<< s) ||| (b2 >>> (64 - s)))
      (a0 <<< s)
      ((a1 <<< s) ||| (a0 >>> (64 - s)))
      ((a2 <<< s) ||| (a1 >>> (64 - s)))
      ((a3 <<< s) ||| (a2 >>> (64 - s)))).2.2.2.2.toNat := by
  have hc3_un_zero : (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 0 :=
    c3_un_zero_of_qHat_mul_le hqHat_mul_le
  have h_un_raw := mulsubN4_val256_eq qHat b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at h_un_raw
  rw [hc3_un_zero, show (0 : Word).toNat = 0 from rfl,
      Nat.zero_mul, Nat.add_zero] at h_un_raw
  have h_n_raw := mulsubN4_val256_eq qHat
    (b0 <<< s)
    ((b1 <<< s) ||| (b0 >>> (64 - s)))
    ((b2 <<< s) ||| (b1 >>> (64 - s)))
    ((b3 <<< s) ||| (b2 >>> (64 - s)))
    (a0 <<< s)
    ((a1 <<< s) ||| (a0 >>> (64 - s)))
    ((a2 <<< s) ||| (a1 >>> (64 - s)))
    ((a3 <<< s) ||| (a2 >>> (64 - s)))
  simp only [] at h_n_raw
  have h_norm_u := EvmWord.val256_normalize_general hs0 hs a0 a1 a2 a3
  have h_norm_b := EvmWord.val256_normalize hs0 hs b0 b1 b2 b3 hb3_bound
  have h_ms_un_eq_mod :=
    val256_ms_un_eq_val256_mod_of_overestimate hbnz hqHat_ge hc3_un_zero
  simp only [] at h_ms_un_eq_mod
  have h_ms_un_lt_b : val256 (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).1
                             (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.1
                             (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
                             (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1 <
                     val256 b0 b1 b2 b3 := by
    rw [h_ms_un_eq_mod]
    exact Nat.mod_lt _ (EvmWord.val256_pos_of_or_ne_zero hbnz)
  have h_b_lt_pow := EvmWord.val256_lt_of_b3_bound b0 b1 b2 b3 (by omega) hb3_bound
  have hs_pos : 0 < 2 ^ s := by positivity
  exact EvmWord.u_top_eq_c3_nat_form (Q := qHat.toNat) s
    h_un_raw h_norm_u h_norm_b h_n_raw h_ms_un_lt_b h_b_lt_pow (by omega) hs_pos
    hc3_n_le_u_top

/-- **Generic: `val256(denormalized) = val256(a) % val256(b)` under the
    overestimate + skip-borrow bounds.**

    Parameterized analog of `EvmWord.val256_denorm_eq_val256_mod_max_skip`
    (ModBridgeAssemble.lean:39). Takes the T3 bound, the overestimate, and
    the skip-borrow c3_n bound, and concludes that the denormalized 4-limb
    value equals `val256(a) mod val256(b)`. Usable for both max-skip and
    call-skip paths. -/
theorem val256_denorm_eq_val256_mod_of_overestimate
    {a0 a1 a2 a3 b0 b1 b2 b3 qHat : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    {s : Nat} (hs0 : 0 < s) (hs : s < 64)
    (hb3_bound : b3.toNat < 2 ^ (64 - s))
    (hqHat_mul_le : qHat.toNat * val256 b0 b1 b2 b3 ≤ val256 a0 a1 a2 a3)
    (hqHat_ge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ qHat.toNat)
    (hc3_n_le_u_top :
        (mulsubN4 qHat
          (b0 <<< s)
          ((b1 <<< s) ||| (b0 >>> (64 - s)))
          ((b2 <<< s) ||| (b1 >>> (64 - s)))
          ((b3 <<< s) ||| (b2 >>> (64 - s)))
          (a0 <<< s)
          ((a1 <<< s) ||| (a0 >>> (64 - s)))
          ((a2 <<< s) ||| (a1 >>> (64 - s)))
          ((a3 <<< s) ||| (a2 >>> (64 - s)))).2.2.2.2.toNat ≤
        (a3 >>> (64 - s)).toNat) :
    let b0' := b0 <<< s
    let b1' := (b1 <<< s) ||| (b0 >>> (64 - s))
    let b2' := (b2 <<< s) ||| (b1 >>> (64 - s))
    let b3' := (b3 <<< s) ||| (b2 >>> (64 - s))
    let u0 := a0 <<< s
    let u1 := (a1 <<< s) ||| (a0 >>> (64 - s))
    let u2 := (a2 <<< s) ||| (a1 >>> (64 - s))
    let u3 := (a3 <<< s) ||| (a2 >>> (64 - s))
    let msN := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    val256 ((msN.1 >>> s) ||| (msN.2.1 <<< (64 - s)))
           ((msN.2.1 >>> s) ||| (msN.2.2.1 <<< (64 - s)))
           ((msN.2.2.1 >>> s) ||| (msN.2.2.2.1 <<< (64 - s)))
           (msN.2.2.2.1 >>> s) =
    val256 a0 a1 a2 a3 % val256 b0 b1 b2 b3 := by
  intro b0' b1' b2' b3' u0 u1 u2 u3 msN
  have hc3_un_zero : (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 0 :=
    c3_un_zero_of_qHat_mul_le hqHat_mul_le
  have h_denorm := EvmWord.val256_denormalize hs0 hs msN.1 msN.2.1 msN.2.2.1 msN.2.2.2.1
  have h_utop_eq := u_top_eq_c3_n_of_overestimate hbnz hs0 hs hb3_bound
    hqHat_mul_le hqHat_ge hc3_n_le_u_top
  have h_un_raw := mulsubN4_val256_eq qHat b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at h_un_raw
  rw [hc3_un_zero, show (0 : Word).toNat = 0 from rfl,
      Nat.zero_mul, Nat.add_zero] at h_un_raw
  have h_n_raw := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_n_raw
  have h_norm_u := EvmWord.val256_normalize_general hs0 hs a0 a1 a2 a3
  have h_norm_b := EvmWord.val256_normalize hs0 hs b0 b1 b2 b3 hb3_bound
  rw [h_norm_b] at h_n_raw
  have h_ms_n_scaled :
      val256 msN.1 msN.2.1 msN.2.2.1 msN.2.2.2.1 =
      val256 (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).1
             (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.1
             (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
             (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1 * 2^s := by
    set Vu : Nat := val256 u0 u1 u2 u3
    set Vms_n : Nat := val256 msN.1 msN.2.1 msN.2.2.1 msN.2.2.2.1
    set Vms_un : Nat := val256 (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).1
         (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.1
         (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
         (mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
    set Va : Nat := val256 a0 a1 a2 a3
    set Vb : Nat := val256 b0 b1 b2 b3
    set Q : Nat := qHat.toNat
    have hqa : Q * (Vb * 2 ^ s) = Q * Vb * 2 ^ s := by ring
    rw [h_utop_eq] at h_norm_u
    have h_scaled : Va * 2 ^ s = Vms_n + Q * Vb * 2 ^ s := by linarith
    have h_un_scaled : Va * 2 ^ s = (Vms_un + Q * Vb) * 2 ^ s := by
      rw [h_un_raw]
    linarith [h_scaled, h_un_scaled,
      (show (Vms_un + Q * Vb) * 2 ^ s = Vms_un * 2^s + Q * Vb * 2^s from by ring)]
  have h_ms_un_eq_mod :=
    val256_ms_un_eq_val256_mod_of_overestimate hbnz hqHat_ge hc3_un_zero
  simp only [] at h_ms_un_eq_mod
  rw [h_denorm, h_ms_n_scaled, Nat.mul_div_cancel _ (by positivity : 0 < 2^s)]
  exact h_ms_un_eq_mod

/-- **Generic per-limb denorm→mod bridge (Word-inputs form).**

    Parameterized analog of `denorm_limbN_eq_mod_max_skip`
    (ModBridgeAssemble.lean:184). -/
theorem denorm_limbN_eq_mod_of_overestimate
    (a0 a1 a2 a3 b0 b1 b2 b3 qHat : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (s : Nat) (hs0 : 0 < s) (hs : s < 64)
    (hb3_bound : b3.toNat < 2 ^ (64 - s))
    (hqHat_mul_le : qHat.toNat * val256 b0 b1 b2 b3 ≤ val256 a0 a1 a2 a3)
    (hqHat_ge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ qHat.toNat)
    (hc3_n_le_u_top :
        (mulsubN4 qHat
          (b0 <<< s)
          ((b1 <<< s) ||| (b0 >>> (64 - s)))
          ((b2 <<< s) ||| (b1 >>> (64 - s)))
          ((b3 <<< s) ||| (b2 >>> (64 - s)))
          (a0 <<< s)
          ((a1 <<< s) ||| (a0 >>> (64 - s)))
          ((a2 <<< s) ||| (a1 >>> (64 - s)))
          ((a3 <<< s) ||| (a2 >>> (64 - s)))).2.2.2.2.toNat ≤
        (a3 >>> (64 - s)).toNat) :
    let b0' := b0 <<< s
    let b1' := (b1 <<< s) ||| (b0 >>> (64 - s))
    let b2' := (b2 <<< s) ||| (b1 >>> (64 - s))
    let b3' := (b3 <<< s) ||| (b2 >>> (64 - s))
    let u0 := a0 <<< s
    let u1 := (a1 <<< s) ||| (a0 >>> (64 - s))
    let u2 := (a2 <<< s) ||| (a1 >>> (64 - s))
    let u3 := (a3 <<< s) ||| (a2 >>> (64 - s))
    let msN := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let a := EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    (EvmWord.mod a b).getLimbN 0 = ((msN.1 >>> s) ||| (msN.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 1 = ((msN.2.1 >>> s) ||| (msN.2.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 2 = ((msN.2.2.1 >>> s) ||| (msN.2.2.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 3 = (msN.2.2.2.1 >>> s) := by
  intro b0' b1' b2' b3' u0 u1 u2 u3 msN a_ b_
  have h_val_eq := val256_denorm_eq_val256_mod_of_overestimate (qHat := qHat)
    hbnz hs0 hs hb3_bound hqHat_mul_le hqHat_ge hc3_n_le_u_top
  simp only [] at h_val_eq
  have hr : EvmWord.fromLimbs (fun i : Fin 4 =>
      match i with
      | 0 => (msN.1 >>> s) ||| (msN.2.1 <<< (64 - s))
      | 1 => (msN.2.1 >>> s) ||| (msN.2.2.1 <<< (64 - s))
      | 2 => (msN.2.2.1 >>> s) ||| (msN.2.2.2.1 <<< (64 - s))
      | 3 => msN.2.2.2.1 >>> s) = EvmWord.mod a_ b_ :=
    EvmWord.mod_of_val256_eq_mod hbnz h_val_eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_3

/-- **Generic 4-limb denorm bridge from `val256 = a%b * 2^s`** (CLOSED).

    Given any 4 limbs `X1..X4` whose val256 equals `val256(a)%val256(b) * 2^s`,
    extract per-limb equations relating `(EvmWord.mod a b).getLimbN i` to
    the funnel-shift-right denorm pattern over `X1..X4`.

    Useful for the call+addback BEQ MOD adapter's single-addback branch
    (with `X = post1` limbs) — and dual-purpose for any other path that
    establishes the val256 = a%b * 2^s fact at normalized limbs. -/
theorem denorm_4limb_eq_mod_of_val256_eq_amod_pow_s
    {a b : EvmWord} {X1 X2 X3 X4 : Word}
    {s : Nat} (hs0 : 0 < s) (hs : s < 64)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (h_val_eq : val256 X1 X2 X3 X4 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) * 2 ^ s) :
    (EvmWord.mod a b).getLimbN 0 = ((X1 >>> s) ||| (X2 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 1 = ((X2 >>> s) ||| (X3 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 2 = ((X3 >>> s) ||| (X4 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 3 = (X4 >>> s) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have h_denorm := EvmWord.val256_denormalize hs0 hs X1 X2 X3 X4
  have hspos : 0 < (2 : Nat) ^ s := Nat.pos_of_ne_zero (by positivity)
  have h_div : val256 X1 X2 X3 X4 / 2 ^ s =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
    rw [h_val_eq, Nat.mul_div_cancel _ hspos]
  rw [h_div] at h_denorm
  -- h_denorm: val256(denorm of X1..X4) = val256(a) % val256(b)
  -- Provide an explicit type for `hr` so Lean unifies `mod_of_val256_eq_mod`'s
  -- let-chain output with the explicit `EvmWord.fromLimbs` form, avoiding the
  -- annotation-stripping issue from `simp only [] at ...`.
  have hr : EvmWord.fromLimbs (fun i : Fin 4 => match i with
      | 0 => (X1 >>> s) ||| (X2 <<< (64 - s))
      | 1 => (X2 >>> s) ||| (X3 <<< (64 - s))
      | 2 => (X3 >>> s) ||| (X4 <<< (64 - s))
      | 3 => X4 >>> s) =
      EvmWord.mod
        (EvmWord.fromLimbs (fun i : Fin 4 => match i with
          | 0 => a.getLimbN 0 | 1 => a.getLimbN 1
          | 2 => a.getLimbN 2 | 3 => a.getLimbN 3))
        (EvmWord.fromLimbs (fun i : Fin 4 => match i with
          | 0 => b.getLimbN 0 | 1 => b.getLimbN 1
          | 2 => b.getLimbN 2 | 3 => b.getLimbN 3)) :=
    EvmWord.mod_of_val256_eq_mod hbnz' h_denorm
  -- Fold fromLimbs(... a.getLimbN ...) = a (and similarly for b) inside hr.
  have ha_fold : (EvmWord.fromLimbs (fun i : Fin 4 => match i with
        | 0 => a.getLimbN 0 | 1 => a.getLimbN 1
        | 2 => a.getLimbN 2 | 3 => a.getLimbN 3)) = a :=
    EvmWord.fromLimbs_match_getLimbN_id a
  have hb_fold : (EvmWord.fromLimbs (fun i : Fin 4 => match i with
        | 0 => b.getLimbN 0 | 1 => b.getLimbN 1
        | 2 => b.getLimbN 2 | 3 => b.getLimbN 3)) = b :=
    EvmWord.fromLimbs_match_getLimbN_id b
  rw [ha_fold, hb_fold] at hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hr]; exact EvmWord.getLimbN_fromLimbs_3

/-- **Memory-equation form of the val256-denormalize fold** (CLOSED).

    Direct drop-in helper for adapter parents needing to fold the four
    `↦ₘ` limb writes at `sp+32..sp+56` into `evmWordIs (sp+32) (EvmWord.mod a b)`.
    Composes `denorm_4limb_eq_mod_of_val256_eq_amod_pow_s` with
    `evmWordIs_sp32_limbs_eq.symm` internally — bypasses the form-
    mismatch issues that arise when adapter callers try to chain these
    manually. -/
theorem denorm_4limb_to_evmWordIs_eq
    {a b : EvmWord} (sp : Word) {X1 X2 X3 X4 : Word}
    {s : Nat} (hs0 : 0 < s) (hs : s < 64)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (h_val_eq : val256 X1 X2 X3 X4 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) * 2 ^ s) :
    (((sp + 32) ↦ₘ ((X1 >>> s) ||| (X2 <<< (64 - s)))) **
     ((sp + 40) ↦ₘ ((X2 >>> s) ||| (X3 <<< (64 - s)))) **
     ((sp + 48) ↦ₘ ((X3 >>> s) ||| (X4 <<< (64 - s)))) **
     ((sp + 56) ↦ₘ (X4 >>> s))) =
    evmWordIs (sp + 32) (EvmWord.mod a b) := by
  have h_denorm := denorm_4limb_eq_mod_of_val256_eq_amod_pow_s
    (a := a) (b := b) (X1 := X1) (X2 := X2) (X3 := X3) (X4 := X4)
    hs0 hs hb3nz h_val_eq
  exact (evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b)
    ((X1 >>> s) ||| (X2 <<< (64 - s)))
    ((X2 >>> s) ||| (X3 <<< (64 - s)))
    ((X3 >>> s) ||| (X4 <<< (64 - s)))
    (X4 >>> s)
    h_denorm.1 h_denorm.2.1 h_denorm.2.2.1 h_denorm.2.2.2).symm

/-- **Generic per-limb denorm→mod bridge at EvmWord level.**

    EvmWord wrapper over `denorm_limbN_eq_mod_of_overestimate`, taking
    `a b : EvmWord` rather than 8 Word arguments. Parameterized analog
    of `denorm_limbN_eq_mod_max_skip_getLimbN` (ModBridgeAssemble.lean:233). -/
theorem denorm_limbN_eq_mod_of_overestimate_getLimbN
    {a b : EvmWord} {qHat : Word}
    {s : Nat} (hs0 : 0 < s) (hs : s < 64)
    (hb3_bound : (b.getLimbN 3).toNat < 2 ^ (64 - s))
    (hqHat_mul_le : qHat.toNat * val256 (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3) ≤
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3))
    (hqHat_ge : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
        qHat.toNat)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hc3_n_le_u_top :
        (mulsubN4 qHat
          (b.getLimbN 0 <<< s)
          ((b.getLimbN 1 <<< s) ||| (b.getLimbN 0 >>> (64 - s)))
          ((b.getLimbN 2 <<< s) ||| (b.getLimbN 1 >>> (64 - s)))
          ((b.getLimbN 3 <<< s) ||| (b.getLimbN 2 >>> (64 - s)))
          (a.getLimbN 0 <<< s)
          ((a.getLimbN 1 <<< s) ||| (a.getLimbN 0 >>> (64 - s)))
          ((a.getLimbN 2 <<< s) ||| (a.getLimbN 1 >>> (64 - s)))
          ((a.getLimbN 3 <<< s) ||| (a.getLimbN 2 >>> (64 - s)))).2.2.2.2.toNat ≤
        (a.getLimbN 3 >>> (64 - s)).toNat) :
    let msN := mulsubN4 qHat
        (b.getLimbN 0 <<< s)
        ((b.getLimbN 1 <<< s) ||| (b.getLimbN 0 >>> (64 - s)))
        ((b.getLimbN 2 <<< s) ||| (b.getLimbN 1 >>> (64 - s)))
        ((b.getLimbN 3 <<< s) ||| (b.getLimbN 2 >>> (64 - s)))
        (a.getLimbN 0 <<< s)
        ((a.getLimbN 1 <<< s) ||| (a.getLimbN 0 >>> (64 - s)))
        ((a.getLimbN 2 <<< s) ||| (a.getLimbN 1 >>> (64 - s)))
        ((a.getLimbN 3 <<< s) ||| (a.getLimbN 2 >>> (64 - s)))
    (EvmWord.mod a b).getLimbN 0 = ((msN.1 >>> s) ||| (msN.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 1 = ((msN.2.1 >>> s) ||| (msN.2.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 2 = ((msN.2.2.1 >>> s) ||| (msN.2.2.2.1 <<< (64 - s))) ∧
    (EvmWord.mod a b).getLimbN 3 = (msN.2.2.2.1 >>> s) := by
  intro msN
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hraw := denorm_limbN_eq_mod_of_overestimate
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    qHat hbnz' s hs0 hs hb3_bound hqHat_mul_le hqHat_ge hc3_n_le_u_top
  simp only [show (EvmWord.fromLimbs fun i : Fin 4 => match i with
                   | 0 => a.getLimbN 0 | 1 => a.getLimbN 1
                   | 2 => a.getLimbN 2 | 3 => a.getLimbN 3) = a
               from EvmWord.fromLimbs_match_getLimbN_id a,
             show (EvmWord.fromLimbs fun i : Fin 4 => match i with
                   | 0 => b.getLimbN 0 | 1 => b.getLimbN 1
                   | 2 => b.getLimbN 2 | 3 => b.getLimbN 3) = b
               from EvmWord.fromLimbs_match_getLimbN_id b] at hraw
  exact hraw

/-- **Call+skip n=4 MOD denorm adapter.** Stack-level adapter folding
    the four denormalized remainder slots at `sp+32..sp+56` into
    `evmWordIs (sp+32) (EvmWord.mod a b)`. Mirror of
    `EvmWord.output_slot_to_evmWordIs_mod_n4_max_skip_denorm` for the
    call-trial path, where `qHat = div128Quot u4 u3 b3'` rather than
    the max trial `signExtend12 4095`. -/
theorem output_slot_to_evmWordIs_mod_n4_call_skip_denorm
    (sp : Word) (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallEvm a b)
    (hsem : n4CallSkipSemanticHolds a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
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
    (((sp + 32) ↦ₘ ((ms.1 >>> shift) ||| (ms.2.1 <<< (64 - shift)))) **
     ((sp + 40) ↦ₘ ((ms.2.1 >>> shift) ||| (ms.2.2.1 <<< (64 - shift)))) **
     ((sp + 48) ↦ₘ ((ms.2.2.1 >>> shift) ||| (ms.2.2.2.1 <<< (64 - shift)))) **
     ((sp + 56) ↦ₘ (ms.2.2.2.1 >>> shift))) =
    evmWordIs (sp + 32) (EvmWord.mod a b) := by
  -- Shift bounds.
  have := clzResult_fst_toNat_le (b.getLimbN 3)
  have hshift_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    by_contra h
    push Not at h
    apply hshift_nz
    apply BitVec.eq_of_toNat_eq
    rw [show (0 : Word).toNat = 0 from rfl]
    omega
  have hshift_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have hmod_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have h0se12 : signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1 =
      -((clzResult (b.getLimbN 3)).1) := by
    rw [signExtend12_0]; simp
  have hanti_toNat_mod :
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat := by
    rw [h0se12, BitVec.toNat_neg]
    have : ((clzResult (b.getLimbN 3)).1).toNat ≤ 2^64 := by
      have := ((clzResult (b.getLimbN 3)).1).isLt; omega
    omega
  -- b3 CLZ bound.
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  -- T3 bound + hsem.
  rw [isSkipBorrowN4CallEvm_def] at hborrow
  have hT3 := div128Quot_call_skip_mul_val256_b_le_val256_a
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hshift_nz hborrow
  rw [n4CallSkipSemanticHolds_def] at hsem
  have hc3_le := c3_le_u4_of_skip_borrow_call hborrow
  simp only [hmod_eq, hanti_toNat_mod] at hT3 hsem hc3_le
  -- Apply the per-limb bridge. Instantiate with `s = clz.1.toNat`.
  have h_limbs := denorm_limbN_eq_mod_of_overestimate_getLimbN (a := a) (b := b)
    (qHat := div128Quot
      ((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
      (((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
       ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat)))
      (((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
       ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))))
    hshift_pos hshift_lt_64 hb3_bound hT3 hsem hb3nz hc3_le
  -- The goal is a big let-chain. Zeta-reduce everything to the explicit
  -- form, then rewrite `% 64` and `antiShift` to the un-modded Nat form
  -- so the helper's output matches.
  simp only [hmod_eq, hanti_toNat_mod]
  exact (evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _
    h_limbs.1 h_limbs.2.1 h_limbs.2.2.1 h_limbs.2.2.2).symm

/-- **EVM-stack-level MOD spec on the n=4 call+skip sub-path.**

    Mirror of `evm_mod_n4_max_skip_stack_spec` (Spec.lean:1370) for the
    call-trial path. Takes the same six runtime + semantic conditions as
    `evm_div_n4_call_skip_stack_spec`.

    Reduces to `evm_mod_n4_full_call_skip_stack_pre_spec_bundled` + a
    postcondition reshape via `output_slot_to_evmWordIs_mod_n4_call_skip_denorm`
    and `mod_n4_call_skip_stack_weaken`. -/
theorem evm_mod_n4_call_skip_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b)
    (hsem : n4CallSkipSemanticHolds a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) := by
  have h_pre := evm_mod_n4_full_call_skip_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
  -- Shift bound normalizations (mirror max-skip pattern).
  have := clzResult_fst_toNat_le (b.getLimbN 3)
  have hshift_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    by_contra h
    push Not at h
    apply hshift_nz
    apply BitVec.eq_of_toNat_eq
    rw [show (0 : Word).toNat = 0 from rfl]; omega
  have hmod_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have h0se12 : signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1 =
      -((clzResult (b.getLimbN 3)).1) := by rw [signExtend12_0]; simp
  have hanti_toNat_mod :
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat := by
    rw [h0se12, BitVec.toNat_neg]
    have : ((clzResult (b.getLimbN 3)).1).toNat ≤ 2^64 := by
      have := ((clzResult (b.getLimbN 3)).1).isLt; omega
    omega
  -- Denorm adapter: fold the four output slots into `evmWordIs (sp+32) mod`.
  have h_slot := output_slot_to_evmWordIs_mod_n4_call_skip_denorm sp a b
    hb3nz hshift_nz hborrow hsem
  refine cpsTriple_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  simp only [fullModN4CallSkipPost_unfold, denormModPost_unfold] at hq
  apply mod_n4_call_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.mod a b) = _ from h_slot.symm]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  simp only [hmod_eq, hanti_toNat_mod] at hq ⊢
  xperm_hyp hq

-- ============================================================================
-- Call+addback BEQ semantic predicates and stack specs (n=4, shift ≠ 0)
-- ============================================================================

/-- Semantic-correctness precondition for the n=4 call+addback-BEQ sub-path:
    the final `q_out` (= `qHat - 1` single-addback or `qHat - 2` double-addback)
    equals `⌊val256(a)/val256(b)⌋`.

    Unlike `n4CallSkipSemanticHolds` which states a lower-bound on the raw
    `div128Quot`, this predicate directly states that the post-addback
    corrected quotient is the true quotient. Proving it from first
    principles requires the Knuth TAOCP Theorem A overestimate bound
    (`q̂ ≤ q_true + 2`) plus the algorithm's addback-correction semantics,
    which combine to ensure q_out is exactly correct. Deferred to a future
    task; the stack spec delegates the proof to callers.

    Mirror of `n4CallSkipSemanticHolds` for the call+addback branch. -/
def n4CallAddbackBeqSemanticHolds (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let q_out : Word :=
    if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
    else qHat + signExtend12 4095
  q_out.toNat =
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem n4CallAddbackBeqSemanticHolds_def {a b : EvmWord} :
    n4CallAddbackBeqSemanticHolds a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     let q_out : Word :=
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095
     q_out.toNat =
       val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :=
  rfl

/-- **Call+addback BEQ n=4 div getLimbN bridge.** Under the runtime conditions
    + `n4CallAddbackBeqSemanticHolds`, the post-addback corrected quotient
    `q_out` equals `(EvmWord.div a b).getLimbN 0`, and the upper three
    quotient limbs are zero.

    Simpler than the call-skip bridge: hsem directly gives the tight equality
    `q_out.toNat = val256(a)/val256(b)`, so we don't need to combine with T3.
    From that, `(EvmWord.div a b).toNat = q_out.toNat` via `BitVec.toNat_udiv`,
    and `q_out : Word` bounds pin the limbs. -/
theorem n4_call_addback_beq_div_mod_getLimbN (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let q_out : Word :=
      if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
      else qHat + signExtend12 4095
    (EvmWord.div a b).getLimbN 0 = q_out ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat ms carry q_out
  rw [n4CallAddbackBeqSemanticHolds_def] at hsem
  change q_out.toNat = val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) at hsem
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  rw [ha_val, hb_val] at hsem
  -- hsem : q_out.toNat = a.toNat / b.toNat
  have hdiv_toNat : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div
    rw [if_neg hbnz]
    exact BitVec.toNat_udiv
  set q_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => q_out | 1 => 0 | 2 => 0 | 3 => 0 with hq_target
  have hq_target_toNat : q_target.toNat = q_out.toNat := by
    simp [q_target, EvmWord.fromLimbs_toNat]
  have hq_eq_div : q_target = EvmWord.div a b :=
    BitVec.eq_of_toNat_eq (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_3

/-- **EVM-stack-level DIV spec on the n=4 call+addback BEQ sub-path.**

    Mirror of `evm_div_n4_call_skip_stack_spec` for the addback BEQ branch.
    Consumes runtime conditions, shift-nonzero, alignment, validity, and
    the semantic-correctness fact `n4CallAddbackBeqSemanticHolds`. Output
    shape is `divN4CallSkipStackPost` (same as call-skip — both paths
    produce identical stack layouts on success). -/
theorem evm_div_n4_call_addback_beq_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) := by
  have h_pre := evm_div_n4_full_call_addback_beq_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz hvalid halign hbltu hcarry2_nz hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_call_addback_beq_div_mod_getLimbN a b hbnz hsem
  refine cpsTriple_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  simp only [fullDivN4CallAddbackBeqPost_unfold, denormDivPost_unfold] at hq
  apply div_n4_call_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) = _
      from by rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
                  hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

/-- **Sub-stub (single-addback): qHat.toNat = a/b + 1.** Under
    `n4CallAddbackBeqSemanticHolds` and the single-addback condition (i.e.
    first-addback carry ≠ 0, equivalent to `q_out = qHat - 1`), the trial
    quotient overestimates by exactly 1. Direct corollary of hsem (which
    pins q_out.toNat = a/b) plus q_out = qHat - 1 in this branch.

    Once filled, this sub-lemma + `mulsubN4_c3_le_one` give c3 ≤ 1 in the
    single-addback branch, which is the missing piece for the addback-BEQ
    MOD adapter's single-addback closure. -/
theorem qHat_eq_div_plus_one_of_single_addback (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
                 let antiShift :=
                   (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
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
                 addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    (div128Quot u4 u3 b3').toNat = a.toNat / b.toNat + 1 := by
  intro shift antiShift b3' u3 u4
  rw [n4CallAddbackBeqSemanticHolds_def] at hsem
  -- Unfold the if in hsem using hcarry_nz.
  simp only [if_neg hcarry_nz] at hsem
  -- val256(a_limbs) = a.toNat, val256(b_limbs) = b.toNat.
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  rw [ha_val, hb_val] at hsem
  -- hsem : (qHat + signExtend12 4095).toNat = a.toNat / b.toNat
  -- Rewrite the LHS via BitVec.toNat_add + signExtend12_4095_toNat.
  rw [BitVec.toNat_add, signExtend12_4095_toNat] at hsem
  -- hsem : (qHat.toNat + (2^64 - 1)) % 2^64 = a.toNat / b.toNat
  set qHat := div128Quot u4 u3 b3' with hqHat_def
  have h_div_lt : a.toNat / b.toNat < 2^64 := by
    have := a.isLt; have := b.isLt
    -- Dividing by anything ≥ 1 keeps result < 2^256. But we need < 2^64.
    -- Use that hsem already pins (qHat + (-1)).toNat (which is < 2^64) = a/b.
    -- Since LHS < 2^64 (it's a Word toNat after addition), a/b < 2^64.
    have h_lhs_lt : ((qHat.toNat + (2^64 - 1)) % 2^64) < 2^64 := Nat.mod_lt _ (by decide)
    omega
  have hqHat_pos : qHat.toNat ≥ 1 := by
    -- From hborrow: c3 ≠ 0 (specifically u4 < c3 ≥ 1).
    -- Contrapositive of `c3_un_zero_of_qHat_mul_le`: c3 ≠ 0 → qHat * b > a.
    -- If qHat = 0, then 0 * b = 0 ≤ a, contradicting qHat * b > a.
    by_contra hqHat_zero
    push Not at hqHat_zero
    -- hqHat_zero : qHat.toNat < 1, i.e., qHat.toNat = 0.
    have hqHat_eq_zero : qHat.toNat = 0 := by omega
    -- Then qHat * b = 0 ≤ a, so c3 = 0 by `c3_un_zero_of_qHat_mul_le`.
    have h_mul_le : qHat.toNat *
        val256 ((b.getLimbN 0) <<< shift)
              (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> (64 - shift)))
              (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> (64 - shift)))
              (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> (64 - shift)))
        ≤ val256 ((a.getLimbN 0) <<< shift)
              (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> (64 - shift)))
              (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> (64 - shift)))
              (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> (64 - shift))) := by
      rw [hqHat_eq_zero, Nat.zero_mul]; exact Nat.zero_le _
    have h_c3_zero := c3_un_zero_of_qHat_mul_le h_mul_le
    -- But hborrow gives u4 < c3, hence c3 ≥ 1 ≠ 0.
    rw [isAddbackBorrowN4CallEvm_def] at hborrow
    have h_u4_lt_c3 := EvmWord.u_top_lt_c3_of_addback_borrow_call
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        hborrow
    -- shift in `_call` form uses the un-modded clzResult; reconcile via rfl/match.
    -- The c3 in h_c3_zero matches the c3 in h_u4_lt_c3 (same shift mod 64).
    simp only [] at h_u4_lt_c3
    -- Goal: False. From h_c3_zero (c3 = 0) and h_u4_lt_c3 (u4 < c3.toNat),
    -- we have u4 < 0, contradiction.
    have h_c3_toNat_zero : (mulsubN4 qHat
        ((b.getLimbN 0) <<< shift)
        (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> (64 - shift)))
        (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> (64 - shift)))
        (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> (64 - shift)))
        ((a.getLimbN 0) <<< shift)
        (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> (64 - shift)))
        (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> (64 - shift)))
        (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> (64 - shift)))).2.2.2.2.toNat = 0 := by
      rw [h_c3_zero]; rfl
    -- Bridge: convert h_u4_lt_c3's Word form to match h_c3_toNat_zero's Nat form.
    -- Use `antiShift_toNat_mod_eq` to rewrite `(signExtend12 0 - clz).toNat % 64`
    -- to `64 - clz.toNat`. Then `(64 - clz.toNat) = (64 - shift)` via
    -- `shift = clz.toNat % 64 = clz.toNat` when clz.toNat ≤ 63.
    have h_clz_le : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
      clzResult_fst_toNat_le _
    have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
      rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
      · exfalso; apply hshift_nz
        exact BitVec.eq_of_toNat_eq (by simp [h0])
      · exact h0
    have h_anti_eq : (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
        = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
      antiShift_toNat_mod_eq h_clz_pos h_clz_le
    have h_shift_eq : shift = (clzResult (b.getLimbN 3)).1.toNat := by
      show (clzResult (b.getLimbN 3)).1.toNat % 64 = (clzResult (b.getLimbN 3)).1.toNat
      omega
    -- Now h_u4_lt_c3 has antiShift in Word form, but h_anti_eq + h_shift_eq give
    -- it equals our local `64 - shift`. After rewriting, the mulsubN4 invocations
    -- in h_u4_lt_c3 and h_c3_toNat_zero have identical arguments, contradiction.
    rw [h_anti_eq] at h_u4_lt_c3
    rw [show (clzResult (b.getLimbN 3)).1.toNat % 64 = (clzResult (b.getLimbN 3)).1.toNat
        from by omega] at h_u4_lt_c3
    -- Unfold qHat/u4/u3/b3'/shift/antiShift in h_c3_toNat_zero to match h_u4_lt_c3's
    -- fully-inlined form, then omega closes via c3 = 0 ∧ u4.toNat < c3.toNat.
    have h_anti_unfold : antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat := h_anti_eq
    rw [hqHat_def,
        show u4 = a.getLimbN 3 >>> antiShift from rfl,
        show u3 = a.getLimbN 3 <<< shift ||| a.getLimbN 2 >>> antiShift from rfl,
        show b3' = b.getLimbN 3 <<< shift ||| b.getLimbN 2 >>> antiShift from rfl,
        h_shift_eq, h_anti_unfold] at h_c3_toNat_zero
    omega
  -- (qHat.toNat + 2^64 - 1) % 2^64 = qHat.toNat - 1 when qHat ≥ 1.
  have h_qHat_lt : qHat.toNat < 2^64 := qHat.isLt
  have : (qHat.toNat + (2^64 - 1)) % 2^64 = qHat.toNat - 1 := by
    rw [show qHat.toNat + (2^64 - 1) = (qHat.toNat - 1) + 2^64 from by omega]
    rw [Nat.add_mod_right]
    apply Nat.mod_eq_of_lt; omega
  rw [this] at hsem
  -- hsem : qHat.toNat - 1 = a.toNat / b.toNat
  omega

/-- **Pure-Nat algebraic identity: post1_low4 + (u4 + 1)*2^256 = a%b*2^s + c3*2^256.**

    Combines the mulsub Euclidean, addback Euclidean, val256 normalization
    identities, and qHat = a/b + 1 into a single Nat equation. Avoids Nat
    subtraction by rearranging.

    From this identity + bound `post1_low4 < 2^256` + `c3 < 2^256` + the
    range of `a%b * 2^s < 2^256`, omega can derive c3 = u4 + 1 in single-
    addback. (Note: the lemma exposes the algebra; the surrounding proof
    must establish u4_lt_c3 from hborrow to pin c3 ≥ u4 + 1.) -/
theorem val256_post1_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    (post1_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) = ms_val + (a_val / b_val + 1) * (b_val * 2^s))
    (h_addback : post1_val + 2^256 = ms_val + b_val * 2^s)
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s) :
    post1_val + (u4 + 1) * 2^256 = a_val % b_val * 2^s + c3 * 2^256 := by
  have h_dam_mul : a_val / b_val * b_val + a_val % b_val = a_val := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod a_val b_val
  -- Replace `a_val / b_val * b_val * 2^s` with `a_val * 2^s - a_val % b_val * 2^s`
  -- via h_dam_mul.
  have h_div_mul_pow : a_val / b_val * b_val * 2^s + a_val % b_val * 2^s = a_val * 2^s := by
    rw [← Nat.add_mul]; rw [h_dam_mul]
  have h_expand : (a_val / b_val + 1) * (b_val * 2^s) =
      a_val / b_val * b_val * 2^s + b_val * 2^s := by ring
  -- h_mulsub_simp: c3 * 2^256 + a_val % b_val * 2^s = ms_val + b_val * 2^s + u4 * 2^256.
  have h_mulsub_simp : c3 * 2^256 + a_val % b_val * 2^s =
      ms_val + b_val * 2^s + u4 * 2^256 := by
    -- Use h_mulsub + h_expand + h_div_mul_pow + h_u4_le.
    have h1 : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) =
              ms_val + (a_val / b_val * b_val * 2^s + b_val * 2^s) := by
      rw [← h_expand]; exact h_mulsub
    omega
  -- Combine with h_addback.
  omega

/-- **Pure-Nat: c3 ≤ u4 + 1 from the closed identity + bounds.**

    Direct corollary: from `post1_val + (u4 + 1)*2^256 = a%b*2^s + c3*2^256`
    plus `post1_val < 2^256` (val256 bound) and `a%b*2^s < 2^256` (a%b < b
    and b * 2^s ≤ 2^256), it follows that `c3 ≤ u4 + 1` — otherwise
    post1_val would exceed 2^256. -/
theorem c3_le_u4_plus_one_from_identity
    (post1_val a_val b_val s u4 c3 : Nat)
    (h_id : post1_val + (u4 + 1) * 2^256 = a_val % b_val * 2^s + c3 * 2^256)
    (h_post1_lt : post1_val < 2^256)
    (h_amod_pow_lt : a_val % b_val * 2^s < 2^256) :
    c3 ≤ u4 + 1 := by
  -- Suppose c3 ≥ u4 + 2. Then RHS ≥ (u4 + 2)*2^256 = (u4 + 1)*2^256 + 2^256.
  -- LHS = post1_val + (u4 + 1)*2^256 < 2^256 + (u4 + 1)*2^256.
  -- a%b*2^s ≥ 0 and a%b*2^s < 2^256, so RHS could be in
  -- [(u4 + 2)*2^256, (u4 + 2)*2^256 + 2^256). LHS bound contradicts.
  by_contra h_gt
  push Not at h_gt
  have h_c3_ge : c3 ≥ u4 + 2 := h_gt
  have h_c3_mul : c3 * 2^256 ≥ (u4 + 2) * 2^256 := Nat.mul_le_mul_right _ h_c3_ge
  have h_split : (u4 + 2) * 2^256 = (u4 + 1) * 2^256 + 2^256 := by ring
  omega

/-- **Pure-Nat: c3 = u4 + 1 from mulsub Euclidean + addback Euclidean + bounds.**

    Combined sub-stub: takes the val256-level Euclidean equations, normalization
    bounds, and `u4 < c3`, and outputs c3 = u4 + 1 directly. This is the
    pure-Nat composition of the algebraic identity, the c3 ≤ u4 + 1 bound,
    and the u4 < c3 hypothesis.

    Once the Word-level wrapper at `c3_n_eq_u4_plus_one_of_single_addback`
    is plumbed up, it just calls this. -/
theorem c3_eq_u4_plus_one_from_mulsub_addback_bounds
    (post1_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) = ms_val + (a_val / b_val + 1) * (b_val * 2^s))
    (h_addback : post1_val + 2^256 = ms_val + b_val * 2^s)
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s)
    (h_post1_lt : post1_val < 2^256)
    (h_amod_pow_lt : a_val % b_val * 2^s < 2^256)
    (h_u4_lt_c3 : u4 < c3) :
    c3 = u4 + 1 := by
  have h_id := val256_post1_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    post1_val ms_val a_val b_val s u4 c3 h_mulsub h_addback h_u4_le
  have h_le := c3_le_u4_plus_one_from_identity
    post1_val a_val b_val s u4 c3 h_id h_post1_lt h_amod_pow_lt
  omega

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
noncomputable def algCallAddbackBeqCarry (a b : EvmWord) : Word :=
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
noncomputable def algCallAddbackBeqMsC3 (a b : EvmWord) : Word :=
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
noncomputable def algCallAddbackBeqU4 (a b : EvmWord) : Word :=
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
noncomputable def algCallAddbackBeqPost1Val (a b : EvmWord) : Nat :=
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
noncomputable def algCallAddbackBeqPost1Limb0 (a b : EvmWord) : Word :=
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
noncomputable def algCallAddbackBeqPost1Limb1 (a b : EvmWord) : Word :=
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
noncomputable def algCallAddbackBeqPost1Limb2 (a b : EvmWord) : Word :=
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
noncomputable def algCallAddbackBeqPost1Limb3 (a b : EvmWord) : Word :=
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
noncomputable def algCallAddbackBeqUn0Out (a b : EvmWord) : Word :=
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
noncomputable def algCallAddbackBeqUn1Out (a b : EvmWord) : Word :=
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
noncomputable def algCallAddbackBeqUn2Out (a b : EvmWord) : Word :=
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
noncomputable def algCallAddbackBeqUn3Out (a b : EvmWord) : Word :=
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
noncomputable def algCallAddbackBeqMsLowVal (a b : EvmWord) : Nat :=
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

/-- **Addback Euclidean (carry = 1) for the call+addback BEQ algorithm** (CLOSED).

    In the single-addback branch (`algCallAddbackBeqCarry a b ≠ 0`),
    the val256 of the post1 limbs satisfies:

      `algCallAddbackBeqPost1Val a b + 2^256 =
         algCallAddbackBeqMsLowVal a b + val256(b_limbs) * 2^s`

    where s = clz % 64. Combines `addbackN4_val256_eq` (carry-form) with
    `addbackN4_carry_le_one` to pin carry.toNat = 1, plus `val256_normalize`
    to fold the normalized b into `val256(b) * 2^s`.

    Useful as the `h_addback` precondition of
    `post1_val_eq_amod_pow_s_pure_nat` when closing the wrapper. -/
theorem algCallAddbackBeq_addback_euclidean_carry_one
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqPost1Val a b + 2 ^ 256 =
      algCallAddbackBeqMsLowVal a b +
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
  -- Setup: clz bounds.
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  -- Unfold both irreducibles.
  rw [algCallAddbackBeqPost1Val_unfold, algCallAddbackBeqMsLowVal_unfold]
  simp only []
  -- Define ms in let-chain form.
  set shift := (clzResult (b.getLimbN 3)).1.toNat % 64 with hshift_def
  set antiShift :=
    (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 with hanti_def
  set b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  set b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  set b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  set b0' := (b.getLimbN 0) <<< shift
  set u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  set u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  set u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  set u0 := (a.getLimbN 0) <<< shift
  set u4 := (a.getLimbN 3) >>> antiShift
  set qHat := div128Quot u4 u3 b3'
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  -- Addback Euclidean at val256 level.
  have h_addback_eq := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  simp only [] at h_addback_eq
  -- carry.toNat = 1: from hcarry_nz (≠ 0) + addbackN4_carry_le_one (≤ 1).
  have h_carry_le := addbackN4_carry_le_one ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  rw [algCallAddbackBeqCarry_unfold] at hcarry_nz
  simp only [] at hcarry_nz
  have h_carry_eq_one :
      (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat = 1 := by
    have h_pos : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat ≠ 0 := by
      intro h_zero
      apply hcarry_nz
      apply BitVec.eq_of_toNat_eq
      rw [h_zero]; rfl
    omega
  rw [h_carry_eq_one] at h_addback_eq
  -- val256(b_norm) = val256(b) * 2^s.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ shift := by
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  -- Combine.
  rw [h_norm_b] at h_addback_eq
  omega

/-- **Bound: `algCallAddbackBeqU4 < algCallAddbackBeqMsC3`** (CLOSED).

    Wraps `EvmWord.u_top_lt_c3_of_addback_borrow_call` in the irreducible-
    bundle form, taking just `hborrow : isAddbackBorrowN4CallEvm a b`.
    Useful as the `h_u4_lt_c3` precondition of
    `post1_val_eq_amod_pow_s_pure_nat` when closing the wrapper. -/
theorem algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat
    (a b : EvmWord) (hborrow : isAddbackBorrowN4CallEvm a b) :
    (algCallAddbackBeqU4 a b).toNat < (algCallAddbackBeqMsC3 a b).toNat := by
  rw [show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl,
      show (algCallAddbackBeqMsC3 a b).toNat = _ from by
        unfold algCallAddbackBeqMsC3; rfl]
  rw [isAddbackBorrowN4CallEvm_def] at hborrow
  exact EvmWord.u_top_lt_c3_of_addback_borrow_call
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hborrow

/-- **Mulsub Euclidean for the call+addback BEQ algorithm** (CLOSED).

    The val256-level mulsub Euclidean identity at normalized inputs,
    composed with `qHat = a/b + 1` (single-addback) and the normalization
    identities for `u_norm` and `b_norm`. In the irreducible-bundle form:

      (algCallAddbackBeqMsC3 a b).toNat * 2^256 +
        (val256(a_limbs) * 2^s - (algCallAddbackBeqU4 a b).toNat * 2^256) =
      algCallAddbackBeqMsLowVal a b +
        (val256(a_limbs) / val256(b_limbs) + 1) * (val256(b_limbs) * 2^s)

    Useful as the `h_mulsub` precondition of
    `post1_val_eq_amod_pow_s_pure_nat` when closing the wrapper. -/
theorem algCallAddbackBeq_mulsub_euclidean
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    (algCallAddbackBeqMsC3 a b).toNat * 2 ^ 256 +
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) -
        (algCallAddbackBeqU4 a b).toNat * 2 ^ 256) =
    algCallAddbackBeqMsLowVal a b +
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 1) *
      (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64)) := by
  -- Setup: clz bounds.
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  -- Bridge val256(a_limbs) = a.toNat and similar for b.
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  -- qHat = a/b + 1 from the closed sub-stub.
  rw [algCallAddbackBeqCarry_unfold] at hcarry_nz
  have h_qHat_eq : (div128Quot ((a.getLimbN 3) >>>
      ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
      (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
        ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 3)).1).toNat % 64)))
      (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
        ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 3)).1).toNat % 64)))).toNat =
      a.toNat / b.toNat + 1 :=
    qHat_eq_div_plus_one_of_single_addback a b hshift_nz hborrow hsem hcarry_nz
  -- Unfold the irreducibles.
  rw [show (algCallAddbackBeqMsC3 a b).toNat = _ from by
        unfold algCallAddbackBeqMsC3; rfl,
      show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl,
      algCallAddbackBeqMsLowVal_unfold]
  simp only []
  -- Set up the let-chain.
  set shift := (clzResult (b.getLimbN 3)).1.toNat % 64 with hshift_def
  set antiShift :=
    (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 with hanti_def
  set b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift) with hb3_eq
  set b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  set b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  set b0' := (b.getLimbN 0) <<< shift
  set u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift) with hu3_eq
  set u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  set u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  set u0 := (a.getLimbN 0) <<< shift
  set u4 := (a.getLimbN 3) >>> antiShift with hu4_eq
  set qHat := div128Quot u4 u3 b3' with hqHat_eq
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  -- Mulsub Euclidean at val256 level.
  have h_mulsub_eq := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub_eq
  -- val256(b_norm) = val256(b) * 2^s.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ shift := by
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  -- val256(u_norm low4) + u4 * 2^256 = val256(a) * 2^s.
  have h_norm_u : val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ shift := by
    show val256 ((a.getLimbN 0) <<< shift)
                (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift))
                (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift))
                (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)) +
            ((a.getLimbN 3) >>> antiShift).toNat * 2 ^ 256 = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize_general h_clz_pos h_clz_lt_64
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  -- Express h_qHat_eq in terms of the let-chain qHat.
  have h_qHat : qHat.toNat = a.toNat / b.toNat + 1 := h_qHat_eq
  -- Combine. Substitute into h_mulsub_eq using h_norm_b, h_qHat, h_norm_u.
  rw [h_norm_b] at h_mulsub_eq
  rw [h_qHat] at h_mulsub_eq
  rw [ha_val, hb_val]
  have h_u_eq : val256 u0 u1 u2 u3 = a.toNat * 2 ^ shift - u4.toNat * 2 ^ 256 := by
    have h := h_norm_u; rw [ha_val] at h; omega
  rw [h_u_eq] at h_mulsub_eq
  rw [hb_val] at h_mulsub_eq
  -- Bridge the goal's inline `mulsubN4 ...` forms to `ms.{...}` via rfl.
  have h_ms_top : (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat
      = ms.2.2.2.2.toNat := rfl
  have h_ms_low : val256
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.1
      = val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 := rfl
  rw [h_ms_top, h_ms_low]
  omega

/-- **Bound: `a%b * 2^s < 2^256` in the call+addback BEQ shape** (CLOSED).

    Wraps `EvmWord.val256_mod_mul_pow_lt_pow256_of_b3_bound` taking
    `b3 ≠ 0` (rather than `b ≠ 0`) and giving the `% 64`-shifted exponent
    form used by the algorithm scaffold. Useful as the `h_amod_pow_lt`
    precondition of `post1_val_eq_amod_pow_s_pure_nat` when closing
    `algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback`. -/
theorem algCallAddbackBeq_amod_pow_s_lt_pow256
    (a b : EvmWord) (hb3nz : b.getLimbN 3 ≠ 0) :
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
      2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) < 2 ^ 256 := by
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hvb_pos : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) > 0 :=
    EvmWord.val256_pos_of_or_ne_zero hbnz
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  rw [h_s_eq]
  exact EvmWord.val256_mod_mul_pow_lt_pow256_of_b3_bound
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (by omega) hvb_pos hb3_bound

/-- **Sub-stub: c3_n = u4 + 1 in single-addback** (CLOSED).

    The key algebraic identity for the call-addback BEQ MOD adapter, mirroring
    `u_top_eq_c3_n_of_overestimate` (call-skip case where c3_n = u4).

    Under hsem + hcarry_nz (single-addback) + hborrow (giving u4 < c3_n):
    - From `qHat_eq_div_plus_one_of_single_addback`: qHat = val256(a)/val256(b) + 1.
    - Mulsub Euclidean: c3_n*2^256 = val256(ms_n) + qHat*val256(b_norm) - val256(u_norm).
    - val256(u_norm) = val256(a)*2^s - u4*2^256, val256(b_norm) = val256(b)*2^s.
    - Algebra: c3_n*2^256 = val256(ms_n) + (val256(b) - val256(a)%val256(b))*2^s + u4*2^256.

    The bound `0 ≤ val256(post1_low4) < 2^256` (from val256 being a 4-limb val)
    combined with the addback Euclidean (carry = 1) forces c3_n - 1 - u4 = 0,
    i.e., c3_n = u4 + 1.

    Combined with hborrow's c3_n ≥ u4 + 1, this pins c3_n exactly.

    **Caveat for callers**: this sub-stub uses `% 64` form for shift/antiShift
    (matching `n4CallAddbackBeqSemanticHolds_def`). Direct application from a
    parent context that uses `set s := clz.1.toNat` (no `% 64`) hits a
    200k-heartbeat elaboration timeout. Callers should align their let-chain
    binding form to use `% 64`, or inline the proof body. -/
theorem c3_n_eq_u4_plus_one_of_single_addback (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
                 let antiShift :=
                   (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
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
                 addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
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
    ms.2.2.2.2.toNat = u4.toNat + 1 := by
  intro shift antiShift b3' b2' b1' b0' u3 u2 u1 u0 u4 qHat ms
  -- Concrete proof: apply the closed pure-Nat sub-stub
  -- `c3_eq_u4_plus_one_from_mulsub_addback_bounds` after deriving its 6
  -- preconditions:
  -- - h_mulsub: from `mulsubN4_val256_eq` at normalized limbs +
  --   `qHat_eq_div_plus_one_of_single_addback` (hsem is in scope).
  -- - h_addback: from `addbackN4_val256_eq` at normalized limbs (carry = 1
  --   from hcarry_nz).
  -- - h_u4_le: u4*2^256 ≤ val256(a)*2^s. Follows from u4 = a3 >>> antiShift
  --   (top-s bits of a3) plus val256(a) ≥ a3 * 2^192.
  -- - h_post1_lt: val256(post1_low4) < 2^256 (always, val256 of 4 limbs).
  -- - h_amod_pow_lt: val256(a) % val256(b) * 2^s < 2^256. Follows from
  --   val256(a) % val256(b) < val256(b) ≤ 2^256 / 2^s ⟹ a%b * 2^s < 2^256.
  --   This is the val256_mod_mul_pow bound, available as
  --   `val256_mod_mul_pow_lt_pow256_of_b3_bound`.
  -- - h_u4_lt_c3: directly from hborrow via `u_top_lt_c3_of_addback_borrow_call`.
  -- TODO: each precondition is a small focused derivation (~5-15 lines).
  -- Save folded forms for sub-stub applications, before unfolding.
  have hsem_orig := hsem
  have hborrow_orig := hborrow
  -- Step 1: h_u4_lt_c3 from hborrow.
  rw [isAddbackBorrowN4CallEvm_def] at hborrow
  have h_u4_lt_c3 := EvmWord.u_top_lt_c3_of_addback_borrow_call
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hborrow
  -- Step 2: h_post1_lt — val256(post1_low4) < 2^256 (val256 of any 4-limb is bounded).
  let post1 := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  have h_post1_lt : val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1 < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  -- Step 3: h_amod_pow_lt — val256(a) % val256(b) * 2^s < 2^256.
  have h_clz_le : (clzResult (b.getLimbN 3)).1.toNat ≤ 64 := by
    have := clzResult_fst_toNat_le (b.getLimbN 3); omega
  have hbnz_or : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hvb_pos : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) > 0 :=
    EvmWord.val256_pos_of_or_ne_zero hbnz_or
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  have h_amod_pow_lt :
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ (clzResult (b.getLimbN 3)).1.toNat < 2 ^ 256 :=
    EvmWord.val256_mod_mul_pow_lt_pow256_of_b3_bound
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      h_clz_le hvb_pos hb3_bound
  -- Step 4: h_u4_le — u4 * 2^256 ≤ val256(a) * 2^s.
  -- u4 = a3 >>> antiShift = a3 / 2^(64-s), so u4 * 2^(64-s) ≤ a3.
  -- val256(a) ≥ a3 * 2^192. Hence u4 * 2^256 = u4 * 2^(64-s) * 2^(192+s)
  --   ≤ a3 * 2^(192+s) ≤ val256(a) * 2^s.
  have h_a3_val_ge :
      (a.getLimbN 3).toNat * 2^192 ≤
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) := by
    unfold val256; nlinarith [(a.getLimbN 0).isLt, (a.getLimbN 1).isLt, (a.getLimbN 2).isLt]
  have h_u4_toNat : u4.toNat =
      (a.getLimbN 3).toNat / 2 ^ ((signExtend12 (0 : BitVec 12) -
        (clzResult (b.getLimbN 3)).1).toNat % 64) := by
    show ((a.getLimbN 3) >>> antiShift).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  -- antiShift = 64 - s, derived via antiShift_toNat_mod_eq (needs 1 ≤ s ≤ 63).
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
  have h_u4_le : u4.toNat * 2^256 ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    rw [h_s_eq]
    -- u4 * 2^antiShift ≤ a3 (Nat.div_mul_le_self).
    have h_u4_mul : u4.toNat * 2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat)
        ≤ (a.getLimbN 3).toNat := by
      rw [h_u4_toNat, h_anti_eq]
      exact Nat.div_mul_le_self _ _
    -- Multiply both sides by 2^(192 + s) and use the val256 ≥ a3*2^192 bound.
    set s := (clzResult (b.getLimbN 3)).1.toNat
    have h_pow_split : (2 : Nat)^256 = 2^(64 - s) * (2^192 * 2^s) := by
      rw [show (2 : Nat)^192 * 2^s = 2^(192 + s) from by rw [pow_add],
          show (2 : Nat)^(64 - s) * 2^(192 + s) = 2^((64 - s) + (192 + s)) from
            (pow_add 2 (64-s) (192+s)).symm,
          show (64 - s) + (192 + s) = 256 from by omega]
    rw [h_pow_split]
    -- Goal: u4 * (2^(64-s) * (2^192 * 2^s)) ≤ val256(a) * 2^s.
    calc u4.toNat * (2 ^ (64 - s) * (2 ^ 192 * 2 ^ s))
        = (u4.toNat * 2 ^ (64 - s)) * (2 ^ 192 * 2 ^ s) := by ring
      _ ≤ (a.getLimbN 3).toNat * (2 ^ 192 * 2 ^ s) :=
          Nat.mul_le_mul_right _ h_u4_mul
      _ = (a.getLimbN 3).toNat * 2 ^ 192 * 2 ^ s := by ring
      _ ≤ val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) * 2 ^ s :=
          Nat.mul_le_mul_right _ h_a3_val_ge
  -- Step 5a: addback Euclidean (val256-level, with carry term) — direct application.
  have h_addback_eq := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  simp only [] at h_addback_eq
  -- Step 5b: carry.toNat = 1 from hcarry_nz + addbackN4_carry_le_one.
  have h_carry_le := addbackN4_carry_le_one ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  have h_carry_eq_one : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat = 1 := by
    -- carry is a Word that's ≠ 0 (hcarry_nz) and ≤ 1 (h_carry_le); so carry.toNat = 1.
    have h_pos : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat ≠ 0 := by
      intro h_zero
      apply hcarry_nz
      change addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' = (0 : Word)
      apply BitVec.eq_of_toNat_eq
      rw [h_zero]; rfl
    omega
  -- Step 5c: val256(b_norm) = val256(b) * 2^s via val256_normalize.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    -- Unfold b0'..b3' and antiShift to bring the `(64 - s)` form into scope.
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    have h_anti_unfold : antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat := h_anti_eq
    have h_shift_unfold : shift = (clzResult (b.getLimbN 3)).1.toNat := h_s_eq
    rw [h_anti_unfold, h_shift_unfold, h_s_eq]
    have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by
      have := h_clz_le_63; omega
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  -- Step 5d: combine h_addback_eq + h_carry_eq_one + h_norm_b → h_addback.
  have h_addback : val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1 + 2^256 =
      val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 +
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    show val256 (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').1
                (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.1
                (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.1
                (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.2.1 + 2^256 = _
    rw [← h_norm_b]
    have h := h_addback_eq
    rw [h_carry_eq_one] at h
    omega
  -- Step 6: h_qHat_eq — qHat.toNat = a/b + 1 from the closed sub-stub.
  have h_qHat_eq : qHat.toNat = a.toNat / b.toNat + 1 :=
    qHat_eq_div_plus_one_of_single_addback a b hshift_nz hborrow_orig hsem_orig hcarry_nz
  -- Step 7: h_mulsub_eq — mulsub Euclidean at val256 level.
  have h_mulsub_eq := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub_eq
  -- Step 8: h_norm_u — val256(u_norm_low4) + u4*2^256 = val256(a)*2^s.
  have h_norm_u : val256 u0 u1 u2 u3 + u4.toNat * 2^256 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    show val256 ((a.getLimbN 0) <<< shift)
                (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift))
                (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift))
                (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)) +
            ((a.getLimbN 3) >>> antiShift).toNat * 2^256 = _
    have h_anti_unfold : antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat := h_anti_eq
    have h_shift_unfold : shift = (clzResult (b.getLimbN 3)).1.toNat := h_s_eq
    rw [h_anti_unfold, h_shift_unfold, h_s_eq]
    have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by
      have := h_clz_le_63; omega
    exact EvmWord.val256_normalize_general h_clz_pos h_clz_lt_64
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  -- Step 9: combine h_mulsub_eq + h_norm_u + h_norm_b + h_qHat_eq → h_mulsub.
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  -- Step 9: h_mulsub composition.
  -- h_norm_b'  : val256(b0'..b3') = b.toNat * 2^s.
  -- h_norm_u'  : val256(u0..u3) + u4*2^256 = a.toNat * 2^s.
  have h_norm_b' : val256 b0' b1' b2' b3' = b.toNat *
      2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    rw [h_norm_b, hb_val]
  have h_norm_u' : val256 u0 u1 u2 u3 + u4.toNat * 2^256 = a.toNat *
      2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    have h := h_norm_u
    rw [ha_val] at h
    exact h
  -- ms_eq: ms.2.2.2.2 = (inline mulsubN4 ...).2.2.2.2 (defeq via set ms).
  have h_ms_eq : ms.2.2.2.2 = (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2 := rfl
  have h_ms_lo_eq : (val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 :)
      = val256 (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).1
               (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.1
               (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.1
               (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.1 := rfl
  have h_mulsub : ms.2.2.2.2.toNat * 2^256 +
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) - u4.toNat * 2^256) =
      val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 +
        (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 1) *
          (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
            2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64)) := by
    rw [ha_val, hb_val, h_ms_eq, h_ms_lo_eq]
    have h := h_mulsub_eq
    rw [h_qHat_eq, h_norm_b'] at h
    have h_u_val : val256 u0 u1 u2 u3 =
        a.toNat * 2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) - u4.toNat * 2^256 := by
      have h2 := h_norm_u'
      omega
    rw [h_u_val] at h
    omega
  -- Align h_amod_pow_lt's `2^s` form (no `% 64`) with the Nat lemma's expected form.
  have h_amod_pow_lt' :
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) < 2 ^ 256 := by
    rw [h_s_eq]; exact h_amod_pow_lt
  -- Final composition: apply the closed Nat lemma with all 6 preconditions.
  show ms.2.2.2.2.toNat = u4.toNat + 1
  exact c3_eq_u4_plus_one_from_mulsub_addback_bounds
    (val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1)
    (val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1)
    (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3))
    (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    ((clzResult (b.getLimbN 3)).1.toNat % 64) u4.toNat ms.2.2.2.2.toNat
    h_mulsub h_addback h_u4_le h_post1_lt h_amod_pow_lt' h_u4_lt_c3

/-- **Wrapper: c3 = u4 + 1 in single-addback (irreducible-form).**

    Wraps `c3_n_eq_u4_plus_one_of_single_addback` to take its hypothesis
    in irreducible-bundle form (`algCallAddbackBeqCarry a b ≠ 0`), avoiding
    the deep let-chain elaboration cost at the call site. The conclusion
    is also stated in irreducible form for symmetry.

    Internally unfolds the irreducible defs and applies the closed sub-stub.
    Caller should provide hb3nz, hshift_nz, hborrow, hsem, and the
    irreducible-form hcarry_nz. -/
theorem algCallAddbackBeqMsC3_eq_u4_plus_one_of_single_addback
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    (algCallAddbackBeqMsC3 a b).toNat = (algCallAddbackBeqU4 a b).toNat + 1 := by
  -- Unfold the irreducible defs to get the let-chain forms.
  show _ = _
  rw [show (algCallAddbackBeqMsC3 a b).toNat = _ from by
        unfold algCallAddbackBeqMsC3; rfl,
      show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl]
  rw [algCallAddbackBeqCarry_unfold] at hcarry_nz
  exact c3_n_eq_u4_plus_one_of_single_addback a b hb3nz hshift_nz hborrow hsem hcarry_nz


/-- **Sub-stub: post1 = a%b * 2^s from c3 = u4 + 1 (pure Nat).**

    Given the closed Nat lemmas + `c3_n_eq_u4_plus_one_of_single_addback`'s
    output, this directly gives val256(post1_low4) = a%b * 2^s.

    Composition of:
    - `val256_post1_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4` (closed).
    - `c3 = u4 + 1` (substituted in).

    Result: post1_val + 0*2^256 = a%b * 2^s + 0, i.e., post1_val = a%b * 2^s. -/
theorem post1_eq_mod_times_pow_s_of_c3_eq_u4_plus_one
    (post1_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) = ms_val + (a_val / b_val + 1) * (b_val * 2^s))
    (h_addback : post1_val + 2^256 = ms_val + b_val * 2^s)
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s)
    (h_c3_eq : c3 = u4 + 1) :
    post1_val = a_val % b_val * 2^s := by
  have h_id := val256_post1_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    post1_val ms_val a_val b_val s u4 c3 h_mulsub h_addback h_u4_le
  -- h_id: post1_val + (u4 + 1) * 2^256 = a%b * 2^s + c3 * 2^256
  -- h_c3_eq: c3 = u4 + 1
  rw [h_c3_eq] at h_id
  omega

/-- **Pure-Nat: post1_val = a%b * 2^s from mulsub+addback Euclidean + bounds.**

    Packaged single-shot sub-stub for the call+addback BEQ MOD adapter's
    single-addback branch (PR #1253). Combines:
    - `c3_eq_u4_plus_one_from_mulsub_addback_bounds` (yields c3 = u4 + 1).
    - `post1_eq_mod_times_pow_s_of_c3_eq_u4_plus_one` (val256-level result).

    Avoids exposing the intermediate `c3 = u4 + 1` step at the call site.
    Once the Word-level bridge to the parent's let-chain is figured out, the
    parent can apply this directly to skip an entire chained `c3` derivation.

    The hypotheses are exactly the 6 preconditions for the c3-pinning lemma:
    `h_mulsub` already encodes `qHat = a/b + 1` via the `(a_val / b_val + 1)`
    factor on its RHS. -/
theorem post1_val_eq_amod_pow_s_pure_nat
    (post1_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) = ms_val + (a_val / b_val + 1) * (b_val * 2^s))
    (h_addback : post1_val + 2^256 = ms_val + b_val * 2^s)
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s)
    (h_post1_lt : post1_val < 2^256)
    (h_amod_pow_lt : a_val % b_val * 2^s < 2^256)
    (h_u4_lt_c3 : u4 < c3) :
    post1_val = a_val % b_val * 2^s := by
  have h_c3_eq := c3_eq_u4_plus_one_from_mulsub_addback_bounds
    post1_val ms_val a_val b_val s u4 c3
    h_mulsub h_addback h_u4_le h_post1_lt h_amod_pow_lt h_u4_lt_c3
  exact post1_eq_mod_times_pow_s_of_c3_eq_u4_plus_one
    post1_val ms_val a_val b_val s u4 c3 h_mulsub h_addback h_u4_le h_c3_eq

/-- **Wrapper: post1Val = a%b * 2^s in single-addback (irreducible-form)** (CLOSED).

    Given the algorithm's invariants in single-addback (carry ≠ 0), the val256
    of the first-addback post1 limbs at normalized inputs equals
    `val256(a) % val256(b) * 2^s` — i.e., the un-truncated form of the
    Knuth-style remainder.

    Stated in irreducible-bundle form (`algCallAddbackBeqPost1Val a b` =
    val256-of-post1; `algCallAddbackBeqCarry a b ≠ 0` = single-addback)
    so the call site doesn't pay the deep let-chain elaboration cost.

    Composes the 6 closed Word-level preconditions through
    `post1_val_eq_amod_pow_s_pure_nat`:
    - `algCallAddbackBeqPost1Val_lt_pow256`                    (h_post1_lt)
    - `algCallAddbackBeq_amod_pow_s_lt_pow256`                 (h_amod_pow_lt)
    - `algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat` (h_u4_lt_c3)
    - `algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s`     (h_u4_le)
    - `algCallAddbackBeq_addback_euclidean_carry_one`          (h_addback)
    - `algCallAddbackBeq_mulsub_euclidean`                     (h_mulsub) -/
theorem algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqPost1Val a b =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
  exact post1_val_eq_amod_pow_s_pure_nat
    (algCallAddbackBeqPost1Val a b)
    (algCallAddbackBeqMsLowVal a b)
    (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3))
    (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    ((clzResult (b.getLimbN 3)).1.toNat % 64)
    (algCallAddbackBeqU4 a b).toNat
    (algCallAddbackBeqMsC3 a b).toNat
    (algCallAddbackBeq_mulsub_euclidean a b hshift_nz hborrow hsem hcarry_nz)
    (algCallAddbackBeq_addback_euclidean_carry_one a b hshift_nz hcarry_nz)
    (algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s a b hshift_nz)
    (algCallAddbackBeqPost1Val_lt_pow256 a b)
    (algCallAddbackBeq_amod_pow_s_lt_pow256 a b hb3nz)
    (algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat a b hborrow)

/-- **Unified parent-form: post1Val = a%b * 2^s in single-addback** (CLOSED).

    Drop-in replacement for the parent adapter's single-addback branch:
    takes the parent's local `(64-s)`-form `addbackN4_carry … ≠ 0`
    hypothesis directly, and returns the val256 equation in the parent's
    `(64-s)`-form too. Internally chains the carry/post1Val bridges with
    the closed wrapper. -/
theorem parent_post1Val_eq_amod_pow_s_of_single_addback
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz :
      let s := (clzResult (b.getLimbN 3)).1.toNat % 64
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
      addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0) :
    let s := (clzResult (b.getLimbN 3)).1.toNat % 64
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
    val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ s := by
  intro s b0' b1' b2' b3' u0 u1 u2 u3 u4 qHat ms post1
  -- Bridge hcarry_nz: parent's (64-s) carry → algCallAddbackBeqCarry a b ≠ 0.
  have h_carry_bridge := algCallAddbackBeqCarry_eq_parent_64ms_form a b hshift_nz
  simp only [] at h_carry_bridge
  have hcarry_irreducible : algCallAddbackBeqCarry a b ≠ 0 := by
    rw [h_carry_bridge]; exact hcarry_nz
  -- Apply the closed wrapper.
  have h_wrapper := algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback
    a b hb3nz hshift_nz hborrow hsem hcarry_irreducible
  -- Bridge the wrapper's irreducible-form post1Val to parent's (64-s)-form post1.
  have h_post1_bridge := algCallAddbackBeqPost1Val_eq_parent_64ms_form a b hshift_nz
  simp only [] at h_post1_bridge
  rw [h_post1_bridge] at h_wrapper
  exact h_wrapper

/-- **Sub-lemma: per-limb mod equations using irreducible Post1Limb bundles** (CLOSED).

    Drop-in for the parent adapter's single-addback branch: produces per-limb
    equations `(EvmWord.mod a b).getLimbN i = (Limb{i} >>> s) ||| (Limb{i+1} <<< (64-s))`
    using the irreducible `algCallAddbackBeqPost1Limb{0..3}` bundles, keeping
    the goal small.

    Composes:
      * `parent_post1Val_eq_amod_pow_s_of_single_addback` (val256 fact, parent shape)
      * `algCallAddbackBeqPost1Val_eq_val256_limbs` (val256 ↔ per-limb irreducibles)
      * `denorm_4limb_eq_mod_of_val256_eq_amod_pow_s` (val256 → per-limb evmWordIs) -/
theorem mod_n4_call_addback_beq_single_addback_post1_limbs_close
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    let s := (clzResult (b.getLimbN 3)).1.toNat % 64
    (EvmWord.mod a b).getLimbN 0 =
      ((algCallAddbackBeqPost1Limb0 a b) >>> s) |||
        ((algCallAddbackBeqPost1Limb1 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 1 =
      ((algCallAddbackBeqPost1Limb1 a b) >>> s) |||
        ((algCallAddbackBeqPost1Limb2 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 2 =
      ((algCallAddbackBeqPost1Limb2 a b) >>> s) |||
        ((algCallAddbackBeqPost1Limb3 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 3 =
      (algCallAddbackBeqPost1Limb3 a b) >>> s := by
  intro s
  -- Step 1: get the val256 fact.
  have h_wrapper := algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback
    a b hb3nz hshift_nz hborrow hsem hcarry_nz
  -- Step 2: rewrite val256 in terms of irreducible per-limb bundles.
  rw [algCallAddbackBeqPost1Val_eq_val256_limbs] at h_wrapper
  -- Step 3: derive bounds on s.
  have h_clz_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_s_pos : 0 < s := by show 0 < _; omega
  have h_s_lt_64 : s < 64 := by show _ < 64; omega
  -- Step 4: apply denorm_4limb to get per-limb equations.
  exact denorm_4limb_eq_mod_of_val256_eq_amod_pow_s
    (a := a) (b := b)
    (X1 := algCallAddbackBeqPost1Limb0 a b)
    (X2 := algCallAddbackBeqPost1Limb1 a b)
    (X3 := algCallAddbackBeqPost1Limb2 a b)
    (X4 := algCallAddbackBeqPost1Limb3 a b)
    h_s_pos h_s_lt_64 hb3nz h_wrapper

/-- **Call+addback BEQ n=4 MOD denorm adapter** (single-addback CLOSED, double-addback SORRY).

    Stack-level adapter folding the 4 denormalized remainder slots at
    sp+32..sp+56 into `evmWordIs (sp+32) (EvmWord.mod a b)` for the
    call+addback BEQ path.

    Signature uses irreducible Un{i}Out bundles to keep the goal small
    (a previous version had a 246-line proof body wrestling with deep
    inline let-chains). The proof fans out via:
      - `algCallAddbackBeqUn{i}Out_eq_post1Limb{i}_of_single_addback`
        (folds Un{i}Out → Post1Limb{i} under hcarry ≠ 0).
      - `mod_n4_call_addback_beq_single_addback_post1_limbs_close`
        (per-limb mod equations in irreducible form).
      - `evmWordIs_sp32_limbs_eq.symm` (final fold).

    Double-addback branch (carry = 0) remains sorry pending Knuth bound
    for c3 = 1. -/
theorem output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm
    (sp : Word) (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let un0Out := algCallAddbackBeqUn0Out a b
    let un1Out := algCallAddbackBeqUn1Out a b
    let un2Out := algCallAddbackBeqUn2Out a b
    let un3Out := algCallAddbackBeqUn3Out a b
    (((sp + 32) ↦ₘ ((un0Out >>> shift) ||| (un1Out <<< (64 - shift)))) **
     ((sp + 40) ↦ₘ ((un1Out >>> shift) ||| (un2Out <<< (64 - shift)))) **
     ((sp + 48) ↦ₘ ((un2Out >>> shift) ||| (un3Out <<< (64 - shift)))) **
     ((sp + 56) ↦ₘ (un3Out >>> shift))) =
    evmWordIs (sp + 32) (EvmWord.mod a b) := by
  intro shift un0Out un1Out un2Out un3Out
  by_cases hcarry : algCallAddbackBeqCarry a b = 0
  · -- Double-addback branch (carry = 0). Pending Knuth bound for c3 = 1.
    sorry
  · -- Single-addback branch: fold Un{i}Out → Post1Limb{i} via bridges.
    rw [show un0Out = algCallAddbackBeqPost1Limb0 a b from
          algCallAddbackBeqUn0Out_eq_post1Limb0_of_single_addback a b hcarry,
        show un1Out = algCallAddbackBeqPost1Limb1 a b from
          algCallAddbackBeqUn1Out_eq_post1Limb1_of_single_addback a b hcarry,
        show un2Out = algCallAddbackBeqPost1Limb2 a b from
          algCallAddbackBeqUn2Out_eq_post1Limb2_of_single_addback a b hcarry,
        show un3Out = algCallAddbackBeqPost1Limb3 a b from
          algCallAddbackBeqUn3Out_eq_post1Limb3_of_single_addback a b hcarry]
    have h_limbs := mod_n4_call_addback_beq_single_addback_post1_limbs_close
      a b hb3nz hshift_nz hborrow hsem hcarry
    simp only [] at h_limbs
    exact (evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _
      h_limbs.1 h_limbs.2.1 h_limbs.2.2.1 h_limbs.2.2.2).symm

/-- **EVM-stack-level MOD spec on the n=4 call+addback BEQ sub-path (SORRY).**

    Mirror of `evm_div_n4_call_addback_beq_stack_spec` for MOD. Depends on
    the `output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm` adapter
    above (currently sorry). Once the adapter is filled in, this stack spec
    reduces mechanically using the template from
    `evm_mod_n4_call_skip_stack_spec` (landed in #1207). -/
theorem evm_mod_n4_call_addback_beq_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) := by
  have h_pre := evm_mod_n4_full_call_addback_beq_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  have hshift_le_63 := clzResult_fst_toNat_le (b.getLimbN 3)
  have hshift_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    by_contra h
    push Not at h
    apply hshift_nz
    apply BitVec.eq_of_toNat_eq
    rw [show (0 : Word).toNat = 0 from rfl]; omega
  have hmod_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have h0se12 : signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1 =
      -((clzResult (b.getLimbN 3)).1) := by rw [signExtend12_0]; simp
  have hanti_toNat_mod :
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat := by
    rw [h0se12, BitVec.toNat_neg]
    have : ((clzResult (b.getLimbN 3)).1).toNat ≤ 2^64 := by
      have := ((clzResult (b.getLimbN 3)).1).isLt; omega
    omega
  have h_slot := output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm sp a b
    hb3nz hshift_nz hcarry2_nz hborrow hsem
  refine cpsTriple_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  simp only [fullModN4CallAddbackBeqPost_unfold, denormModPost_unfold] at hq
  -- Fold hq's inline un{i}Out forms to the irreducible Un{i}Out names
  -- (matching the parent adapter's new signature).
  simp only [← algCallAddbackBeqUn0Out_unfold, ← algCallAddbackBeqUn1Out_unfold,
             ← algCallAddbackBeqUn2Out_unfold, ← algCallAddbackBeqUn3Out_unfold] at hq
  apply mod_n4_call_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.mod a b) = _ from h_slot.symm]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  simp only [hmod_eq, hanti_toNat_mod] at hq ⊢
  xperm_hyp hq

end EvmAsm.Evm64
