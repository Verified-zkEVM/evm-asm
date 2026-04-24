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
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Shift0
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4Shift0

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

/-- **Call+addback BEQ n=4 MOD denorm adapter (SORRY).** Stack-level adapter
    folding the four denormalized remainder slots at `sp+32..sp+56` into
    `evmWordIs (sp+32) (EvmWord.mod a b)` for the call+addback BEQ path.

    Mirror of `output_slot_to_evmWordIs_mod_n4_call_skip_denorm` but for the
    addback branch. The post's mulsub uses raw `qHat = div128Quot …`, then 1
    or 2 addbacks correct it so the post-addback remainder equals
    `val256(a_norm) - q_out * val256(b_norm)` (where q_out is the corrected
    quotient, matching `n4CallAddbackBeqSemanticHolds`).

    Proof approach (to fill in):
    1. Use `hsem` to derive `q_out * val256(b) ≤ val256(a)` (bound needed for
       the parameterized `val256_denorm_eq_val256_mod_of_overestimate`).
    2. Show the post-addback partial remainder equals `mulsubN4 q_out b_norm
       a_norm`'s output limbs (via addback correctness theorems combined with
       Euclidean equations).
    3. Apply `val256_denorm_eq_val256_mod_of_overestimate` with qHat = q_out
       (the parameterized chain from the landed call-skip MOD PR).
    4. Use `mod_of_val256_eq_mod` + `evmWordIs_sp32_limbs_eq` to fold into
       `evmWordIs`. -/
theorem output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm
    (sp : Word) (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
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
    let c3 := ms.2.2.2.2
    let u4_new := u4 - c3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let un0Out := if carry = 0 then ab'.1 else ab.1
    let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
    let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
    let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
    (((sp + 32) ↦ₘ ((un0Out >>> shift) ||| (un1Out <<< (64 - shift)))) **
     ((sp + 40) ↦ₘ ((un1Out >>> shift) ||| (un2Out <<< (64 - shift)))) **
     ((sp + 48) ↦ₘ ((un2Out >>> shift) ||| (un3Out <<< (64 - shift)))) **
     ((sp + 56) ↦ₘ (un3Out >>> shift))) =
    evmWordIs (sp + 32) (EvmWord.mod a b) := by
  -- TODO(#66 follow-up): key math gap. Steps:
  -- 1. From hsem, derive q_out * val256(b) ≤ val256(a) where q_out is
  --    qHat + (1 or 2) × (-1). (q_out.toNat = val256(a)/val256(b), and
  --    division q * b ≤ a is standard.)
  -- 2. Via addback correctness + mulsub Euclidean + hsem, show
  --    val256(un0Out..un3Out) = val256(a_norm) - q_out * val256(b_norm).
  -- 3. Apply the parameterized denorm chain (landed in #1207) with
  --    qHat = q_out to fold into EvmWord.mod a b.
  sorry

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
