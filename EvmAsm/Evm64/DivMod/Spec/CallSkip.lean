/-
  EvmAsm.Evm64.DivMod.Spec.CallSkip

  Call-trial precondition bundles for the 256-bit EVM DIV and MOD
  programs.

  The call-trial variants use `divScratchValuesCall` (19 cells — the
  base `divScratchValues` 15 cells plus 4 extras for the `div128`
  subroutine call path). Used as preconditions of the forthcoming
  `evm_{div,mod}_n4_full_call_{skip,addback}_stack_pre_spec` theorems.

  `divN4StackPreCall` sits next to `divN4StackPre` in `Spec.Base`; this
  file adds the MOD-side counterpart `modN4StackPreCall`.
-/

import EvmAsm.Evm64.DivMod.Spec.Base
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4Shift0
import EvmAsm.Evm64.EvmWordArith.Div128Shift0
import EvmAsm.Evm64.EvmWordArith.AddbackBorrowExtract
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2
import EvmAsm.Evm64.DivMod.Spec.CallSkipOverestimateBridge

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
    Paired with `modN4StackPreCall` for
    `evm_mod_n4_call_skip_stack_spec_within`. -/
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
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 126 + 2 + 23 + 10)
      base (base + nopOff) (divCode base)
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
  exact cpsTripleWithin_weaken
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
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 126 + 2 + 23 + 10)
      base (base + nopOff) (divCode base)
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
  exact cpsTripleWithin_weaken
    (fun _ hp => by rw [divN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper over `evm_mod_n4_full_call_skip_spec`. Same shape
    as `evm_div_n4_full_call_skip_stack_pre_spec` but for the MOD path:
    `divCode → modCode`, `evm_div_n4_full_call_skip_spec →
    evm_mod_n4_full_call_skip_spec`, and `fullDivN4CallSkipPost →
    fullModN4CallSkipPost`. -/
theorem evm_mod_n4_full_call_skip_stack_pre_spec_within (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTripleWithin 264 base (base + nopOff) (modCode base)
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
  have hraw := evm_mod_n4_full_call_skip_spec_within sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_nz halign hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_mod_n4_full_call_skip_stack_pre_spec_within`: takes
    the precondition as a single `modN4StackPreCall` atom. Mirror of
    `evm_div_n4_full_call_skip_stack_pre_spec_bundled`. -/
theorem evm_mod_n4_full_call_skip_stack_pre_spec_bundled_within (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTripleWithin 264 base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_mod_n4_full_call_skip_stack_pre_spec_within sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
  exact cpsTripleWithin_weaken
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
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 202 + 2 + 23 + 10)
      base (base + nopOff) (divCode base)
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
    hbnz' hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  exact cpsTripleWithin_weaken
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
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 202 + 2 + 23 + 10)
      base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_div_n4_full_call_addback_beq_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  exact cpsTripleWithin_weaken
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
theorem evm_mod_n4_full_call_addback_beq_stack_pre_spec_within (sp base : Word)
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
    cpsTripleWithin 340 base (base + nopOff) (modCode base)
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
  have hraw := evm_mod_n4_full_call_addback_beq_spec_within sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_mod_n4_full_call_addback_beq_stack_pre_spec_within`:
    takes the precondition as a single `modN4StackPreCall` atom. Mirror
    of `evm_div_n4_full_call_addback_beq_stack_pre_spec_bundled`. -/
theorem evm_mod_n4_full_call_addback_beq_stack_pre_spec_bundled_within (sp base : Word)
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
    cpsTripleWithin 340 base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_mod_n4_full_call_addback_beq_stack_pre_spec_within sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  exact cpsTripleWithin_weaken
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
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 126 + 12)
      base (base + nopOff) (divCode base)
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
  exact cpsTripleWithin_weaken
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
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 126 + 12)
      base (base + nopOff) (divCode base)
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
  exact cpsTripleWithin_weaken
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
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 126 + 12)
      base (base + nopOff) (modCode base)
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
  exact cpsTripleWithin_weaken
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
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 126 + 12)
      base (base + nopOff) (modCode base)
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
  exact cpsTripleWithin_weaken
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
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 202 + 12)
      base (base + nopOff) (divCode base)
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
  exact cpsTripleWithin_weaken
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
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 202 + 12)
      base (base + nopOff) (divCode base)
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
  exact cpsTripleWithin_weaken
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
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 202 + 12)
      base (base + nopOff) (modCode base)
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
  exact cpsTripleWithin_weaken
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
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 202 + 12)
      base (base + nopOff) (modCode base)
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
  exact cpsTripleWithin_weaken
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

/-- **`n4CallSkipSemanticHolds` holds unconditionally** under the standard
    call-trial preconditions (CLOSED).

    The semantic-correctness predicate `val256(a)/val256(b) ≤ qHat`
    is exactly Knuth Theorem A (lower bound) at the val256 level —
    formerly issue #65, deferred to "future task". Now closed via
    the existing `div128Quot_call_skip_ge_val256_div_v2` (PR #1154 / V2)
    in `EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2`.

    Removes the need for callers of `evm_div_n4_call_skip_stack_spec`
    and `evm_mod_n4_call_skip_stack_spec` to construct the
    `n4CallSkipSemanticHolds` hypothesis externally. -/
theorem n4CallSkipSemanticHolds_of_call_trial (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b) :
    n4CallSkipSemanticHolds a b := by
  rw [n4CallSkipSemanticHolds_def]
  rw [isCallTrialN4Evm_def] at hcall
  exact div128Quot_call_skip_ge_val256_div_v2
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hb3nz hshift_nz hcall

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
    and `denormDivPost` (no dedicated `_unfold` lemma yet — to be added).

    **Tip**: callers without an externally-supplied
    `n4CallSkipSemanticHolds` should use
    `evm_div_n4_call_skip_stack_spec_unconditional`, which discharges
    that hypothesis automatically (CLOSED via Knuth-A lower bound). -/
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
    cpsTripleWithin 264 base (base + nopOff) (divCode base)
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
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
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

    Reduces to `evm_mod_n4_full_call_skip_stack_pre_spec_bundled_within` + a
    postcondition reshape via `output_slot_to_evmWordIs_mod_n4_call_skip_denorm`
    and `mod_n4_call_skip_stack_weaken`.

    **Tip**: callers without an externally-supplied
    `n4CallSkipSemanticHolds` should use
    `evm_mod_n4_call_skip_stack_spec_unconditional_within`. -/
theorem evm_mod_n4_call_skip_stack_spec_within (sp base : Word)
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
    cpsTripleWithin 264 base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) := by
  have h_pre := evm_mod_n4_full_call_skip_stack_pre_spec_bundled_within sp base a b
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
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
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

/-- **`isSkipBorrowN4CallEvm` and `isAddbackBorrowN4CallEvm` are
    complementary** (CLOSED).

    The two predicates differ only in `=` vs `≠ 0` at the bottom level
    (an `if-then-1-else-0` indicator), so exactly one holds for any
    inputs. Useful for shift_nz top-level dispatchers that route to
    skip vs. addback paths. -/
theorem isSkipBorrowN4CallEvm_or_isAddbackBorrowN4CallEvm (a b : EvmWord) :
    isSkipBorrowN4CallEvm a b ∨ isAddbackBorrowN4CallEvm a b := by
  rw [isSkipBorrowN4CallEvm_def, isAddbackBorrowN4CallEvm_def]
  unfold isSkipBorrowN4Call isAddbackBorrowN4Call
  simp only []
  by_cases h : (if BitVec.ult ((a.getLimbN 3) >>>
        ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
        (mulsubN4_c3 (div128Quot ((a.getLimbN 3) >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((a.getLimbN 2) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((b.getLimbN 2) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))))
          ((b.getLimbN 0) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64))
          (((b.getLimbN 1) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((b.getLimbN 0) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((b.getLimbN 2) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((b.getLimbN 1) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((b.getLimbN 2) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          ((a.getLimbN 0) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64))
          (((a.getLimbN 1) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((a.getLimbN 0) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((a.getLimbN 2) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((a.getLimbN 1) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((a.getLimbN 2) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))))
        then (1 : Word) else 0) = (0 : Word)
  · exact Or.inl h
  · exact Or.inr h

/-- **`evm_div_n4_call_skip_stack_spec` without `hsem`** — discharges the
    semantic hypothesis from the call-trial preconditions (CLOSED).

    Wrapper that calls `evm_div_n4_call_skip_stack_spec` with
    `hsem := n4CallSkipSemanticHolds_of_call_trial _ _ hb3nz hshift_nz hbltu`,
    eliminating the externally-supplied semantic predicate from the API. -/
theorem evm_div_n4_call_skip_stack_spec_unconditional (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTripleWithin 264 base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) :=
  evm_div_n4_call_skip_stack_spec sp base a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
    (n4CallSkipSemanticHolds_of_call_trial a b hb3nz hshift_nz hbltu)

/-- **`evm_mod_n4_call_skip_stack_spec_within` without `hsem`** — same idea
    for MOD. -/
theorem evm_mod_n4_call_skip_stack_spec_unconditional_within (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTripleWithin 264 base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) :=
  evm_mod_n4_call_skip_stack_spec_within sp base a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
    (n4CallSkipSemanticHolds_of_call_trial a b hb3nz hshift_nz hbltu)

end EvmAsm.Evm64
