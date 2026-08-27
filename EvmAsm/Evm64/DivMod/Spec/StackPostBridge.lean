/-
  EvmAsm.Evm64.DivMod.Spec.StackPostBridge

  V4 stack-post bridge: weaken `divStackDispatchPostCallableExactFrame`
  (which exposes `x1` and `x9` as exact-value atoms) to the public
  `divStackDispatchPost` (which uses anonymous `regOwn .x1` / `regOwn .x9`).

  Required by the final per-lane unconditional wrappers (N1/N2/N3/N4) to
  weaken their callable-frame postcondition to the public DIV stack-spec
  post.  Bead `evm-asm-9iqmw.7.1.7.2.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallablePost
public import EvmAsm.Rv64.Tactics.XSimp

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Combine the no-x1 scratch ownership with `regOwn .x1` to obtain the
    full call-scratch ownership.  These differ only in associativity of
    `sepConj` (`**`), discharged by `xperm_hyp`. -/
theorem divScratchOwnCallNoX1_with_regOwn_x1
    (sp : Word) :
    ∀ h, (divScratchOwnCallNoX1 sp ** regOwn .x1) h →
      divScratchOwnCall sp h := by
  intro h hp
  rw [divScratchOwnCall_unfold, divScratchOwnCallNoX1_unfold] at *
  xperm_hyp hp

/-- V4 stack-post bridge: weaken the callable-frame post (with exact
    `raVal` and `x9Val`) to the public dispatch post (with anonymous
    `regOwn` slots). -/
theorem divStackDispatchPostCallableExactFrame_weaken
    (sp : Word) (a b : EvmWord) (raVal x9Val : Word) :
    ∀ h, divStackDispatchPostCallableExactFrame sp a b raVal x9Val h →
      divStackDispatchPost sp a b h := by
  intro h hp
  rw [divStackDispatchPostCallableExactFrame_unfold,
      divStackDispatchPostCallable_unfold,
      divStackDispatchPost_unfold] at *
  -- Goal-form: LHS = (((.x12 ↦ᵣ (sp+32)) ** regOwn .x2 ** ... **
  --   divScratchOwnCallNoX1 sp) ** (.x1 ↦ᵣ raVal)) ** (.x9 ↦ᵣ x9Val)
  -- RHS = (.x12 ↦ᵣ (sp+32)) ** regOwn .x9 ** regOwn .x2 ** ... **
  --   divScratchOwnCall sp
  -- Strategy: weaken .x1 and .x9 atoms to regOwn, then merge with
  -- divScratchOwnCallNoX1 to recover divScratchOwnCall, then permute.
  -- We do this by first establishing the weaker LHS form.
  have step1 : ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x2 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
        evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
        divScratchOwnCallNoX1 sp) ** regOwn .x1) ** regOwn .x9) h := by
    revert hp
    apply sepConj_mono
    · apply sepConj_mono
      · exact fun _ hp => hp
      · exact regIs_implies_regOwn _
    · exact regIs_implies_regOwn _
  -- Now permute step1 into the dispatch-post shape.
  have step2 : ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x9 ** regOwn .x2 **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
      evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
      (divScratchOwnCallNoX1 sp ** regOwn .x1)) h := by
    xperm_hyp step1
  -- Finally merge divScratchOwnCallNoX1 ** regOwn .x1 into divScratchOwnCall.
  revert step2
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact divScratchOwnCallNoX1_with_regOwn_x1 sp

end EvmAsm.Evm64
