/-
  EvmAsm.Evm64.DivMod.Spec.StackPostBridgeMod

  MOD mirror of `StackPostBridge.divStackDispatchPostCallableExactFrame_weaken`:
  weaken `modStackDispatchPostCallableExactFrame` to the public
  `modStackDispatchPost` (drop exact `x1`/`x9` to ownership, merge the no-`x1`
  scratch with `regOwn .x1`).  Reuses the shared
  `divScratchOwnCallNoX1_with_regOwn_x1` (scratch ownership is div/mod-agnostic);
  only the post bundle names + the `sp+32` result word differ.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.StackPostBridge
public import EvmAsm.Evm64.DivMod.Spec.CallablePost
public import EvmAsm.Rv64.Tactics.XSimp

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem modStackDispatchPostCallableExactFrame_weaken
    (sp : Word) (a b : EvmWord) (raVal x9Val : Word) :
    ∀ h, modStackDispatchPostCallableExactFrame sp a b raVal x9Val h →
      modStackDispatchPost sp a b h := by
  intro h hp
  rw [modStackDispatchPostCallableExactFrame_unfold,
      modStackDispatchPostCallable_unfold,
      modStackDispatchPost_unfold] at *
  have step1 : ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x2 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
        evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
        divScratchOwnCallNoX1 sp) ** regOwn .x1) ** regOwn .x9) h := by
    revert hp
    apply sepConj_mono
    · apply sepConj_mono
      · exact fun _ hp => hp
      · exact regIs_implies_regOwn _
    · exact regIs_implies_regOwn _
  have step2 : ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x9 ** regOwn .x2 **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
      evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
      (divScratchOwnCallNoX1 sp ** regOwn .x1)) h := by
    xperm_hyp step1
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
