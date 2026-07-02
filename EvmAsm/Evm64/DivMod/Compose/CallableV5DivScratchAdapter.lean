/-
  EvmAsm.Evm64.DivMod.Compose.CallableV5DivScratchAdapter

  Scratch-carrying variant of the layer-1 v5 DIV callable adapter
  (`evm_div_callable_v5_spec_from_noNop_exact_frame`): the callable-ExactFrame
  lanes / the 5-lane callable scaffold all carry the div128 scratch cell
  `(sp+3936 ↦ₘ scratchMem)` in the pre and `memOwn (sp+3936)` in the post (the
  body genuinely writes that cell), but the base adapter's `hStack` has neither.
  This twin threads the `sp+3936` cell through: the div body (`hStack`) consumes
  `scratchMem` and produces `memOwn (sp+3936)`; the `cc_ret` return instruction is
  `pcFree` on `sp+3936`, so the `memOwn` cell is framed through the return step.
  Toward `evm_div_callable_v5`.
-/

import EvmAsm.Evm64.DivMod.CallableV5Div

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- Scratch-carrying v5 callable DIV wrapper: like
    `evm_div_callable_v5_spec_from_noNop_exact_frame` but with the div128 scratch
    cell `sp+3936` threaded (pre `↦ₘ scratchMem`, post `memOwn`). -/
theorem evm_div_callable_v5_spec_from_noNop_exact_frame_scratch
    (sp base x9Val raVal : Word) (a b : EvmWord)
    (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableExactFrame sp a b raVal x9Val **
         memOwn (sp + signExtend12 3936))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal x9Val **
       memOwn (sp + signExtend12 3936)) := by
  rw [divStackDispatchPostCallableExactFrame_unfold] at hStack ⊢
  -- Extend the div body onto the full callable code surface.
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := divCode_noNop_v5_sub_div_callable_code_v5) hStack
  -- Reassociate the post so `x1` is the outermost atom (the frame for `cc_ret`
  -- is everything else, including the `memOwn (sp+3936)` scratch cell).
  have hStackForRet :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (evm_div_callable_code_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (((divStackDispatchPostCallable sp a b ** (.x9 ↦ᵣ x9Val)) **
            memOwn (sp + signExtend12 3936)) ** (.x1 ↦ᵣ raVal)) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v5_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL
      ((divStackDispatchPostCallable sp a b ** (.x9 ↦ᵣ x9Val)) **
        memOwn (sp + signExtend12 3936))
      (by
        rw [divStackDispatchPostCallable_unfold, divScratchOwnCallNoX1_unfold,
          divScratchOwn_unfold]
        pcFree)
      hRet
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr hStackForRet hRetFramed)

end EvmAsm.Evm64
