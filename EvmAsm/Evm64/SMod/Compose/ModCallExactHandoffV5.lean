/-
  EvmAsm.Evm64.SMod.Compose.ModCallExactHandoffV5

  v5 SMOD dispatch-ready handoff: wraps the v5 code adapter
  (`evm_mod_callable_v5_x9owned_framed_spec_in_smodCodeV5`, step 1) in the SMOD
  abs/sign private frame (`smodModCallPrivateFrame` = x8/x13/x18, no x9), landing
  `saveRaAbsThenModCallCallablePost` (which itself carries `regOwn .x9`) with the
  `sp+3936` scratch cell carried through.  v5 analog of the v4
  `saveRaAbsThenModCallDispatchReadyPost_callable_from_noNop_spec_in_smodCodeV4`.

  Step 2 of the SMOD `.proven` flip over `evm_mod_callable_v5`.  Because M2's mod
  callable spec is UNCONDITIONAL, this takes no `h_stack` hypothesis (unlike v4).
-/

import EvmAsm.Evm64.SMod.Compose.ModCallExactCallableV5
import EvmAsm.Evm64.SMod.Compose.ModCallGenericHandoff
import EvmAsm.Evm64.SMod.Compose.DispatchReadyView

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- v5 dispatch-ready callable handoff: from `saveRaAbsThenModCallDispatchReadyPost`
    (+ the `sp+3936` scratch cell) to `saveRaAbsThenModCallCallablePost` with the
    scratch cell carried, over `smodCodeV5`.  Feeds the unconditional M2 callable
    (step 1) — no `h_stack`. -/
theorem saveRaAbsThenModCallDispatchReadyPost_x9owned_spec_in_smodCodeV5
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbase : base &&& 1 = 0)
    (halign : (((base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) :
    cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (smodCodeV5 base)
      (saveRaAbsThenModCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)
      (saveRaAbsThenModCallCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       memOwn (sp + signExtend12 (3936 : BitVec 12))) := by
  let dividendAbsWord : EvmWord :=
    smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord : EvmWord :=
    smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSign := smodAbsSign divisorTop
  let divisorMask := smodAbsMask divisorTop
  let divisorSum3 := smodAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry3 := smodAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let retAddr := (base + modCallOff) + 4
  let privateFrame := smodModCallPrivateFrame vRa dividendTop
  have hCallable :=
    evm_mod_callable_v5_x9owned_framed_spec_in_smodCodeV5
      (F := privateFrame)
      sp base divisorSign retAddr
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem halign
  rw [show retAddr &&& ~~~(1 : Word) = base + resultSignFixOff from by
    dsimp only [retAddr]; exact modCall_return_andn_one_eq_resultSignFixOff base hbase]
    at hCallable
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [saveRaAbsThenModCallDispatchReadyPost_unfold_smod_components] at hp
      dsimp only at hp
      rw [EvmAsm.Evm64.divModStackDispatchPreNoX1_unfold]
      dsimp only [dividendAbsWord, divisorAbsWord, divisorSign, retAddr,
        divisorMask, divisorSum3, divisorCarry3, privateFrame]
      rw [smodModCallPrivateFrame_unfold]
      dsimp only
      rw [EvmAsm.Evm64.divModStackDispatchPreNoX1_unfold] at hp
      xperm_chunked hp)
    (fun h hp => by
      simp only [EvmAsm.Evm64.modStackDispatchPostCallableX9Owned_unfold] at hp
      dsimp only [privateFrame] at hp
      rw [smodModCallPrivateFrame_unfold] at hp
      rw [saveRaAbsThenModCallCallablePost_unfold]
      dsimp only [dividendAbsWord, divisorAbsWord, privateFrame]
      rw [smodModCallPrivateFrame_unfold]
      dsimp only at hp ⊢
      xperm_chunked hp)
    hCallable

end EvmAsm.Evm64.SMod.Compose
