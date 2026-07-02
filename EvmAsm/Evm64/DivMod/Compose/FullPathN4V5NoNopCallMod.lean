/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopCallMod

  MOD mirror of `FullPathN4V5NoNopCall`: the n=4 loop body lifted to `modCode_noNop_v5`
  via `sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5` (raw shared-code body reused).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopCall

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

theorem divK_loop_body_n4_call_skip_j0_norm_v5_noNop_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopBodyN4CallJ0NormPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (loopBodyN4CallSkipJ0PostV5 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw := divK_loop_body_n4_call_skip_j0_v5_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
    retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5) raw
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [loopBodyN4CallJ0NormPre_unfold] at hp
      rw [loopBodyN4CallSkipJ0PreV4_unfold]
      rw [loopBodyN4CallSkipJ0Pre_unfold]
      simp only [se12_32, se12_40, se12_48, se12_56,
                 u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
                 u_base_off4072_j0, u_base_off4064_j0, q_addr_j0]
      xperm_hyp hp)
    (fun _ hp => hp)
    raw'

end EvmAsm.Evm64
