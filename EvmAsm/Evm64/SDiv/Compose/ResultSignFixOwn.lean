/-
  EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwn

  Register-ownership wrappers for the SDIV result sign-fix block. The DIV
  callable post exposes sign-fix scratch registers as `regOwn`; this file
  starts packaging the standard `resultSignFix_spec_in_sdivCode` behind that
  shape one register at a time.
-/

import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFixBlockSpec
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwnPre
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

/-- v4 SDIV result sign-fix spec that consumes owned `x10` instead of requiring
    a concrete old mask value. -/
theorem resultSignFix_regOwn_x10_spec_in_sdivCodeV4
    (sp sign valueOld carryOld limb0 limb1 limb2 limb3 : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCodeV4 base)
      (resultSignFixPreOwnX10 sp sign valueOld carryOld limb0 limb1 limb2 limb3)
      (resultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [resultSignFixPreOwnX10_unfold]
  apply EvmAsm.Rv64.cpsTripleWithin_of_forall_regIs_to_regOwn
  intro maskOld
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      rw [resultSignFixPre_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_spec_in_sdivCodeV4 sp sign maskOld valueOld carryOld
      limb0 limb1 limb2 limb3 base)

/-- v4 SDIV result sign-fix spec that consumes owned `x10` and `x7`, leaving
    only the old `x11` carry value concrete. -/
theorem resultSignFix_regOwn_x10_x7_spec_in_sdivCodeV4
    (sp sign carryOld limb0 limb1 limb2 limb3 : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCodeV4 base)
      (resultSignFixPreOwnX10X7 sp sign carryOld limb0 limb1 limb2 limb3)
      (resultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [resultSignFixPreOwnX10X7_unfold]
  apply EvmAsm.Rv64.cpsTripleWithin_of_forall_regIs_to_regOwn
  intro valueOld
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      rw [resultSignFixPreOwnX10_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_regOwn_x10_spec_in_sdivCodeV4 sp sign valueOld carryOld
      limb0 limb1 limb2 limb3 base)

/-- v4 SDIV result sign-fix spec that consumes owned `x10`, `x7`, and `x11`. -/
theorem resultSignFix_regOwn_scratch_spec_in_sdivCodeV4
    (sp sign limb0 limb1 limb2 limb3 : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCodeV4 base)
      (resultSignFixPreOwnScratch sp sign limb0 limb1 limb2 limb3)
      (resultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [resultSignFixPreOwnScratch_unfold]
  apply EvmAsm.Rv64.cpsTripleWithin_of_forall_regIs_to_regOwn
  intro carryOld
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      rw [resultSignFixPreOwnX10X7_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_regOwn_x10_x7_spec_in_sdivCodeV4 sp sign carryOld
      limb0 limb1 limb2 limb3 base)

end EvmAsm.Evm64.SDiv.Compose
