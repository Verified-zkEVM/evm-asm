/-
  EvmAsm.Evm64.SMod.Compose.ResultSignFixOwnV5

  v5 SMOD result-sign-fix specs over `smodCodeV5`, progressively consuming owned
  registers (`x10`, `x7`, `x11`).  Verbatim mirrors of the `smodCodeV4` wrappers
  in `ResultSignFixOwn.lean` (swap `smodCodeV4`→`smodCodeV5` and the recursive
  code-subsumption `smodCodeV4_resultSignFix_sub`→`smodCodeV5_resultSignFix_sub`).
  The SMOD result-sign-fix negates the remainder by the dividend's sign (x13),
  so these reuse the SMOD-local `smodResultSignFixPre*`/`smodResultSignFixPost`
  assertions (code-agnostic).
-/

import EvmAsm.Evm64.SMod.Compose.ResultSignFixOwn
import EvmAsm.Evm64.SMod.Compose.BaseCodeV5

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64

theorem resultSignFix_spec_in_smodCodeV5
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (smodCodeV5 base)
      (smodResultSignFixPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (smodResultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [smodResultSignFixPre_unfold, smodResultSignFixPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x13 .x10 .x7 .x11 0 8 16 24
          (base + resultSignFixOff)) a = some i →
        (smodCodeV5 base) a = some i := by
    intro a i h
    exact smodCodeV5_resultSignFix_sub (base := base) a i
      (by simpa [resultSignFixCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x13 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + resultSignFixOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono hSpec

theorem resultSignFix_regOwn_x10_spec_in_smodCodeV5
    (sp sign valueOld carryOld limb0 limb1 limb2 limb3 : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (smodCodeV5 base)
      (smodResultSignFixPreOwnX10 sp sign valueOld carryOld
        limb0 limb1 limb2 limb3)
      (smodResultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [smodResultSignFixPreOwnX10_unfold]
  apply EvmAsm.Rv64.cpsTripleWithin_of_forall_regIs_to_regOwn
  intro maskOld
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      rw [smodResultSignFixPre_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_spec_in_smodCodeV5 sp sign maskOld valueOld carryOld
      limb0 limb1 limb2 limb3 base)

theorem resultSignFix_regOwn_x10_x7_spec_in_smodCodeV5
    (sp sign carryOld limb0 limb1 limb2 limb3 : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (smodCodeV5 base)
      (smodResultSignFixPreOwnX10X7 sp sign carryOld limb0 limb1 limb2 limb3)
      (smodResultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [smodResultSignFixPreOwnX10X7_unfold]
  apply EvmAsm.Rv64.cpsTripleWithin_of_forall_regIs_to_regOwn
  intro valueOld
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      rw [smodResultSignFixPreOwnX10_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_regOwn_x10_spec_in_smodCodeV5 sp sign valueOld carryOld
      limb0 limb1 limb2 limb3 base)

theorem resultSignFix_regOwn_scratch_spec_in_smodCodeV5
    (sp sign limb0 limb1 limb2 limb3 : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (smodCodeV5 base)
      (smodResultSignFixPreOwnScratch sp sign limb0 limb1 limb2 limb3)
      (smodResultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [smodResultSignFixPreOwnScratch_unfold]
  apply EvmAsm.Rv64.cpsTripleWithin_of_forall_regIs_to_regOwn
  intro carryOld
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      rw [smodResultSignFixPreOwnX10X7_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_regOwn_x10_x7_spec_in_smodCodeV5 sp sign carryOld
      limb0 limb1 limb2 limb3 base)

end EvmAsm.Evm64.SMod.Compose
