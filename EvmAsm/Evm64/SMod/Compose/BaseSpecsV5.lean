/-
  EvmAsm.Evm64.SMod.Compose.BaseSpecsV5

  v5 SMOD wrapper-block leaf specs over `smodCodeV5`.  Each is a verbatim mirror
  of the corresponding `_in_smodCodeV4` spec (SavedRaRet.lean / ModCall.lean),
  lifted from `smodCodeV4` → `smodCodeV5` via the banked `smodCodeV5_*_sub`
  subsumptions (BaseCodeV5.lean).  The underlying block programs and their
  `evm_smod_*_block_spec_within` lemmas are code-agnostic, so only the code
  surface changes.  Foothold for the SMOD `.proven` flip over
  `evm_mod_callable_v5`.
-/

import EvmAsm.Evm64.SMod.Compose.BaseCodeV5
import EvmAsm.Evm64.SMod.Compose.SavedRaRet
import EvmAsm.Evm64.SMod.Compose.ModCall
import EvmAsm.Evm64.SMod.Compose.SaveRa
import EvmAsm.Evm64.SMod.Compose.SignBlockSpecs
import EvmAsm.Evm64.SMod.Compose.AbsBlockSpecs
import EvmAsm.Evm64.SMod.Compose.PreserveDividendSign

namespace EvmAsm.Evm64.SMod.Compose

/-- v5 mirror of `savedRaRet_spec_in_smodCodeV4`. -/
theorem savedRaRet_spec_in_smodCodeV5
    (vSavedRa : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 (base + savedRaRetOff)
        ((vSavedRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~1)
      (smodCodeV5 base)
      (.x18 ↦ᵣ vSavedRa)
      (.x18 ↦ᵣ vSavedRa) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_smod_saved_ra_ret_block_code .x18
          (base + savedRaRetOff)) a = some i →
        (smodCodeV5 base) a = some i := by
    intro a i h
    exact smodCodeV5_savedRaRet_sub (base := base) a i
      (by simpa [savedRaRetCode,
        EvmAsm.Evm64.evm_smod_saved_ra_ret_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_smod_saved_ra_ret_block_spec_within .x18
      vSavedRa (base + savedRaRetOff))

/-- v5 mirror of `modCall_spec_in_smodCodeV4`. -/
theorem modCall_spec_in_smodCodeV5
    (vOld : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 (base + modCallOff)
        ((base + modCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_smodCallOff)
      (smodCodeV5 base)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ ((base + modCallOff) + 4)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_div_call_block_code
          EvmAsm.Evm64.evm_smodCallOff (base + modCallOff)) a = some i →
        (smodCodeV5 base) a = some i := by
    intro a i h
    exact smodCodeV5_modCall_sub (base := base) a i
      (by simpa [modCallCode,
        EvmAsm.Evm64.evm_sdiv_div_call_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_div_call_block_spec_within
      EvmAsm.Evm64.evm_smodCallOff vOld (base + modCallOff))

/-- v5 mirror of `saveRa_spec_in_smodCodeV4`. -/
theorem saveRa_spec_in_smodCodeV5
    (vRa vSavedOld : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 (base + saveRaOff) ((base + saveRaOff) + 4)
      (smodCodeV5 base)
      ((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld))
      ((.x1 ↦ᵣ vRa) **
        (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_smod_save_ra_block_code .x18
          (base + saveRaOff)) a = some i →
        (smodCodeV5 base) a = some i := by
    intro a i h
    exact smodCodeV5_saveRa_sub (base := base) a i
      (by simpa [saveRaCode,
        EvmAsm.Evm64.evm_smod_save_ra_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_smod_save_ra_block_spec_within .x18
      vRa vSavedOld (base + saveRaOff) (by decide))

/-- v5 mirror of `dividendSign_spec_in_smodCodeV4`. -/
theorem dividendSign_spec_in_smodCodeV5
    (sp sOld dividendTop : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 2 (base + dividendSignOff) ((base + dividendSignOff) + 8)
      (smodCodeV5 base)
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
         dividendTop))
      ((.x12 ↦ᵣ sp) **
       (.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
         dividendTop)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_sign_bit_block_code .x12 .x8
          EvmAsm.Evm64.evm_smodDividendTopLimbOff
          (base + dividendSignOff)) a = some i →
        (smodCodeV5 base) a = some i := by
    intro a i h
    exact smodCodeV5_dividendSign_sub (base := base) a i
      (by simpa [dividendSignCode,
        EvmAsm.Evm64.evm_sdiv_sign_bit_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block_spec_within .x12 .x8
      EvmAsm.Evm64.evm_smodDividendTopLimbOff sp sOld dividendTop
      (base + dividendSignOff) (by decide))

/-- v5 mirror of `divisorSign_spec_in_smodCodeV4`. -/
theorem divisorSign_spec_in_smodCodeV5
    (sp sOld divisorTop : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 2 (base + divisorSignOff) ((base + divisorSignOff) + 8)
      (smodCodeV5 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sOld) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
         divisorTop))
      ((.x12 ↦ᵣ sp) **
       (.x9 ↦ᵣ (divisorTop >>> (63 : BitVec 6).toNat)) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
         divisorTop)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_sign_bit_block_code .x12 .x9
          EvmAsm.Evm64.evm_smodDivisorTopLimbOff
          (base + divisorSignOff)) a = some i →
        (smodCodeV5 base) a = some i := by
    intro a i h
    exact smodCodeV5_divisorSign_sub (base := base) a i
      (by simpa [divisorSignCode,
        EvmAsm.Evm64.evm_sdiv_sign_bit_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block_spec_within .x12 .x9
      EvmAsm.Evm64.evm_smodDivisorTopLimbOff sp sOld divisorTop
      (base + divisorSignOff) (by decide))

/-- v5 mirror of `preserveDividendSign_spec_in_smodCodeV4`. -/
theorem preserveDividendSign_spec_in_smodCodeV5
    (dividendSign x13Old : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 (base + preserveDividendSignOff)
      ((base + preserveDividendSignOff) + 4)
      (smodCodeV5 base)
      ((.x8 ↦ᵣ dividendSign) ** (.x13 ↦ᵣ x13Old))
      ((.x8 ↦ᵣ dividendSign) **
        (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Rv64.CodeReq.singleton (base + preserveDividendSignOff)
          (.ADDI .x13 .x8 0)) a = some i →
        (smodCodeV5 base) a = some i := by
    intro a i h
    exact smodCodeV5_preserveDividendSign_sub (base := base) a i
      (by
        rw [preserveDividendSignCode, EvmAsm.Rv64.ADDI,
          EvmAsm.Rv64.single, EvmAsm.Rv64.CodeReq.ofProg_singleton]
        exact h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Rv64.addi_spec_within .x13 .x8 dividendSign x13Old
      0 (base + preserveDividendSignOff) (by decide))

/-- v5 mirror of `dividendAbs_spec_in_smodCodeV4`. -/
theorem dividendAbs_spec_in_smodCodeV5
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + dividendAbsOff) ((base + dividendAbsOff) + 84)
      (smodCodeV5 base)
      (EvmAsm.Evm64.condNegate256BlockPre .x12 .x8 .x10 .x7 .x11
        0 8 16 24 sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3)
      (EvmAsm.Evm64.condNegate256BlockPost .x12 .x8 .x10 .x7 .x11
        0 8 16 24 sp sign limb0 limb1 limb2 limb3) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x8 .x10 .x7 .x11 0 8 16 24
          (base + dividendAbsOff)) a = some i →
        (smodCodeV5 base) a = some i := by
    intro a i h
    exact smodCodeV5_dividendAbs_sub (base := base) a i
      (by simpa [dividendAbsCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x8 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + dividendAbsOff) (by decide) (by decide) (by decide))

/-- v5 mirror of `divisorAbs_spec_in_smodCodeV4`. -/
theorem divisorAbs_spec_in_smodCodeV5
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + divisorAbsOff) ((base + divisorAbsOff) + 84)
      (smodCodeV5 base)
      (EvmAsm.Evm64.condNegate256BlockPre .x12 .x9 .x10 .x7 .x11
        32 40 48 56 sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3)
      (EvmAsm.Evm64.condNegate256BlockPost .x12 .x9 .x10 .x7 .x11
        32 40 48 56 sp sign limb0 limb1 limb2 limb3) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x9 .x10 .x7 .x11 32 40 48 56
          (base + divisorAbsOff)) a = some i →
        (smodCodeV5 base) a = some i := by
    intro a i h
    exact smodCodeV5_divisorAbs_sub (base := base) a i
      (by simpa [divisorAbsCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x9 .x10 .x7 .x11 32 40 48 56
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + divisorAbsOff) (by decide) (by decide) (by decide))

end EvmAsm.Evm64.SMod.Compose
