/-
  EvmAsm.Evm64.SDiv.Compose.BaseCodeV5

  v5 SDIV return-block code subsumptions + leaf return spec, over `sdivCodeV5`.
  The SDIV sign-fix / saved-RA return blocks live in the shared `evm_sdiv_wrapper`
  prefix (identical between `evm_sdiv_v4` and `evm_sdiv_v5`), so these mirror the
  `sdivCodeV4_*_sub` / `*_spec_in_sdivCodeV4` family verbatim, swapping
  `evm_sdiv_v4` → `evm_sdiv_v5` (and the length lemma).  Foothold for the SDIV
  `.proven` flip over `evm_div_callable_v5`.
-/

import EvmAsm.Evm64.SDiv.Compose.BaseFinalBlockSpecs
import EvmAsm.Evm64.SDiv.Compose.CodeHandlesV5
import EvmAsm.Evm64.SDiv.Compose.SaveRaSignBlockSpecs
import EvmAsm.Evm64.SDiv.Compose.BaseDividendAbsBlockSpec
import EvmAsm.Evm64.SDiv.Compose.BaseDivisorAbsBlockSpec

namespace EvmAsm.Evm64.SDiv.Compose

/-- v5 mirror of `sdivCodeV4_savedRaRet_sub`: the saved-RA return block is a slice
    of the shared `evm_sdiv_wrapper` prefix, so it subsumes into `sdivCodeV5`. -/
theorem sdivCodeV5_savedRaRet_sub {base : Word} :
    ∀ a i, (savedRaRetCode base) a = some i → (sdivCodeV5 base) a = some i := by
  unfold savedRaRetCode sdivCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + savedRaRetOff)
    EvmAsm.Evm64.evm_sdiv_v5 (EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block .x18) 70
    (by simp [savedRaRetOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v5 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block_length, EvmAsm.Evm64.evm_sdiv_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v5_length]; norm_num)

/-- v5 mirror of `savedRaRet_spec_in_sdivCodeV4`. -/
theorem savedRaRet_spec_in_sdivCodeV5
    (vSavedRa : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 (base + savedRaRetOff)
        ((vSavedRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~1)
      (sdivCodeV5 base)
      (.x18 ↦ᵣ vSavedRa)
      (.x18 ↦ᵣ vSavedRa) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block_code .x18
          (base + savedRaRetOff)) a = some i →
        (sdivCodeV5 base) a = some i := by
    intro a i h
    exact sdivCodeV5_savedRaRet_sub (base := base) a i
      (by simpa [savedRaRetCode,
        EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block_spec_within .x18
      vSavedRa (base + savedRaRetOff))

/-- v5 mirror of `sdivCodeV4_saveRa_sub`. -/
theorem sdivCodeV5_saveRa_sub {base : Word} :
    ∀ a i, (saveRaCode base) a = some i → (sdivCodeV5 base) a = some i := by
  unfold saveRaCode sdivCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + saveRaOff)
    EvmAsm.Evm64.evm_sdiv_v5 (EvmAsm.Evm64.evm_sdiv_save_ra_block .x18) 0
    (by simp [saveRaOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_save_ra_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v5 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_save_ra_block_length, EvmAsm.Evm64.evm_sdiv_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v5_length]; norm_num)

/-- v5 mirror of `sdivCodeV4_dividendSign_sub`. -/
theorem sdivCodeV5_dividendSign_sub {base : Word} :
    ∀ a i, (dividendSignCode base) a = some i → (sdivCodeV5 base) a = some i := by
  unfold dividendSignCode sdivCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendSignOff)
    EvmAsm.Evm64.evm_sdiv_v5
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x8
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff) 1
    (by simp [dividendSignOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_sign_bit_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v5 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_sign_bit_block_length, EvmAsm.Evm64.evm_sdiv_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v5_length]; norm_num)

/-- v5 mirror of `sdivCodeV4_divisorSign_sub`. -/
theorem sdivCodeV5_divisorSign_sub {base : Word} :
    ∀ a i, (divisorSignCode base) a = some i → (sdivCodeV5 base) a = some i := by
  unfold divisorSignCode sdivCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorSignOff)
    EvmAsm.Evm64.evm_sdiv_v5
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x9
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) 3
    (by simp [divisorSignOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_sign_bit_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v5 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_sign_bit_block_length, EvmAsm.Evm64.evm_sdiv_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v5_length]; norm_num)

/-- v5 mirror of `sdivCodeV4_dividendAbs_sub`. -/
theorem sdivCodeV5_dividendAbs_sub {base : Word} :
    ∀ a i, (dividendAbsCode base) a = some i → (sdivCodeV5 base) a = some i := by
  unfold dividendAbsCode sdivCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendAbsOff)
    EvmAsm.Evm64.evm_sdiv_v5
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 5
    (by simp [dividendAbsOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v5 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length, EvmAsm.Evm64.evm_sdiv_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v5_length]; norm_num)

/-- v5 mirror of `sdivCodeV4_divisorAbs_sub`. -/
theorem sdivCodeV5_divisorAbs_sub {base : Word} :
    ∀ a i, (divisorAbsCode base) a = some i → (sdivCodeV5 base) a = some i := by
  unfold divisorAbsCode sdivCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorAbsOff)
    EvmAsm.Evm64.evm_sdiv_v5
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11
      32 40 48 56) 26
    (by simp [divisorAbsOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v5 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length, EvmAsm.Evm64.evm_sdiv_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v5_length]; norm_num)

/-- v5 mirror of `sdivCodeV4_signXor_sub`. -/
theorem sdivCodeV5_signXor_sub {base : Word} :
    ∀ a i, (signXorCode base) a = some i → (sdivCodeV5 base) a = some i := by
  unfold signXorCode sdivCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + signXorOff)
    EvmAsm.Evm64.evm_sdiv_v5 (EvmAsm.Rv64.XOR' .x8 .x8 .x9) 47
    (by simp [signXorOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      unfold EvmAsm.Evm64.evm_sdiv_v5 EvmAsm.Evm64.evm_sdiv_wrapper
        EvmAsm.Rv64.XOR' EvmAsm.Rv64.single
      simp only [EvmAsm.Rv64.seq, List.length_cons, List.length_nil]; rfl)
    (by
      unfold EvmAsm.Rv64.XOR' EvmAsm.Rv64.single
      rw [EvmAsm.Evm64.evm_sdiv_v5_length]; simp)
    (by rw [EvmAsm.Evm64.evm_sdiv_v5_length]; norm_num)

/-- v5 mirror of `sdivCodeV4_divCall_sub`. -/
theorem sdivCodeV5_divCall_sub {base : Word} :
    ∀ a i, (divCallCode base) a = some i → (sdivCodeV5 base) a = some i := by
  unfold divCallCode sdivCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divCallOff)
    EvmAsm.Evm64.evm_sdiv_v5
    (EvmAsm.Evm64.evm_sdiv_div_call_block EvmAsm.Evm64.evm_sdivCallOff) 48
    (by simp [divCallOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_div_call_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v5 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_div_call_block_length, EvmAsm.Evm64.evm_sdiv_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v5_length]; norm_num)

/-- v5 mirror of `sdivCodeV4_resultSignFix_sub`. -/
theorem sdivCodeV5_resultSignFix_sub {base : Word} :
    ∀ a i, (resultSignFixCode base) a = some i → (sdivCodeV5 base) a = some i := by
  unfold resultSignFixCode sdivCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + resultSignFixOff)
    EvmAsm.Evm64.evm_sdiv_v5
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 49
    (by simp [resultSignFixOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v5 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length, EvmAsm.Evm64.evm_sdiv_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v5_length]; norm_num)

/-- v5 mirror of `divCall_spec_in_sdivCodeV4`: the SDIV `divCall` near-call block
    (identical in the shared `evm_sdiv_wrapper` prefix) over `sdivCodeV5`. -/
theorem divCall_spec_in_sdivCodeV5
    (vOld : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 (base + divCallOff)
        ((base + divCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCodeV5 base)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ ((base + divCallOff) + 4)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_div_call_block_code
          EvmAsm.Evm64.evm_sdivCallOff (base + divCallOff)) a = some i →
        (sdivCodeV5 base) a = some i := by
    intro a i h
    exact sdivCodeV5_divCall_sub (base := base) a i
      (by simpa [divCallCode,
        EvmAsm.Evm64.evm_sdiv_div_call_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_div_call_block_spec_within
      EvmAsm.Evm64.evm_sdivCallOff vOld (base + divCallOff))

/-- v5 mirror of `signXor_spec_in_sdivCodeV4`: the `XOR .x8 .x8 .x9` sign-combine
    block (shared wrapper prefix) over `sdivCodeV5`. -/
theorem signXor_spec_in_sdivCodeV5
    (signDividend signDivisor : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 (base + signXorOff) ((base + signXorOff) + 4)
      (sdivCodeV5 base)
      ((.x8 ↦ᵣ signDividend) ** (.x9 ↦ᵣ signDivisor))
      ((.x8 ↦ᵣ (signDividend ^^^ signDivisor)) ** (.x9 ↦ᵣ signDivisor)) := by
  have hmono :
      ∀ a i, (EvmAsm.Rv64.CodeReq.singleton (base + signXorOff) (.XOR .x8 .x8 .x9)) a = some i →
        (sdivCodeV5 base) a = some i := by
    intro a i h
    exact sdivCodeV5_signXor_sub (base := base) a i
      (by
        rw [signXorCode, EvmAsm.Rv64.XOR', EvmAsm.Rv64.single,
          EvmAsm.Rv64.CodeReq.ofProg_singleton]
        exact h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Rv64.xor_spec_gen_rd_eq_rs1_within .x8 .x9 signDividend signDivisor
      (base + signXorOff) (by decide))

/-- v5 mirror of `saveRa_spec_in_sdivCodeV4`. -/
theorem saveRa_spec_in_sdivCodeV5
    (vRa vSavedOld : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 base (base + 4) (sdivCodeV5 base)
      ((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld))
      ((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) := by
  have hmono :
      ∀ a i, (EvmAsm.Evm64.evm_sdiv_save_ra_block_code .x18 base) a = some i →
        (sdivCodeV5 base) a = some i := by
    intro a i h
    exact sdivCodeV5_saveRa_sub (base := base) a i
      (by simpa [saveRaCode, saveRaOff,
        EvmAsm.Evm64.evm_sdiv_save_ra_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_save_ra_block_spec_within .x18
      vRa vSavedOld base (by decide))

/-- v5 mirror of `dividendSign_spec_in_sdivCodeV4`. -/
theorem dividendSign_spec_in_sdivCodeV5
    (sp sOld dividendTop : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 2 (base + dividendSignOff) ((base + dividendSignOff) + 8)
      (sdivCodeV5 base)
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop))
      ((.x12 ↦ᵣ sp) **
       (.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_sign_bit_block_code .x12 .x8
          EvmAsm.Evm64.evm_sdivDividendTopLimbOff
          (base + dividendSignOff)) a = some i →
        (sdivCodeV5 base) a = some i := by
    intro a i h
    exact sdivCodeV5_dividendSign_sub (base := base) a i
      (by simpa [dividendSignCode,
        EvmAsm.Evm64.evm_sdiv_sign_bit_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block_spec_within .x12 .x8
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff sp sOld dividendTop
      (base + dividendSignOff) (by decide))

/-- v5 mirror of `divisorSign_spec_in_sdivCodeV4`. -/
theorem divisorSign_spec_in_sdivCodeV5
    (sp sOld divisorTop : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 2 (base + divisorSignOff) ((base + divisorSignOff) + 8)
      (sdivCodeV5 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sOld) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
         divisorTop))
      ((.x12 ↦ᵣ sp) **
       (.x9 ↦ᵣ (divisorTop >>> (63 : BitVec 6).toNat)) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
         divisorTop)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_sign_bit_block_code .x12 .x9
          EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
          (base + divisorSignOff)) a = some i →
        (sdivCodeV5 base) a = some i := by
    intro a i h
    exact sdivCodeV5_divisorSign_sub (base := base) a i
      (by simpa [divisorSignCode,
        EvmAsm.Evm64.evm_sdiv_sign_bit_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block_spec_within .x12 .x9
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff sp sOld divisorTop
      (base + divisorSignOff) (by decide))

/-- v5 mirror of `dividendAbs_spec_in_sdivCodeV4`. -/
theorem dividendAbs_spec_in_sdivCodeV5
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + dividendAbsOff) ((base + dividendAbsOff) + 84)
      (sdivCodeV5 base)
      (dividendAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (dividendAbsPost sp sign limb0 limb1 limb2 limb3) := by
  rw [dividendAbsPre_unfold, dividendAbsPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x8 .x10 .x7 .x11 0 8 16 24
          (base + dividendAbsOff)) a = some i →
        (sdivCodeV5 base) a = some i := by
    intro a i h
    exact sdivCodeV5_dividendAbs_sub (base := base) a i
      (by simpa [dividendAbsCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x8 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + dividendAbsOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono hSpec

/-- v5 mirror of `divisorAbs_spec_in_sdivCodeV4`. -/
theorem divisorAbs_spec_in_sdivCodeV5
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + divisorAbsOff) ((base + divisorAbsOff) + 84)
      (sdivCodeV5 base)
      (divisorAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (divisorAbsPost sp sign limb0 limb1 limb2 limb3) := by
  rw [divisorAbsPre_unfold, divisorAbsPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x9 .x10 .x7 .x11 32 40 48 56
          (base + divisorAbsOff)) a = some i →
        (sdivCodeV5 base) a = some i := by
    intro a i h
    exact sdivCodeV5_divisorAbs_sub (base := base) a i
      (by simpa [divisorAbsCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x9 .x10 .x7 .x11 32 40 48 56
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + divisorAbsOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono hSpec

end EvmAsm.Evm64.SDiv.Compose
