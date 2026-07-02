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

end EvmAsm.Evm64.SDiv.Compose
