/-
  EvmAsm.Evm64.SMod.Compose.BaseCodeV5

  v5 SMOD block code subsumptions over `smodCodeV5`.  The SMOD wrapper prefix is
  identical between `evm_smod` (v4) and `evm_smod_v5` (only the appended divider
  differs), so these mirror the `smodCodeV4_*_sub` family verbatim, swapping
  `evm_smod` → `evm_smod_v5` (and the length lemma).  Foothold for the SMOD
  `.proven` flip over `evm_mod_callable_v5`.
-/

import EvmAsm.Evm64.SMod.Compose.BaseCode
import EvmAsm.Evm64.SMod.Compose.CodeHandlesV5

namespace EvmAsm.Evm64.SMod.Compose

theorem smodCodeV5_saveRa_sub {base : Word} :
    ∀ a i, (saveRaCode base) a = some i → (smodCodeV5 base) a = some i := by
  unfold saveRaCode smodCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + saveRaOff)
    EvmAsm.Evm64.evm_smod_v5 (EvmAsm.Evm64.evm_smod_save_ra_block .x18) 0
    (by simp [saveRaOff])
    (by
      apply EvmAsm.Evm64.SMod.Compose.smod_slice_of_drop
      rw [EvmAsm.Evm64.evm_smod_save_ra_block_length]
      unfold EvmAsm.Evm64.evm_smod_v5 EvmAsm.Evm64.evm_smod_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_smod_save_ra_block_length, EvmAsm.Evm64.evm_smod_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_smod_v5_length]; norm_num)

theorem smodCodeV5_dividendSign_sub {base : Word} :
    ∀ a i, (dividendSignCode base) a = some i → (smodCodeV5 base) a = some i := by
  unfold dividendSignCode smodCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendSignOff)
    EvmAsm.Evm64.evm_smod_v5
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x8
      EvmAsm.Evm64.evm_smodDividendTopLimbOff) 1
    (by simp [dividendSignOff])
    (by
      apply EvmAsm.Evm64.SMod.Compose.smod_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_sign_bit_block_length]
      unfold EvmAsm.Evm64.evm_smod_v5 EvmAsm.Evm64.evm_smod_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_sign_bit_block_length, EvmAsm.Evm64.evm_smod_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_smod_v5_length]; norm_num)

theorem smodCodeV5_preserveDividendSign_sub {base : Word} :
    ∀ a i, (preserveDividendSignCode base) a = some i → (smodCodeV5 base) a = some i := by
  unfold preserveDividendSignCode smodCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + preserveDividendSignOff)
    EvmAsm.Evm64.evm_smod_v5 (EvmAsm.Rv64.ADDI .x13 .x8 0) 3
    (by simp [preserveDividendSignOff])
    (by
      apply EvmAsm.Evm64.SMod.Compose.smod_slice_of_drop
      unfold EvmAsm.Evm64.evm_smod_v5 EvmAsm.Evm64.evm_smod_wrapper
        EvmAsm.Rv64.ADDI EvmAsm.Rv64.single
      simp only [EvmAsm.Rv64.seq, List.length_cons, List.length_nil]; rfl)
    (by
      unfold EvmAsm.Rv64.ADDI EvmAsm.Rv64.single
      rw [EvmAsm.Evm64.evm_smod_v5_length]; simp)
    (by rw [EvmAsm.Evm64.evm_smod_v5_length]; norm_num)

theorem smodCodeV5_divisorSign_sub {base : Word} :
    ∀ a i, (divisorSignCode base) a = some i → (smodCodeV5 base) a = some i := by
  unfold divisorSignCode smodCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorSignOff)
    EvmAsm.Evm64.evm_smod_v5
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x9
      EvmAsm.Evm64.evm_smodDivisorTopLimbOff) 4
    (by simp [divisorSignOff])
    (by
      apply EvmAsm.Evm64.SMod.Compose.smod_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_sign_bit_block_length]
      unfold EvmAsm.Evm64.evm_smod_v5 EvmAsm.Evm64.evm_smod_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_sign_bit_block_length, EvmAsm.Evm64.evm_smod_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_smod_v5_length]; norm_num)

theorem smodCodeV5_dividendAbs_sub {base : Word} :
    ∀ a i, (dividendAbsCode base) a = some i → (smodCodeV5 base) a = some i := by
  unfold dividendAbsCode smodCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendAbsOff)
    EvmAsm.Evm64.evm_smod_v5
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 6
    (by simp [dividendAbsOff])
    (by
      apply EvmAsm.Evm64.SMod.Compose.smod_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length]
      unfold EvmAsm.Evm64.evm_smod_v5 EvmAsm.Evm64.evm_smod_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length,
        EvmAsm.Evm64.evm_smod_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_smod_v5_length]; norm_num)

theorem smodCodeV5_divisorAbs_sub {base : Word} :
    ∀ a i, (divisorAbsCode base) a = some i → (smodCodeV5 base) a = some i := by
  unfold divisorAbsCode smodCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorAbsOff)
    EvmAsm.Evm64.evm_smod_v5
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11
      32 40 48 56) 27
    (by simp [divisorAbsOff])
    (by
      apply EvmAsm.Evm64.SMod.Compose.smod_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length]
      unfold EvmAsm.Evm64.evm_smod_v5 EvmAsm.Evm64.evm_smod_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length,
        EvmAsm.Evm64.evm_smod_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_smod_v5_length]; norm_num)

theorem smodCodeV5_modCall_sub {base : Word} :
    ∀ a i, (modCallCode base) a = some i → (smodCodeV5 base) a = some i := by
  unfold modCallCode smodCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + modCallOff)
    EvmAsm.Evm64.evm_smod_v5
    (EvmAsm.Evm64.evm_sdiv_div_call_block EvmAsm.Evm64.evm_smodCallOff) 48
    (by simp [modCallOff])
    (by
      apply EvmAsm.Evm64.SMod.Compose.smod_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_div_call_block_length]
      unfold EvmAsm.Evm64.evm_smod_v5 EvmAsm.Evm64.evm_smod_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_div_call_block_length, EvmAsm.Evm64.evm_smod_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_smod_v5_length]; norm_num)

theorem smodCodeV5_resultSignFix_sub {base : Word} :
    ∀ a i, (resultSignFixCode base) a = some i → (smodCodeV5 base) a = some i := by
  unfold resultSignFixCode smodCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + resultSignFixOff)
    EvmAsm.Evm64.evm_smod_v5
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x13 .x10 .x7 .x11
      0 8 16 24) 49
    (by simp [resultSignFixOff])
    (by
      apply EvmAsm.Evm64.SMod.Compose.smod_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length]
      unfold EvmAsm.Evm64.evm_smod_v5 EvmAsm.Evm64.evm_smod_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length,
        EvmAsm.Evm64.evm_smod_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_smod_v5_length]; norm_num)

theorem smodCodeV5_savedRaRet_sub {base : Word} :
    ∀ a i, (savedRaRetCode base) a = some i → (smodCodeV5 base) a = some i := by
  unfold savedRaRetCode smodCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + savedRaRetOff)
    EvmAsm.Evm64.evm_smod_v5 (EvmAsm.Evm64.evm_smod_saved_ra_ret_block .x18) 70
    (by simp [savedRaRetOff])
    (by
      apply EvmAsm.Evm64.SMod.Compose.smod_slice_of_drop
      rw [EvmAsm.Evm64.evm_smod_saved_ra_ret_block_length]
      unfold EvmAsm.Evm64.evm_smod_v5 EvmAsm.Evm64.evm_smod_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_smod_saved_ra_ret_block_length,
        EvmAsm.Evm64.evm_smod_v5_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_smod_v5_length]; norm_num)

theorem smodCodeV5_block_subs {base : Word} :
    (∀ a i, (saveRaCode base) a = some i → (smodCodeV5 base) a = some i) ∧
    (∀ a i, (dividendSignCode base) a = some i → (smodCodeV5 base) a = some i) ∧
    (∀ a i, (preserveDividendSignCode base) a = some i → (smodCodeV5 base) a = some i) ∧
    (∀ a i, (divisorSignCode base) a = some i → (smodCodeV5 base) a = some i) ∧
    (∀ a i, (dividendAbsCode base) a = some i → (smodCodeV5 base) a = some i) ∧
    (∀ a i, (divisorAbsCode base) a = some i → (smodCodeV5 base) a = some i) ∧
    (∀ a i, (modCallCode base) a = some i → (smodCodeV5 base) a = some i) ∧
    (∀ a i, (resultSignFixCode base) a = some i → (smodCodeV5 base) a = some i) ∧
    (∀ a i, (savedRaRetCode base) a = some i → (smodCodeV5 base) a = some i) ∧
    (∀ a i, (modCallableCodeV5 base) a = some i → (smodCodeV5 base) a = some i) := by
  exact ⟨smodCodeV5_saveRa_sub, smodCodeV5_dividendSign_sub,
    smodCodeV5_preserveDividendSign_sub, smodCodeV5_divisorSign_sub,
    smodCodeV5_dividendAbs_sub, smodCodeV5_divisorAbs_sub, smodCodeV5_modCall_sub,
    smodCodeV5_resultSignFix_sub, smodCodeV5_savedRaRet_sub,
    smodCodeV5_modCallable_sub⟩

end EvmAsm.Evm64.SMod.Compose
