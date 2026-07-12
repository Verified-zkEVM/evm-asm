/-
  EvmAsm.Evm64.SDiv.Compose.BaseCode

  CodeReq handles and sub-block inclusion lemmas for the SDIV wrapper.
-/

import EvmAsm.Evm64.SDiv.Compose.CodeHandles
import EvmAsm.Evm64.SDiv.Compose.SignCodeSlices

namespace EvmAsm.Evm64.SDiv.Compose

/-- Structural slice helper: if dropping `idx` instructions off `full` exposes
    `b` as a prefix, then taking `b.length` recovers `b`. This is the
    kernel-checkable replacement for the `h_slice` argument of
    `CodeReq.ofProg_mono_sub`; the `hdrop` premise is discharged by shallow
    `rfl`/`drop_append_length` reduction rather than enumerating the whole
    390-instruction list. -/
theorem sdivCodeV4_dividendAbs_sub {base : Word} :
    ∀ a i, (dividendAbsCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold dividendAbsCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendAbsOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 5
    (by simp [dividendAbsOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length, EvmAsm.Evm64.evm_sdiv_v4_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_divisorAbs_sub {base : Word} :
    ∀ a i, (divisorAbsCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold divisorAbsCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorAbsOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11
      32 40 48 56) 26
    (by simp [divisorAbsOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length, EvmAsm.Evm64.evm_sdiv_v4_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_signXor_sub {base : Word} :
    ∀ a i, (signXorCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold signXorCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + signXorOff)
    EvmAsm.Evm64.evm_sdiv_v4 (EvmAsm.Rv64.XOR' .x8 .x8 .x9) 47
    (by simp [signXorOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
        EvmAsm.Rv64.XOR' EvmAsm.Rv64.single
      simp only [EvmAsm.Rv64.seq, List.length_cons, List.length_nil]; rfl)
    (by
      unfold EvmAsm.Rv64.XOR' EvmAsm.Rv64.single
      rw [EvmAsm.Evm64.evm_sdiv_v4_length]; simp)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_divCall_sub {base : Word} :
    ∀ a i, (divCallCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold divCallCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divCallOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_div_call_block EvmAsm.Evm64.evm_sdivCallOff) 48
    (by simp [divCallOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_div_call_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_div_call_block_length, EvmAsm.Evm64.evm_sdiv_v4_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_resultSignFix_sub {base : Word} :
    ∀ a i, (resultSignFixCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold resultSignFixCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + resultSignFixOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 49
    (by simp [resultSignFixOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length, EvmAsm.Evm64.evm_sdiv_v4_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_savedRaRet_sub {base : Word} :
    ∀ a i, (savedRaRetCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold savedRaRetCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + savedRaRetOff)
    EvmAsm.Evm64.evm_sdiv_v4 (EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block .x18) 70
    (by simp [savedRaRetOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block_length, EvmAsm.Evm64.evm_sdiv_v4_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_divCallable_sub {base : Word} :
    ∀ a i, (divCallableCodeV4 base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold divCallableCodeV4 sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + wrapperEndOff)
    EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_div_callable_v4 71
    (by simp [wrapperEndOff])
    (by
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Rv64.seq
      rw [← EvmAsm.Evm64.evm_sdiv_wrapper_length]
      have h_drop :
          List.drop EvmAsm.Evm64.evm_sdiv_wrapper.length
              (EvmAsm.Evm64.evm_sdiv_wrapper ++ EvmAsm.Evm64.evm_div_callable_v4) =
            EvmAsm.Evm64.evm_div_callable_v4 := List.drop_append_length
      rw [h_drop]
      simp only [List.take_length])
    (by
      rw [EvmAsm.Evm64.evm_div_callable_v4_length, EvmAsm.Evm64.evm_sdiv_v4_length])
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_block_subs {base : Word} :
    (∀ a i, (saveRaCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (dividendSignCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (divisorSignCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (dividendAbsCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (divisorAbsCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (signXorCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (divCallCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (resultSignFixCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (savedRaRetCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (divCallableCodeV4 base) a = some i → (sdivCodeV4 base) a = some i) := by
  exact ⟨sdivCodeV4_saveRa_sub, sdivCodeV4_dividendSign_sub,
    sdivCodeV4_divisorSign_sub, sdivCodeV4_dividendAbs_sub,
    sdivCodeV4_divisorAbs_sub, sdivCodeV4_signXor_sub, sdivCodeV4_divCall_sub,
    sdivCodeV4_resultSignFix_sub, sdivCodeV4_savedRaRet_sub,
    sdivCodeV4_divCallable_sub⟩

end EvmAsm.Evm64.SDiv.Compose
