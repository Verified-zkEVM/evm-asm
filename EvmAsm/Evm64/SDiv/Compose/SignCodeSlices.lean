/-
  EvmAsm.Evm64.SDiv.Compose.SignCodeSlices

  CodeReq slice inclusions for the saved-`ra` and sign-bit probe blocks.
  These small structural lemmas are kept separate from the larger SDIV
  wrapper slice table so primitive sign-block specs do not import it.
-/

import EvmAsm.Evm64.SDiv.Compose.CodeHandles

namespace EvmAsm.Evm64.SDiv.Compose

theorem sdiv_slice_of_drop (full b : List EvmAsm.Rv64.Instr) (idx : Nat)
    (hdrop : full.drop idx = b ++ full.drop (idx + b.length)) :
    (full.drop idx).take b.length = b := by
  rw [hdrop, List.take_append_length]

theorem sdivCodeV4_saveRa_sub {base : Word} :
    ∀ a i, (saveRaCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold saveRaCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + saveRaOff)
    EvmAsm.Evm64.evm_sdiv_v4 (EvmAsm.Evm64.evm_sdiv_save_ra_block .x18) 0
    (by simp [saveRaOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_save_ra_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_save_ra_block_length, EvmAsm.Evm64.evm_sdiv_v4_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_dividendSign_sub {base : Word} :
    ∀ a i, (dividendSignCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold dividendSignCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendSignOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x8
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff) 1
    (by simp [dividendSignOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_sign_bit_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_sign_bit_block_length, EvmAsm.Evm64.evm_sdiv_v4_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_divisorSign_sub {base : Word} :
    ∀ a i, (divisorSignCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold divisorSignCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorSignOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x9
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) 3
    (by simp [divisorSignOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_sign_bit_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_sign_bit_block_length, EvmAsm.Evm64.evm_sdiv_v4_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

end EvmAsm.Evm64.SDiv.Compose
