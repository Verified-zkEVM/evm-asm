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

end EvmAsm.Evm64.SDiv.Compose
