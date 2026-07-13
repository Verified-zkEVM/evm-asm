/-
  EvmAsm.Evm64.SDiv.Compose.Base

  Shared composition infrastructure for SDIV: `sdivCode` (the union of
  all sub-block `CodeReq`s), subsumption helpers tying sub-block codes
  back to `sdivCode`, and shared length lemmas.

  Skeleton placeholder for GH #90 (beads slice evm-asm-kyp6). Concrete
  definitions will be added once `evm_sdiv` is laid out (slice
  evm-asm-01uh) and the per-block specs from `LimbSpec.lean` start
  composing.
-/

import EvmAsm.Rv64.BitAux
import EvmAsm.Evm64.SDiv.LimbSpec
import EvmAsm.Evm64.SDiv.AddrNorm
import EvmAsm.Evm64.DivMod.CallableV1Legacy
import EvmAsm.Evm64.DivMod.CallableV4Div
import EvmAsm.Evm64.SDiv.Compose.SDivViewChainC
import EvmAsm.Evm64.SDiv.Compose.BaseOffsets
import EvmAsm.Evm64.SDiv.Compose.BaseSignSequence
import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFix
import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFixBlockSpec
import EvmAsm.Evm64.SDiv.Compose.BaseFinalBlockSpecs

namespace EvmAsm.Evm64.SDiv.Compose

/-- Wrapper sub-region inside `sdivCodeV4`. -/
theorem sdivCodeV4_wrapper_sub {base : Word} :
    ∀ a i, (EvmAsm.Rv64.CodeReq.ofProg base evm_sdiv_wrapper) a = some i →
      (sdivCodeV4 base) a = some i := by
  unfold sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base base evm_sdiv_v4 evm_sdiv_wrapper 0
    (EvmAsm.Evm64.SDiv.AddrNorm.wrapperStart_addr base)
    (by unfold evm_sdiv_v4; simp only [EvmAsm.Rv64.seq, EvmAsm.Rv64.Program]; rfl)
    (by
      rw [evm_sdiv_v4_length, evm_sdiv_wrapper_length]
      norm_num)
    (by
      rw [evm_sdiv_v4_length]
      norm_num)

/-- The appended v4 unsigned DIV callable sub-region inside `sdivCodeV4`. -/
theorem sdivCodeV4_div_callable_sub {base : Word} :
    ∀ a i, (evm_div_callable_code_v4 (base + 284)) a = some i →
      (sdivCodeV4 base) a = some i := by
  intro a i h
  rw [evm_div_callable_code_v4_eq_ofProg (base + 284)] at h
  unfold sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + 284)
    evm_sdiv_v4 evm_div_callable_v4 71
    (EvmAsm.Evm64.SDiv.AddrNorm.divCallableStart_addr base)
    (by
      unfold evm_sdiv_v4 EvmAsm.Rv64.seq
      rw [← evm_sdiv_wrapper_length]
      have h_drop :
          List.drop evm_sdiv_wrapper.length
              (evm_sdiv_wrapper ++ evm_div_callable_v4) =
            evm_div_callable_v4 := by
        exact List.drop_append_length
      rw [h_drop]
      simp only [List.take_length])
    (by rw [evm_div_callable_v4_length, evm_sdiv_v4_length])
    (by
      rw [evm_sdiv_v4_length]
      norm_num)
    a i h

/-- Bundled top-level SDIV v4 code subsumptions for the wrapper and appended
    v4 unsigned DIV callable. -/
theorem sdivCodeV4_top_level_subs {base : Word} :
    (∀ a i, (EvmAsm.Rv64.CodeReq.ofProg base evm_sdiv_wrapper) a = some i →
      (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (evm_div_callable_code_v4 (base + 284)) a = some i →
      (sdivCodeV4 base) a = some i) := by
  exact ⟨sdivCodeV4_wrapper_sub, sdivCodeV4_div_callable_sub⟩

/-- The near `JAL` at the SDIV wrapper's `divCall` block targets the appended
    unsigned DIV callable, which starts at `base + wrapperEndOff`.  This is
    the entry-PC alignment fact needed to sequence the wrapper prefix with the
    callable DIV stack dispatcher. -/
theorem divCall_target_eq_wrapperEndOff (base : Word) :
    (base + divCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_sdivCallOff =
      base + wrapperEndOff := by
  show (base + (192 : Word)) + (92 : Word) = base + (284 : Word)
  bv_omega

/-- Under the standard RV PC-alignment invariant (`base` has its low bit
    clear), the JALR low-bit mask `&&& ~~~1` on the post-`divCall` return
    address `base + resultSignFixOff` is the identity. Bite-sized helper
    for slice 4 (evm-asm-tdlsu): used to align the exit PC of
    `evm_div_callable_spec_in_sdivCode` (which returns to `saved_ra &&& ~~~1`
    via JALR) with the SDIV wrapper's `resultSignFix` entry. -/
theorem base_add_resultSignFixOff_andn_one
    (base : Word) (hbase : base &&& 1 = 0) :
    (base + resultSignFixOff) &&& ~~~(1 : Word) = base + resultSignFixOff := by
  show (base + (196 : Word)) &&& ~~~(1 : Word) = base + (196 : Word)
  exact EvmAsm.Rv64.BitAux.word_add_even_andn_one hbase (by decide)

/-- The return address written by the SDIV wrapper's near `divCall` is exactly
    the result-sign-fixup entry, and masking bit 0 for the eventual `JALR`
    keeps it there.  This is the concrete `raVal &&& ~~~1` alignment fact
    needed when composing the wrapper prefix with `evm_div_callable`. -/
theorem divCall_return_andn_one_eq_resultSignFixOff
    (base : Word) (hbase : base &&& 1 = 0) :
    (((base + divCallOff) + 4 : Word) &&& ~~~(1 : Word)) =
      base + resultSignFixOff := by
  show (((base + (192 : Word)) + (4 : Word)) &&& ~~~(1 : Word)) =
      base + (196 : Word)
  have hsum : (base + 192 + 4 : Word) = base + 196 := by bv_omega
  rw [hsum]
  exact EvmAsm.Rv64.BitAux.word_add_even_andn_one hbase (by decide)

end EvmAsm.Evm64.SDiv.Compose
