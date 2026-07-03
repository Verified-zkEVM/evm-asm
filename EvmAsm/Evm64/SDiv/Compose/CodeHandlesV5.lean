/-
  EvmAsm.Evm64.SDiv.Compose.CodeHandlesV5

  v5 code-region inclusion lemmas for the SDIV wrapper: the appended v5 unsigned
  divider callable `evm_div_callable_v5` sits inside `sdivCodeV5` at the
  `wrapperEndOff` offset.  Mirrors the v4 `sdivCodeV4_divCallable_sub` /
  `evm_div_callable_code_v4_sub_sdivCodeV4`.  Foundational brick for the SDIV
  `.proven` flip over `evm_div_callable_v5`.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallCallable
import EvmAsm.Evm64.DivMod.Callable

namespace EvmAsm.Evm64.SDiv.Compose

/-- The appended v5 unsigned divider callable region is inside `sdivCodeV5`. -/
theorem sdivCodeV5_divCallable_sub {base : Word} :
    ∀ a i, (divCallableCodeV5 base) a = some i → (sdivCodeV5 base) a = some i := by
  unfold divCallableCodeV5 sdivCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + wrapperEndOff)
    EvmAsm.Evm64.evm_sdiv_v5 EvmAsm.Evm64.evm_div_callable_v5 71
    (by simp [wrapperEndOff])
    (by
      unfold EvmAsm.Evm64.evm_sdiv_v5 EvmAsm.Rv64.seq
      rw [← EvmAsm.Evm64.evm_sdiv_wrapper_length]
      have h_drop :
          List.drop EvmAsm.Evm64.evm_sdiv_wrapper.length
              (EvmAsm.Evm64.evm_sdiv_wrapper ++ EvmAsm.Evm64.evm_div_callable_v5) =
            EvmAsm.Evm64.evm_div_callable_v5 := List.drop_append_length
      rw [h_drop]
      simp only [List.take_length])
    (by
      rw [EvmAsm.Evm64.evm_div_callable_v5_length, EvmAsm.Evm64.evm_sdiv_v5_length])
    (by rw [EvmAsm.Evm64.evm_sdiv_v5_length]; norm_num)

/-- Code-subsumption: the layer-1 v5 callable code region (at `wrapperEndOff`)
    is inside `sdivCodeV5`.  Feeds `cpsTripleWithin_extend_code` to lift the M2
    callable spec onto the SDIV code surface. -/
theorem evm_div_callable_code_v5_sub_sdivCodeV5 {base : Word} :
    ∀ a i,
      (EvmAsm.Evm64.evm_div_callable_code_v5 (base + wrapperEndOff)) a = some i →
      (sdivCodeV5 base) a = some i := by
  intro a i h
  have hOfProg :
      (EvmAsm.Rv64.CodeReq.ofProg
        (base + wrapperEndOff) EvmAsm.Evm64.evm_div_callable_v5) a =
        some i := by
    rw [← EvmAsm.Evm64.evm_div_callable_code_v5_eq_ofProg (base + wrapperEndOff)]
    exact h
  exact sdivCodeV5_divCallable_sub (base := base) a i
    (by simpa [divCallableCodeV5] using hOfProg)

end EvmAsm.Evm64.SDiv.Compose
