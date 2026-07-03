/-
  EvmAsm.Evm64.SMod.Compose.CodeHandlesV5

  v5 code-region inclusion lemmas for the SMOD wrapper: the appended v5 unsigned
  modulo callable `evm_mod_callable_v5` sits inside `smodCodeV5` at the
  `wrapperEndOff` offset.  Mirrors the SDIV `CodeHandlesV5`.  Foundational brick
  for the SMOD `.proven` flip over `evm_mod_callable_v5`.
-/

import EvmAsm.Evm64.SMod.Compose.ModCallCallable
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.SMod.Compose.CodeHandles

namespace EvmAsm.Evm64.SMod.Compose

/-- The appended v5 unsigned modulo callable region is inside `smodCodeV5`. -/
theorem smodCodeV5_modCallable_sub {base : Word} :
    ∀ a i, (modCallableCodeV5 base) a = some i → (smodCodeV5 base) a = some i := by
  unfold modCallableCodeV5 smodCodeV5
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + wrapperEndOff)
    EvmAsm.Evm64.evm_smod_v5 EvmAsm.Evm64.evm_mod_callable_v5 71
    (by simp [wrapperEndOff])
    (by
      unfold EvmAsm.Evm64.evm_smod_v5 EvmAsm.Rv64.seq
      rw [← EvmAsm.Evm64.evm_smod_wrapper_length]
      have h_drop :
          List.drop EvmAsm.Evm64.evm_smod_wrapper.length
              (EvmAsm.Evm64.evm_smod_wrapper ++ EvmAsm.Evm64.evm_mod_callable_v5) =
            EvmAsm.Evm64.evm_mod_callable_v5 := List.drop_append_length
      rw [h_drop]
      simp only [List.take_length])
    (by
      rw [EvmAsm.Evm64.evm_mod_callable_v5_length, EvmAsm.Evm64.evm_smod_v5_length])
    (by rw [EvmAsm.Evm64.evm_smod_v5_length]; norm_num)

/-- Code-subsumption: the layer-1 v5 callable code region (at `wrapperEndOff`)
    is inside `smodCodeV5`.  Feeds `cpsTripleWithin_extend_code` to lift the M2
    mod callable spec onto the SMOD code surface. -/
theorem evm_mod_callable_code_v5_sub_smodCodeV5 {base : Word} :
    ∀ a i,
      (EvmAsm.Evm64.evm_mod_callable_code_v5 (base + wrapperEndOff)) a = some i →
      (smodCodeV5 base) a = some i := by
  intro a i h
  have hOfProg :
      (EvmAsm.Rv64.CodeReq.ofProg
        (base + wrapperEndOff) EvmAsm.Evm64.evm_mod_callable_v5) a =
        some i := by
    rw [← EvmAsm.Evm64.evm_mod_callable_code_v5_eq_ofProg (base + wrapperEndOff)]
    exact h
  exact smodCodeV5_modCallable_sub (base := base) a i
    (by simpa [modCallableCodeV5] using hOfProg)

end EvmAsm.Evm64.SMod.Compose
