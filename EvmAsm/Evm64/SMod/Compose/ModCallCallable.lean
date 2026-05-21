/-
  EvmAsm.Evm64.SMod.Compose.ModCallCallable

  CodeReq bridges for the unsigned MOD callable appended after the SMOD wrapper.
-/

import EvmAsm.Evm64.DivMod.CallableV1Legacy
import EvmAsm.Evm64.DivMod.CallableV4Mod
import EvmAsm.Evm64.SMod.Compose.BaseCode

namespace EvmAsm.Evm64.SMod.Compose

theorem evm_mod_callable_code_v1_sub_smodCode {base : Word} :
    ∀ a i,
      (EvmAsm.Evm64.evm_mod_callable_code_v1 (base + wrapperEndOff)) a = some i →
      (smodCode base) a = some i := by
  intro a i h
  have hOfProg :
      (EvmAsm.Rv64.CodeReq.ofProg
        (base + wrapperEndOff) EvmAsm.Evm64.evm_mod_callable_v1) a =
        some i := by
    rw [← EvmAsm.Evm64.evm_mod_callable_code_v1_eq_ofProg (base + wrapperEndOff)]
    exact h
  exact smodCode_modCallable_sub (base := base) a i
    (by
      simpa [modCallableCode] using hOfProg)

theorem evm_mod_callable_code_v4_sub_smodCodeV4 {base : Word} :
    ∀ a i,
      (EvmAsm.Evm64.evm_mod_callable_code_v4 (base + wrapperEndOff)) a = some i →
      (smodCodeV4 base) a = some i := by
  intro a i h
  have hOfProg :
      (EvmAsm.Rv64.CodeReq.ofProg
        (base + wrapperEndOff) EvmAsm.Evm64.evm_mod_callable_v4) a =
        some i := by
    rw [← EvmAsm.Evm64.evm_mod_callable_code_v4_eq_ofProg (base + wrapperEndOff)]
    exact h
  exact smodCodeV4_modCallable_sub (base := base) a i
    (by
      simpa [modCallableCodeV4] using hOfProg)

end EvmAsm.Evm64.SMod.Compose
