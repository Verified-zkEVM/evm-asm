/-
  EvmAsm.Evm64.SMod.Compose.ModCallCallable

  CodeReq bridges for the unsigned MOD callable appended after the SMOD wrapper.
-/

module

public import EvmAsm.Evm64.DivMod.CallableV1Legacy
public import EvmAsm.Evm64.DivMod.CallableV4Mod
public import EvmAsm.Evm64.SMod.Compose.BaseCode

@[expose] public section

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

/-- The v4 MOD no-NOP body code is a sub-region of `smodCodeV4`. -/
theorem modCode_noNop_v4_sub_smodCodeV4 {base : Word} :
    ∀ a i,
      (EvmAsm.Evm64.modCode_noNop_v4 (base + wrapperEndOff)) a = some i →
      (smodCodeV4 base) a = some i := fun a i h =>
  evm_mod_callable_code_v4_sub_smodCodeV4
    a i (EvmAsm.Evm64.modCode_noNop_v4_sub_mod_callable_code_v4 a i h)

/-- The appended v4 unsigned MOD callable is a sub-region of the canonical
    production SMOD code handle. -/
theorem evm_mod_callable_code_v4_sub_smodCodeCanonical {base : Word} :
    ∀ a i,
      (EvmAsm.Evm64.evm_mod_callable_code_v4 (base + wrapperEndOff)) a = some i →
      (smodCodeCanonical base) a = some i := by
  simpa [smodCodeCanonical] using evm_mod_callable_code_v4_sub_smodCodeV4 (base := base)

end EvmAsm.Evm64.SMod.Compose
