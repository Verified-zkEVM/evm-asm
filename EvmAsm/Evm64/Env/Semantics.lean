/-
  EvmAsm.Evm64.Env.Semantics

  Pure semantic bridge for simple environment opcode bytes (GH #103 slice 3).
-/

import EvmAsm.Evm64.Env.Field

namespace EvmAsm.Evm64
namespace Env

/-- Value pushed by a simple environment opcode byte, when the byte is supported. -/
def simpleEnvOpcodeValue? (opcode : Nat) (env : EvmEnv) : Option EvmWord :=
  (SimpleEnvField.ofOpcodeByte? opcode).map (fun field => field.value env)

theorem simpleEnvOpcodeValue?_of_decoded {opcode : Nat} {field : SimpleEnvField}
    (env : EvmEnv) (h_decode : SimpleEnvField.ofOpcodeByte? opcode = some field) :
    simpleEnvOpcodeValue? opcode env = some (field.value env) := by
  simp [simpleEnvOpcodeValue?, h_decode]

theorem simpleEnvOpcodeValue?_of_opcodeByte (field : SimpleEnvField) (env : EvmEnv) :
    simpleEnvOpcodeValue? field.opcodeByte env = some (field.value env) := by
  exact simpleEnvOpcodeValue?_of_decoded env (SimpleEnvField.ofOpcodeByte?_opcodeByte field)

theorem simpleEnvOpcodeValue?_of_unknown {opcode : Nat} (env : EvmEnv)
    (h_decode : SimpleEnvField.ofOpcodeByte? opcode = none) :
    simpleEnvOpcodeValue? opcode env = none := by
  simp [simpleEnvOpcodeValue?, h_decode]

@[simp] theorem simpleEnvOpcodeValue?_balance (env : EvmEnv) :
    simpleEnvOpcodeValue? 0x31 env = none := by
  exact simpleEnvOpcodeValue?_of_unknown env SimpleEnvField.ofOpcodeByte?_balance

@[simp] theorem simpleEnvOpcodeValue?_unknown_ff (env : EvmEnv) :
    simpleEnvOpcodeValue? 0xff env = none := by
  exact simpleEnvOpcodeValue?_of_unknown env SimpleEnvField.ofOpcodeByte?_unknown_ff

end Env
end EvmAsm.Evm64
