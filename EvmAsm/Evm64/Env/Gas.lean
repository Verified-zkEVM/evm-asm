/-
  EvmAsm.Evm64.Env.Gas

  Static gas helpers for simple environment opcodes (issues #117 / #103).
-/

import EvmAsm.Evm64.Env.Field

namespace EvmAsm.Evm64
namespace Env

namespace SimpleEnvField

/-- Shanghai static/base gas for the simple environment opcodes. -/
def simpleEnvStaticGasCost (_field : SimpleEnvField) : Nat := 2

@[simp] theorem simpleEnvStaticGasCost_eq_two (field : SimpleEnvField) :
    simpleEnvStaticGasCost field = 2 := rfl

theorem simpleEnvStaticGasCost_address :
    simpleEnvStaticGasCost address = 2 := rfl

theorem simpleEnvStaticGasCost_selfBalance :
    simpleEnvStaticGasCost selfBalance = 2 := rfl

theorem simpleEnvStaticGasCost_cases (field : SimpleEnvField) :
    match field with
    | address => simpleEnvStaticGasCost address = 2
    | caller => simpleEnvStaticGasCost caller = 2
    | callValue => simpleEnvStaticGasCost callValue = 2
    | origin => simpleEnvStaticGasCost origin = 2
    | gasPrice => simpleEnvStaticGasCost gasPrice = 2
    | coinbase => simpleEnvStaticGasCost coinbase = 2
    | timestamp => simpleEnvStaticGasCost timestamp = 2
    | number => simpleEnvStaticGasCost number = 2
    | prevrandao => simpleEnvStaticGasCost prevrandao = 2
    | gasLimit => simpleEnvStaticGasCost gasLimit = 2
    | chainId => simpleEnvStaticGasCost chainId = 2
    | baseFee => simpleEnvStaticGasCost baseFee = 2
    | selfBalance => simpleEnvStaticGasCost selfBalance = 2 := by
  cases field <;> rfl

end SimpleEnvField

end Env
end EvmAsm.Evm64
