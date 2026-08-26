/-
  EvmAsm.Evm64.Env.Gas

  Static gas helpers for simple environment opcodes (issues #117 / #103).
-/

module

public import EvmAsm.Evm64.Env.Field
public import EvmAsm.Evm64.Gas

@[expose] public section

namespace EvmAsm.Evm64
namespace Env

namespace SimpleEnvField

/-- EVM opcode table entry for a simple environment field. -/
def opcode : SimpleEnvField → EvmOpcode
  | address => .ADDRESS
  | caller => .CALLER
  | callValue => .CALLVALUE
  | origin => .ORIGIN
  | gasPrice => .GASPRICE
  | coinbase => .COINBASE
  | timestamp => .TIMESTAMP
  | number => .NUMBER
  | prevrandao => .PREVRANDAO
  | gasLimit => .GASLIMIT
  | chainId => .CHAINID
  | baseFee => .BASEFEE
  | selfBalance => .SELFBALANCE

/-- Shanghai static/base gas for the simple environment opcodes. -/
def simpleEnvStaticGasCost : SimpleEnvField → Nat
  | selfBalance => 5
  | _ => 2

theorem opcode_byte (field : SimpleEnvField) :
    EvmOpcode.byte? field.opcode = some field.opcodeByte := by
  cases field <;> rfl

end SimpleEnvField

end Env
end EvmAsm.Evm64
