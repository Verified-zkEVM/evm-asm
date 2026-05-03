/-
  EvmAsm.Evm64.Env.Field

  Shared field surface for the simple environment opcodes (GH #103 slice 1).
  The later `evm_env_load` program/spec can be parameterized by this enum
  instead of duplicating one opcode-specific setup for each environment field.
-/

import EvmAsm.Evm64.Environment.Assertion

namespace EvmAsm.Evm64
namespace Env

open EvmAsm.Rv64

/-- The 13 simple environment opcodes whose result is a 256-bit word stored in
    the environment block. Address-shaped fields are zero-extended through
    `EvmEnv.addrAsWord`. -/
inductive SimpleEnvField where
  | address
  | caller
  | callValue
  | origin
  | gasPrice
  | coinbase
  | timestamp
  | number
  | prevrandao
  | gasLimit
  | chainId
  | baseFee
  | selfBalance
  deriving DecidableEq, Repr

namespace SimpleEnvField

/-- Canonical EVM opcode byte for this simple environment field. -/
def opcodeByte : SimpleEnvField → Nat
  | address => 0x30
  | caller => 0x33
  | callValue => 0x34
  | origin => 0x32
  | gasPrice => 0x3a
  | coinbase => 0x41
  | timestamp => 0x42
  | number => 0x43
  | prevrandao => 0x44
  | gasLimit => 0x45
  | chainId => 0x46
  | baseFee => 0x48
  | selfBalance => 0x47

/-- Decode an opcode byte when it is one of the simple environment opcodes. -/
def ofOpcodeByte? : Nat → Option SimpleEnvField
  | 0x30 => some address
  | 0x32 => some origin
  | 0x33 => some caller
  | 0x34 => some callValue
  | 0x3a => some gasPrice
  | 0x41 => some coinbase
  | 0x42 => some timestamp
  | 0x43 => some number
  | 0x44 => some prevrandao
  | 0x45 => some gasLimit
  | 0x46 => some chainId
  | 0x47 => some selfBalance
  | 0x48 => some baseFee
  | _ => none

/-- Byte offset of the field in the `envIs` block. Every simple env field is
    represented as a 32-byte slot. -/
def offset : SimpleEnvField → Nat
  | address => EvmEnv.addressOff
  | caller => EvmEnv.callerOff
  | callValue => EvmEnv.callValueOff
  | origin => EvmEnv.txOriginOff
  | gasPrice => EvmEnv.gasPriceOff
  | coinbase => EvmEnv.blockCoinbaseOff
  | timestamp => EvmEnv.blockTimestampOff
  | number => EvmEnv.blockNumberOff
  | prevrandao => EvmEnv.blockPrevrandaoOff
  | gasLimit => EvmEnv.blockGasLimitOff
  | chainId => EvmEnv.chainIdOff
  | baseFee => EvmEnv.blockBaseFeeOff
  | selfBalance => EvmEnv.selfBalanceOff

/-- Value pushed by the corresponding simple environment opcode. -/
def value (field : SimpleEnvField) (env : EvmEnv) : EvmWord :=
  match field with
  | address => EvmEnv.addrAsWord env.address
  | caller => EvmEnv.addrAsWord env.caller
  | callValue => env.callValue
  | origin => EvmEnv.addrAsWord env.txOrigin
  | gasPrice => env.gasPrice
  | coinbase => EvmEnv.addrAsWord env.blockCoinbase
  | timestamp => env.blockTimestamp
  | number => env.blockNumber
  | prevrandao => env.blockPrevrandao
  | gasLimit => env.blockGasLimit
  | chainId => env.chainId
  | baseFee => env.blockBaseFee
  | selfBalance => env.selfBalance

/-- Address of this field's 32-byte slot relative to an environment base. -/
def slotAddr (base : Word) (field : SimpleEnvField) : Word :=
  base + BitVec.ofNat 64 field.offset

/-- The individual `envIs` cell that an `evm_env_load field` handler will read. -/
def cellIs (base : Word) (field : SimpleEnvField) (env : EvmEnv) : Assertion :=
  evmWordIs (slotAddr base field) (field.value env)

theorem offset_align (field : SimpleEnvField) :
    field.offset % 32 = 0 := by
  cases field <;> decide

theorem ofOpcodeByte?_opcodeByte (field : SimpleEnvField) :
    ofOpcodeByte? field.opcodeByte = some field := by
  cases field <;> rfl

theorem ofOpcodeByte?_balance :
    ofOpcodeByte? 0x31 = none := rfl

theorem ofOpcodeByte?_unknown_ff :
    ofOpcodeByte? 0xff = none := rfl

theorem cellIs_unfold (base : Word) (field : SimpleEnvField) (env : EvmEnv) :
    cellIs base field env =
      evmWordIs (base + BitVec.ofNat 64 field.offset) (field.value env) := rfl

theorem pcFree_cellIs {base : Word} {field : SimpleEnvField} {env : EvmEnv} :
    (cellIs base field env).pcFree := by
  unfold cellIs
  exact pcFree_evmWordIs

instance (base : Word) (field : SimpleEnvField) (env : EvmEnv) :
    Assertion.PCFree (cellIs base field env) :=
  ⟨pcFree_cellIs⟩

theorem value_address (env : EvmEnv) :
    value address env = EvmEnv.addrAsWord env.address := rfl

theorem value_caller (env : EvmEnv) :
    value caller env = EvmEnv.addrAsWord env.caller := rfl

theorem value_callValue (env : EvmEnv) :
    value callValue env = env.callValue := rfl

theorem value_selfBalance (env : EvmEnv) :
    value selfBalance env = env.selfBalance := rfl

end SimpleEnvField

end Env
end EvmAsm.Evm64
