/-
  EvmAsm.Evm64.Environment.Assertion

  Slice 3 of #100 (EVM environment context layout).

  Defines the `envIs base env` separation-logic assertion that pins every
  field of an `EvmEnv` to a concrete cell at `base + <off>` using the
  per-field offsets from `Environment.Layout`. 32-byte fields use
  `evmWordIs` (four little-endian 64-bit limbs); 8-byte fields use
  `memIs` (a single doubleword cell). 160-bit addresses are
  zero-extended to a 256-bit `EvmWord` for storage, matching the EVM
  ABI convention.

  Slice 4 (`evm-asm-xbyi`) wires this module into the umbrella and adds
  a smoke test; opcode-specific decomposition lemmas (`envIs_caller_split`
  etc.) live under the per-opcode trees and only depend on the lemmas
  exposed here.
-/

module

public import EvmAsm.Evm64.Stack
public import EvmAsm.Evm64.Environment
public import EvmAsm.Evm64.Environment.Layout

@[expose] public section

namespace EvmAsm.Evm64
namespace EvmEnv

open EvmAsm.Rv64

/-- Coerce a 160-bit Ethereum address into a 256-bit `EvmWord` by
    zero-extension. Matches how `ADDRESS`, `CALLER`, `ORIGIN`, and
    `COINBASE` deliver their results onto the EVM stack. -/
@[reducible] def addrAsWord (a : Address) : EvmWord := a.zeroExtend 256

/-- The full execution-context assertion: every field of `env` lives at
    its named offset from `base`. Field order matches the layout table
    in `Environment/Layout.lean` so a single right-associative
    `sepConj` chain mirrors the on-disk order. -/
def envIs (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Definitional unfold: `envIs base env` is the right-associative
    `sepConj` of the per-field cells. Useful as a `simp only` rewrite
    when an opcode handler needs to frame out a single field. -/
theorem envIs_unfold (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
       evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
       evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
       evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
       evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
       evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
       evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
       evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
       evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
       evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
       evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
       evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
       evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
       ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
       ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
       ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
       ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)) := rfl

/-- The remaining 16 env-field cells after the `caller` cell is rotated
    to the head of the sepConj chain. Spelled out as a top-level `def`
    so callers can frame on it explicitly and keep track of the
    resources still owned by the env block. -/
def envIsCallerRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `caller` cell to the head of `envIs base env`. The
    leftover assertion is spelled out as `envIsCallerRest base env`
    rather than hidden behind an existential, so a `CALLER` opcode
    handler that frames on the head still sees — and owns — every
    other field of the env block. -/
theorem envIs_caller_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 callerOff) (addrAsWord env.caller) **
        envIsCallerRest base env) := by
  rw [envIs_unfold]
  unfold envIsCallerRest
  ac_rfl

/-- `envIs` is PC-free: it is a finite `sepConj` of `evmWordIs` /
    `memIs` cells, all of which are individually PC-free. -/
theorem pcFree_envIs {base : Word} {env : EvmEnv} :
    (envIs base env).pcFree := by
  unfold envIs; pcFree

instance (base : Word) (env : EvmEnv) : Assertion.PCFree (envIs base env) :=
  ⟨pcFree_envIs⟩

/-! ## Footprint size

  Convenience constants for the env block's footprint, used by
  downstream slices that need to express disjointness with the
  caller's frame.
-/

/-- Number of doubleword cells that a single env block occupies.
    `envSize = 472` bytes (M24 added persistentLogCheckpoint +
    transientLogLength) ⇒ `envCells = 59`. -/
def envCells : Nat := 59

theorem envCells_eq : envCells * 8 = envSize := by decide

/-! ## Acceptance smoke tests (#100 slice 4)

  These are deliberately tiny: they only re-exercise the
  `envIs_unfold` + `ac_rfl` recipe used by `envIs_caller_split` for
  two additional representative field shapes — the `address` field
  (an `Address` already sitting at the head of the chain at offset
  0) and the `callValue` field (a non-`Address` `EvmWord` cell deep
  in the middle of the chain). Together with `envIs_caller_split`
  they cover all three field templates a future opcode handler
  (`ADDRESS`, `CALLVALUE`, `CALLER`, …) is going to invoke.
-/

/-- Remaining 16 env-field cells after the `address` cell is rotated
    to the head of the sepConj chain. Mirror of `envIsCallerRest`. -/
def envIsAddressRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `address` cell to the head. Trivial — `address` is
    already the head of `envIs`'s sepConj chain — but stated as a
    named theorem so opcode handlers (`ADDRESS`) can frame on it
    uniformly with `envIs_caller_split` / `envIs_callValue_split`. -/
theorem envIs_address_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 addressOff) (addrAsWord env.address) **
        envIsAddressRest base env) := by
  rw [envIs_unfold]
  unfold envIsAddressRest
  ac_rfl

/-- Remaining 16 env-field cells after the `callValue` cell is
    rotated to the head of the sepConj chain. Smoke test for a
    non-`Address` `EvmWord` field in the middle of the chain. -/
def envIsCallValueRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `callValue` cell (non-`Address` `EvmWord` deep in the
    chain) to the head. Mirror of `envIs_caller_split` for the
    `CALLVALUE` opcode. -/
theorem envIs_callValue_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 callValueOff) env.callValue **
        envIsCallValueRest base env) := by
  rw [envIs_unfold]
  unfold envIsCallValueRest
  ac_rfl

/-! ## Per-field rotate-to-head splits for the remaining 10 SimpleEnvFields

  Slice 4b of `evm-asm-3fvb` (#103). Mirrors `envIs_caller_split` /
  `envIs_address_split` / `envIs_callValue_split` for every other
  `SimpleEnvField` so `evm_env_load_stack_spec` (slice 5) can frame on
  whichever field its parameter selects with a single uniform rewrite.
  Each block follows the same `envIs_unfold` + `unfold <Rest>` + `ac_rfl`
  recipe.
-/

/-- Remaining 16 env-field cells after the `selfBalance` cell is
    rotated to the head of the sepConj chain. -/
def envIsSelfBalanceRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `selfBalance` cell to the head. Mirror of
    `envIs_caller_split` for the `SELFBALANCE` opcode. -/
theorem envIs_selfBalance_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 selfBalanceOff) env.selfBalance **
        envIsSelfBalanceRest base env) := by
  rw [envIs_unfold]
  unfold envIsSelfBalanceRest
  ac_rfl

/-- Remaining 16 env-field cells after the `txOrigin` cell is rotated
    to the head. -/
def envIsTxOriginRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `txOrigin` cell to the head. Mirror of
    `envIs_caller_split` for the `ORIGIN` opcode. -/
theorem envIs_origin_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 txOriginOff) (addrAsWord env.txOrigin) **
        envIsTxOriginRest base env) := by
  rw [envIs_unfold]
  unfold envIsTxOriginRest
  ac_rfl

/-- Remaining 16 env-field cells after the `gasPrice` cell is rotated
    to the head. -/
def envIsGasPriceRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `gasPrice` cell to the head. Mirror of
    `envIs_caller_split` for the `GASPRICE` opcode. -/
theorem envIs_gasPrice_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 gasPriceOff) env.gasPrice **
        envIsGasPriceRest base env) := by
  rw [envIs_unfold]
  unfold envIsGasPriceRest
  ac_rfl

/-- Remaining 16 env-field cells after the `blockCoinbase` cell is
    rotated to the head. -/
def envIsBlockCoinbaseRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `blockCoinbase` cell to the head. Mirror of
    `envIs_caller_split` for the `COINBASE` opcode. -/
theorem envIs_coinbase_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff) (addrAsWord env.blockCoinbase) **
        envIsBlockCoinbaseRest base env) := by
  rw [envIs_unfold]
  unfold envIsBlockCoinbaseRest
  ac_rfl

/-- Remaining 16 env-field cells after the `blockTimestamp` cell is
    rotated to the head. -/
def envIsBlockTimestampRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `blockTimestamp` cell to the head. Mirror of
    `envIs_caller_split` for the `TIMESTAMP` opcode. -/
theorem envIs_timestamp_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 blockTimestampOff) env.blockTimestamp **
        envIsBlockTimestampRest base env) := by
  rw [envIs_unfold]
  unfold envIsBlockTimestampRest
  ac_rfl

/-- Remaining 16 env-field cells after the `blockNumber` cell is
    rotated to the head. -/
def envIsBlockNumberRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `blockNumber` cell to the head. Mirror of
    `envIs_caller_split` for the `NUMBER` opcode. -/
theorem envIs_number_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 blockNumberOff) env.blockNumber **
        envIsBlockNumberRest base env) := by
  rw [envIs_unfold]
  unfold envIsBlockNumberRest
  ac_rfl

/-- Remaining 16 env-field cells after the `blockPrevrandao` cell is
    rotated to the head. -/
def envIsBlockPrevrandaoRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `blockPrevrandao` cell to the head. Mirror of
    `envIs_caller_split` for the `PREVRANDAO` opcode. -/
theorem envIs_prevrandao_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
        envIsBlockPrevrandaoRest base env) := by
  rw [envIs_unfold]
  unfold envIsBlockPrevrandaoRest
  ac_rfl

/-- Remaining 16 env-field cells after the `blockGasLimit` cell is
    rotated to the head. -/
def envIsBlockGasLimitRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `blockGasLimit` cell to the head. Mirror of
    `envIs_caller_split` for the `GASLIMIT` opcode. -/
theorem envIs_gasLimit_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff) env.blockGasLimit **
        envIsBlockGasLimitRest base env) := by
  rw [envIs_unfold]
  unfold envIsBlockGasLimitRest
  ac_rfl

/-- Remaining 16 env-field cells after the `chainId` cell is rotated
    to the head. -/
def envIsChainIdRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `chainId` cell to the head. Mirror of
    `envIs_caller_split` for the `CHAINID` opcode. -/
theorem envIs_chainId_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 chainIdOff) env.chainId **
        envIsChainIdRest base env) := by
  rw [envIs_unfold]
  unfold envIsChainIdRest
  ac_rfl

/-- Remaining 16 env-field cells after the `blockBaseFee` cell is
    rotated to the head. -/
def envIsBlockBaseFeeRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `blockBaseFee` cell to the head. Mirror of
    `envIs_caller_split` for the `BASEFEE` opcode. -/
theorem envIs_baseFee_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff) env.blockBaseFee **
        envIsBlockBaseFeeRest base env) := by
  rw [envIs_unfold]
  unfold envIsBlockBaseFeeRest
  ac_rfl

/-- Remaining 16 env-field cells after the `callDataLen` cell is rotated
    to the head. Used by `CALLDATASIZE` (slice 3 of `evm-asm-xjk8` /
    `evm-asm-8mp7`) to frame on the single 64-bit length cell while
    keeping ownership of every other env field. -/
def envIsCallDataLenRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the `callDataLen` cell to the head. Mirror of
    `envIs_caller_split` for the `CALLDATASIZE` opcode. -/
theorem envIs_callDataLen_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (((base + BitVec.ofNat 64 callDataLenOff) ↦ₘ env.callDataLen) **
        envIsCallDataLenRest base env) := by
  rw [envIs_unfold]
  unfold envIsCallDataLenRest
  ac_rfl

/-- Remaining 15 env-field cells after the `callDataPtr` and
    `callDataLen` cells are rotated to the head. CALLDATALOAD and
    CALLDATACOPY need the pointer/length pair together: the pointer
    identifies the source byte buffer, and the length drives the
    out-of-bounds zero-padding checks. -/
def envIsCallDataPtrLenRest (base : Word) (env : EvmEnv) : Assertion :=
  evmWordIs (base + BitVec.ofNat 64 addressOff)         (addrAsWord env.address) **
  evmWordIs (base + BitVec.ofNat 64 selfBalanceOff)     env.selfBalance **
  evmWordIs (base + BitVec.ofNat 64 callerOff)          (addrAsWord env.caller) **
  evmWordIs (base + BitVec.ofNat 64 callValueOff)       env.callValue **
  evmWordIs (base + BitVec.ofNat 64 txOriginOff)        (addrAsWord env.txOrigin) **
  evmWordIs (base + BitVec.ofNat 64 gasPriceOff)        env.gasPrice **
  evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff)   (addrAsWord env.blockCoinbase) **
  evmWordIs (base + BitVec.ofNat 64 blockTimestampOff)  env.blockTimestamp **
  evmWordIs (base + BitVec.ofNat 64 blockNumberOff)     env.blockNumber **
  evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
  evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff)   env.blockGasLimit **
  evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff)    env.blockBaseFee **
  evmWordIs (base + BitVec.ofNat 64 chainIdOff)         env.chainId **
  ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
  ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)

/-- Rotate the calldata pointer/length pair to the head of `envIs`.

    Distinctive token: `envIs_callDataPtrLen_split`. -/
theorem envIs_callDataPtrLen_split (base : Word) (env : EvmEnv) :
    envIs base env =
      (((base + BitVec.ofNat 64 callDataPtrOff) ↦ₘ env.callDataPtr) **
       ((base + BitVec.ofNat 64 callDataLenOff) ↦ₘ env.callDataLen) **
        envIsCallDataPtrLenRest base env) := by
  rw [envIs_unfold]
  unfold envIsCallDataPtrLenRest
  ac_rfl

end EvmEnv
end EvmAsm.Evm64
