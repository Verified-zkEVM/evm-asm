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

import EvmAsm.Evm64.Stack
import EvmAsm.Evm64.Environment
import EvmAsm.Evm64.Environment.Layout

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

/-- The `caller` field of the env splits off the head: `envIs base env`
    is `evmWordIs (base + addressOff) env.address ** evmWordIs (base +
    callerOff) env.caller ** rest`-shape after a single sep_perm. This
    decomposition lemma is the canonical pattern opcode handlers will
    use; it is provided here as the smallest non-trivial example. -/
theorem envIs_caller_split (base : Word) (env : EvmEnv) :
    ∃ rest : Assertion,
      envIs base env =
        (evmWordIs (base + BitVec.ofNat 64 callerOff) (addrAsWord env.caller) ** rest) := by
  refine ⟨?rest, ?eq⟩
  case rest =>
    exact
      evmWordIs (base + BitVec.ofNat 64 addressOff) (addrAsWord env.address) **
      evmWordIs (base + BitVec.ofNat 64 selfBalanceOff) env.selfBalance **
      evmWordIs (base + BitVec.ofNat 64 callValueOff) env.callValue **
      evmWordIs (base + BitVec.ofNat 64 txOriginOff) (addrAsWord env.txOrigin) **
      evmWordIs (base + BitVec.ofNat 64 gasPriceOff) env.gasPrice **
      evmWordIs (base + BitVec.ofNat 64 blockCoinbaseOff) (addrAsWord env.blockCoinbase) **
      evmWordIs (base + BitVec.ofNat 64 blockTimestampOff) env.blockTimestamp **
      evmWordIs (base + BitVec.ofNat 64 blockNumberOff) env.blockNumber **
      evmWordIs (base + BitVec.ofNat 64 blockPrevrandaoOff) env.blockPrevrandao **
      evmWordIs (base + BitVec.ofNat 64 blockGasLimitOff) env.blockGasLimit **
      evmWordIs (base + BitVec.ofNat 64 blockBaseFeeOff) env.blockBaseFee **
      evmWordIs (base + BitVec.ofNat 64 chainIdOff) env.chainId **
      ((base + BitVec.ofNat 64 callDataPtrOff)    ↦ₘ env.callDataPtr) **
      ((base + BitVec.ofNat 64 callDataLenOff)    ↦ₘ env.callDataLen) **
      ((base + BitVec.ofNat 64 returnDataPtrOff)  ↦ₘ env.returnDataPtr) **
      ((base + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ env.returnDataSize)
  case eq =>
    rw [envIs_unfold]
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
    `envSize = 448` bytes ⇒ `envCells = 56`. -/
def envCells : Nat := 56

theorem envCells_eq : envCells * 8 = envSize := by decide

end EvmEnv
end EvmAsm.Evm64
