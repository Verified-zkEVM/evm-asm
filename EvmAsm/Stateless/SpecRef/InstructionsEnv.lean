/-
  EvmAsm.Stateless.SpecRef.InstructionsEnv

  Port of the environment/block instruction families of
  `execution-specs/src/ethereum/forks/amsterdam/vm/instructions/`
  (`@tests-zkevm@v0.5.0`, `bd8c673`) — bead `evm-asm-s1d19.5`:

  * `environment.py` — `address`, `balance`, `origin`, `caller`,
    `callvalue`, `calldataload`, `calldatasize`, `calldatacopy`,
    `codesize`, `codecopy`, `gasprice`, `extcodesize`, `extcodecopy`,
    `returndatasize`, `returndatacopy`, `extcodehash`, `self_balance`,
    `base_fee`, `blob_hash`, `blob_base_fee` (functions of the same
    names)
  * `block.py` — `block_hash`, `coinbase`, `timestamp`, `number`,
    `gas_limit`, `chain_id`, `prev_randao`, `slot_number` (functions of
    the same names)

  plus `to_address_masked` from `utils/address.py`
  (`execution-specs/src/ethereum/forks/amsterdam/utils/address.py`,
  function `to_address_masked`) and the remaining `OPCODE_*` constants
  they charge.
-/

import EvmAsm.Stateless.SpecRef.InstructionsCore

namespace EvmAsm.Stateless.SpecRef

namespace GasCosts

def OPCODE_ADDRESS : Uint := 2
def OPCODE_BASEFEE : Uint := 2
def OPCODE_BLOBBASEFEE : Uint := 2
def OPCODE_BLOBHASH : Uint := 3
def OPCODE_BLOCKHASH : Uint := 20
def OPCODE_CALLDATACOPY_BASE : Uint := 3
def OPCODE_CALLDATASIZE : Uint := 2
def OPCODE_CALLER : Uint := 2
def OPCODE_CALLVALUE : Uint := 2
def OPCODE_CHAINID : Uint := 2
def OPCODE_CODECOPY_BASE : Uint := 3
def OPCODE_CODESIZE : Uint := 2
def OPCODE_COINBASE : Uint := 2
def OPCODE_GASLIMIT : Uint := 2
def OPCODE_GASPRICE : Uint := 2
def OPCODE_NUMBER : Uint := 2
def OPCODE_ORIGIN : Uint := 2
def OPCODE_PREVRANDAO : Uint := 2
def OPCODE_RETURNDATACOPY_BASE : Uint := 3
def OPCODE_RETURNDATACOPY_PER_WORD : Uint := 3
def OPCODE_RETURNDATASIZE : Uint := 2
def OPCODE_SLOTNUM : Uint := 2
def OPCODE_TIMESTAMP : Uint := 2

end GasCosts

/-- `to_address_masked(u256)` (`utils/address.py`): the low 20 bytes. -/
def to_address_masked (x : U256) : Address :=
  natToBytesBE 20 (x % 2^160)

/-- EIP-2929 warm/cold account accounting shared by
    `balance`/`extcode*` (and the call family). -/
def accessGasCost (address : Address) : EvmM Uint := do
  if (← EvmM.getEvm).accessedAddresses.contains address then
    pure GasCosts.WARM_ACCESS
  else do
    EvmM.modifyEvm (fun e =>
      { e with accessedAddresses := setAdd e.accessedAddresses address })
    pure GasCosts.COLD_ACCOUNT_ACCESS

private def pcNext : EvmM Unit :=
  EvmM.modifyEvm (fun e => { e with pc := e.pc + 1 })

private def pushConst (gas : Uint) (v : U256) : EvmM Unit := do
  charge_gas gas
  stackPush v
  pcNext

/-! ## `environment.py` -/

def iAddress : EvmM Unit := do
  charge_gas GasCosts.OPCODE_ADDRESS
  stackPush (bytesBEtoNat (← EvmM.getEvm).message.currentTarget)
  pcNext

def iBalance : EvmM Unit := do
  let address := to_address_masked (← stackPop)
  charge_gas (← accessGasCost address)
  stackPush (← EvmM.liftTx (getAccount address)).balance
  pcNext

def iOrigin : EvmM Unit := do
  charge_gas GasCosts.OPCODE_ORIGIN
  stackPush (bytesBEtoNat (← EvmM.getEvm).message.txEnv.origin)
  pcNext

def iCaller : EvmM Unit := do
  charge_gas GasCosts.OPCODE_CALLER
  stackPush (bytesBEtoNat (← EvmM.getEvm).message.caller)
  pcNext

def iCallvalue : EvmM Unit := do
  charge_gas GasCosts.OPCODE_CALLVALUE
  stackPush (← EvmM.getEvm).message.value
  pcNext

def iCalldataload : EvmM Unit := do
  let start_index ← stackPop
  charge_gas GasCosts.OPCODE_CALLDATALOAD
  stackPush (bytesBEtoNat (buffer_read (← EvmM.getEvm).message.data start_index 32))
  pcNext

def iCalldatasize : EvmM Unit := do
  charge_gas GasCosts.OPCODE_CALLDATASIZE
  stackPush (← EvmM.getEvm).message.data.length
  pcNext

/-- The shared copy shape of `calldatacopy`/`codecopy`. -/
private def copyFromBuffer (base : Uint) (getBuffer : Evm → Bytes) : EvmM Unit := do
  let memory_start_index ← stackPop
  let data_start_index ← stackPop
  let size ← stackPop
  let words := ceil32 size / 32
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_start_index, size)]) <$> EvmM.getEvm
  charge_gas (base + GasCosts.OPCODE_COPY_PER_WORD * words + extend.cost)
  extendMemory extend.expandBy
  EvmM.modifyEvm (fun e =>
    let value := buffer_read (getBuffer e) data_start_index size
    { e with memory := memory_write e.memory memory_start_index value })
  pcNext

def iCalldatacopy : EvmM Unit :=
  copyFromBuffer GasCosts.OPCODE_CALLDATACOPY_BASE (·.message.data)

def iCodesize : EvmM Unit := do
  charge_gas GasCosts.OPCODE_CODESIZE
  stackPush (← EvmM.getEvm).code.length
  pcNext

def iCodecopy : EvmM Unit :=
  copyFromBuffer GasCosts.OPCODE_CODECOPY_BASE (·.code)

def iGasprice : EvmM Unit := do
  charge_gas GasCosts.OPCODE_GASPRICE
  stackPush (← EvmM.getEvm).message.txEnv.gasPrice
  pcNext

/-- The account's code through the tracker (`get_account` +
    `get_code`). -/
def extCodeOf (address : Address) : EvmM Bytes := do
  let code_hash := (← EvmM.liftTx (getAccount address)).codeHash
  EvmM.liftTx (getCode code_hash address)

def iExtcodesize : EvmM Unit := do
  let address := to_address_masked (← stackPop)
  -- + WARM_ACCESS: EIP-8038 code reading cost.
  charge_gas ((← accessGasCost address) + GasCosts.WARM_ACCESS)
  stackPush (← extCodeOf address).length
  pcNext

def iExtcodecopy : EvmM Unit := do
  let address := to_address_masked (← stackPop)
  let memory_start_index ← stackPop
  let code_start_index ← stackPop
  let size ← stackPop
  let words := ceil32 size / 32
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_start_index, size)]) <$> EvmM.getEvm
  let access ← accessGasCost address
  charge_gas (access + GasCosts.WARM_ACCESS
    + GasCosts.OPCODE_COPY_PER_WORD * words + extend.cost)
  extendMemory extend.expandBy
  let code ← extCodeOf address
  EvmM.modifyEvm (fun e =>
    let value := buffer_read code code_start_index size
    { e with memory := memory_write e.memory memory_start_index value })
  pcNext

def iReturndatasize : EvmM Unit := do
  charge_gas GasCosts.OPCODE_RETURNDATASIZE
  stackPush (← EvmM.getEvm).returnData.length
  pcNext

def iReturndatacopy : EvmM Unit := do
  let memory_start_index ← stackPop
  let return_data_start_position ← stackPop
  let size ← stackPop
  let words := ceil32 size / 32
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_start_index, size)]) <$> EvmM.getEvm
  charge_gas (GasCosts.OPCODE_RETURNDATACOPY_BASE
    + GasCosts.OPCODE_RETURNDATACOPY_PER_WORD * words + extend.cost)
  let e ← EvmM.getEvm
  if return_data_start_position + size > e.returnData.length then
    throw .outOfBoundsRead
  extendMemory extend.expandBy
  EvmM.modifyEvm (fun e =>
    let value := (e.returnData.drop return_data_start_position).take size
    { e with memory := memory_write e.memory memory_start_index value })
  pcNext

def iExtcodehash : EvmM Unit := do
  let address := to_address_masked (← stackPop)
  charge_gas (← accessGasCost address)
  let account ← EvmM.liftTx (getAccount address)
  stackPush (if account == EMPTY_ACCOUNT then 0 else bytesBEtoNat account.codeHash)
  pcNext

def iSelfbalance : EvmM Unit := do
  charge_gas GasCosts.FAST_STEP
  let target := (← EvmM.getEvm).message.currentTarget
  stackPush (← EvmM.liftTx (getAccount target)).balance
  pcNext

def iBasefee : EvmM Unit := do
  pushConst GasCosts.OPCODE_BASEFEE (← EvmM.getEvm).message.blockEnv.baseFeePerGas

def iBlobhash : EvmM Unit := do
  let index ← stackPop
  charge_gas GasCosts.OPCODE_BLOBHASH
  let hashes := (← EvmM.getEvm).message.txEnv.blobVersionedHashes
  stackPush (bytesBEtoNat ((hashes.getD index (List.replicate 32 0x00))))
  pcNext

def iBlobbasefee : EvmM Unit := do
  charge_gas GasCosts.OPCODE_BLOBBASEFEE
  let price ← EvmM.liftSpec
    (calculate_blob_gas_price (← EvmM.getEvm).message.blockEnv.excessBlobGas)
  stackPush price
  pcNext

/-! ## `block.py` -/

def iBlockhash : EvmM Unit := do
  let block_number ← stackPop
  charge_gas GasCosts.OPCODE_BLOCKHASH
  let e ← EvmM.getEvm
  let current := e.message.blockEnv.number
  if current ≤ block_number || current > block_number + 256 then
    stackPush 0
  else do
    let hashes := e.message.blockEnv.blockHashes
    let offset := current - block_number
    -- Python `block_hashes[-offset]`; an out-of-range index (fewer
    -- witness headers than the touched depth) is an uncaught
    -- `IndexError` → rejection, not a halt.
    if offset > hashes.length then
      EvmM.liftSpec (throw (.executionRejected "BLOCKHASH beyond witness headers"))
    let h := hashes.getD (hashes.length - offset) (List.replicate 32 0x00)
    EvmM.liftTx (trackAncestorAccess offset)
    stackPush (bytesBEtoNat h)
  pcNext

def iCoinbase : EvmM Unit := do
  pushConst GasCosts.OPCODE_COINBASE
    (bytesBEtoNat (← EvmM.getEvm).message.blockEnv.coinbase)

def iTimestamp : EvmM Unit := do
  pushConst GasCosts.OPCODE_TIMESTAMP (← EvmM.getEvm).message.blockEnv.time

def iNumber : EvmM Unit := do
  pushConst GasCosts.OPCODE_NUMBER (← EvmM.getEvm).message.blockEnv.number

def iGaslimit : EvmM Unit := do
  pushConst GasCosts.OPCODE_GASLIMIT (← EvmM.getEvm).message.blockEnv.blockGasLimit

def iChainid : EvmM Unit := do
  pushConst GasCosts.OPCODE_CHAINID (← EvmM.getEvm).message.blockEnv.chainId

def iPrevrandao : EvmM Unit := do
  pushConst GasCosts.OPCODE_PREVRANDAO
    (bytesBEtoNat (← EvmM.getEvm).message.blockEnv.prevRandao)

def iSlotnum : EvmM Unit := do
  pushConst GasCosts.OPCODE_SLOTNUM (← EvmM.getEvm).message.blockEnv.slotNumber

end EvmAsm.Stateless.SpecRef
