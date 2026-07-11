/-
  EvmAsm.Stateless.SpecRef.InstructionsCore

  Port of the non-system instruction families of
  `execution-specs/src/ethereum/forks/amsterdam/vm/instructions/`
  (`@tests-zkevm@v0.5.0`, `bd8c673`) — bead `evm-asm-s1d19.5`, Stack C
  stage 4:

  * `arithmetic.py` — `add`, `sub`, `mul`, `div`, `sdiv`, `mod`,
    `smod`, `addmod`, `mulmod`, `exp`, `signextend` (functions of the
    same names)
  * `comparison.py` — `less_than`, `signed_less_than`, `greater_than`,
    `signed_greater_than`, `equal`, `is_zero`
  * `bitwise.py` — `bitwise_and`, `bitwise_or`, `bitwise_xor`,
    `bitwise_not`, `get_byte`, `bitwise_shl`, `bitwise_shr`,
    `bitwise_sar`, `count_leading_zeros`
  * `keccak.py` — `keccak` (function `keccak`)
  * `control_flow.py` — `stop`, `jump`, `jumpi`, `pc`, `gas_left`,
    `jumpdest`
  * `memory.py` — `mstore`, `mstore8`, `mload`, `msize`, `mcopy`
  * `stack.py` (instructions) — `pop`, `push_n`, `dup_n`, `swap_n`,
    `dupn`, `swapn`, `exchange` (functions of the same names)
  * `log.py` — `log_n` (function `log_n`)
  * `storage.py` — `sload`, `sstore`, `tload`, `tstore`

  plus the per-opcode `OPCODE_*` gas constants (`vm/gas.py`, class
  `GasCosts`), added here into the open `GasCosts` namespace.

  Values are unbounded `Nat` capped explicitly at 2²⁵⁶ (`wrap256` at
  every arithmetic site, mirroring the Python `U256` wrapping ops);
  the stack holds its TOP at the list HEAD (Python appends at the end),
  so Python's `stack[-1 - n]` is index `n` here.
-/

import EvmAsm.Stateless.SpecRef.Vm

namespace EvmAsm.Stateless.SpecRef

namespace GasCosts

def OPCODE_ADD : Uint := 3
def OPCODE_ADDMOD : Uint := 8
def OPCODE_AND : Uint := 3
def OPCODE_BYTE : Uint := 3
def OPCODE_CALLDATALOAD : Uint := 3
def OPCODE_CLZ : Uint := 5
def OPCODE_COPY_PER_WORD : Uint := 3
def OPCODE_DIV : Uint := 5
def OPCODE_DUP : Uint := 3
def OPCODE_DUPN : Uint := 3
def OPCODE_EQ : Uint := 3
def OPCODE_EXCHANGE : Uint := 3
def OPCODE_EXP_BASE : Uint := 10
def OPCODE_EXP_PER_BYTE : Uint := 50
def OPCODE_GAS : Uint := 2
def OPCODE_GT : Uint := 3
def OPCODE_ISZERO : Uint := 3
def OPCODE_JUMP : Uint := 8
def OPCODE_JUMPDEST : Uint := 1
def OPCODE_JUMPI : Uint := 10
def OPCODE_KECCAK256_BASE : Uint := 30
def OPCODE_KECCAK256_PER_WORD : Uint := 6
def OPCODE_LOG_BASE : Uint := 375
def OPCODE_LOG_DATA_PER_BYTE : Uint := 8
def OPCODE_LOG_TOPIC : Uint := 375
def OPCODE_LT : Uint := 3
def OPCODE_MCOPY_BASE : Uint := 3
def OPCODE_MLOAD_BASE : Uint := 3
def OPCODE_MOD : Uint := 5
def OPCODE_MSIZE : Uint := 2
def OPCODE_MSTORE8_BASE : Uint := 3
def OPCODE_MSTORE_BASE : Uint := 3
def OPCODE_MUL : Uint := 5
def OPCODE_MULMOD : Uint := 8
def OPCODE_NOT : Uint := 3
def OPCODE_OR : Uint := 3
def OPCODE_PC : Uint := 2
def OPCODE_POP : Uint := 2
def OPCODE_PUSH : Uint := 3
def OPCODE_PUSH0 : Uint := 2
def OPCODE_SAR : Uint := 3
def OPCODE_SDIV : Uint := 5
def OPCODE_SGT : Uint := 3
def OPCODE_SHL : Uint := 3
def OPCODE_SHR : Uint := 3
def OPCODE_SIGNEXTEND : Uint := 5
def OPCODE_SLT : Uint := 3
def OPCODE_SMOD : Uint := 5
def OPCODE_SUB : Uint := 3
def OPCODE_SWAP : Uint := 3
def OPCODE_SWAPN : Uint := 3
def OPCODE_TLOAD : Uint := 100
def OPCODE_TSTORE : Uint := 100
def OPCODE_XOR : Uint := 3

end GasCosts

/-! ## U256 helpers (`ethereum_types.numeric.U256`) -/

def U256_MOD : Nat := 2^256
def U256_MAX : Nat := 2^256 - 1

/-- Wrap into the U256 range (`wrapping_add`/`sub`/`mul` etc.). -/
def wrap256 (n : Nat) : U256 := n % U256_MOD

/-- `U256.to_signed()`: two's-complement read. -/
def toSigned (x : U256) : Int :=
  if x < 2^255 then (x : Int) else (x : Int) - (U256_MOD : Int)

/-- `U256.from_signed(v)`: two's-complement write. -/
def fromSigned (v : Int) : U256 :=
  (v % (U256_MOD : Int)).toNat

/-- `x.to_be_bytes32()`. -/
def toBeBytes32 (x : U256) : Bytes := natToBytesBE 32 x

/-- Advance the program counter. -/
private def pcAdd (n : Nat) : EvmM Unit :=
  EvmM.modifyEvm (fun e => { e with pc := e.pc + n })

/-- The shared shape of a binary op: pop 2, charge, push, `pc += 1`. -/
private def binOp (gas : Uint) (f : U256 → U256 → U256) : EvmM Unit := do
  let x ← stackPop
  let y ← stackPop
  charge_gas gas
  stackPush (f x y)
  pcAdd 1

private def unOp (gas : Uint) (f : U256 → U256) : EvmM Unit := do
  let x ← stackPop
  charge_gas gas
  stackPush (f x)
  pcAdd 1

/-! ## `arithmetic.py` -/

def iAdd : EvmM Unit := binOp GasCosts.OPCODE_ADD (fun x y => wrap256 (x + y))
def iSub : EvmM Unit := binOp GasCosts.OPCODE_SUB (fun x y => wrap256 (U256_MOD + x - y))
def iMul : EvmM Unit := binOp GasCosts.OPCODE_MUL (fun x y => wrap256 (x * y))
def iDiv : EvmM Unit := binOp GasCosts.OPCODE_DIV (fun x y => if y == 0 then 0 else x / y)

/-- `sdiv`: truncated signed division with the `-2²⁵⁵ / -1` special
    case. -/
def iSdiv : EvmM Unit := binOp GasCosts.OPCODE_SDIV (fun x y =>
  let a := toSigned x
  let b := toSigned y
  if b == 0 then 0
  else if a == -(2^255 : Int) && b == -1 then fromSigned (-(2^255 : Int))
  else
    let q : Int := (if a * b < 0 then -1 else 1) * ((a.natAbs / b.natAbs : Nat) : Int)
    fromSigned q)

def iMod : EvmM Unit := binOp GasCosts.OPCODE_MOD (fun x y => if y == 0 then 0 else x % y)

/-- `smod`: sign follows the dividend. -/
def iSmod : EvmM Unit := binOp GasCosts.OPCODE_SMOD (fun x y =>
  let a := toSigned x
  let b := toSigned y
  if b == 0 then 0
  else fromSigned ((if a < 0 then -1 else 1) * ((a.natAbs % b.natAbs : Nat) : Int)))

def iAddmod : EvmM Unit := do
  let x ← stackPop
  let y ← stackPop
  let z ← stackPop
  charge_gas GasCosts.OPCODE_ADDMOD
  stackPush (if z == 0 then 0 else (x + y) % z)
  pcAdd 1

def iMulmod : EvmM Unit := do
  let x ← stackPop
  let y ← stackPop
  let z ← stackPop
  charge_gas GasCosts.OPCODE_MULMOD
  stackPush (if z == 0 then 0 else (x * y) % z)
  pcAdd 1

def iExp : EvmM Unit := do
  let base ← stackPop
  let exponent ← stackPop
  let exponent_bytes := (Nat.log2 (max exponent 1) + 1 + 7) / 8
  let exponent_bytes := if exponent == 0 then 0 else exponent_bytes
  charge_gas (GasCosts.OPCODE_EXP_BASE + GasCosts.OPCODE_EXP_PER_BYTE * exponent_bytes)
  stackPush (EvmAsm.Rv64.Accel.powMod base exponent U256_MOD)
  pcAdd 1

def iSignextend : EvmM Unit := binOp GasCosts.OPCODE_SIGNEXTEND (fun byte_num value =>
  if byte_num > 31 then value
  else
    let bits := (byte_num + 1) * 8
    let low := value % 2^bits
    if low < 2^(bits - 1) then low
    else low + (U256_MOD - 2^bits))

/-! ## `comparison.py` -/

private def boolPush (b : Bool) : U256 := if b then 1 else 0

def iLt : EvmM Unit := binOp GasCosts.OPCODE_LT (fun x y => boolPush (x < y))
def iGt : EvmM Unit := binOp GasCosts.OPCODE_GT (fun x y => boolPush (x > y))
def iSlt : EvmM Unit := binOp GasCosts.OPCODE_SLT (fun x y => boolPush (toSigned x < toSigned y))
def iSgt : EvmM Unit := binOp GasCosts.OPCODE_SGT (fun x y => boolPush (toSigned x > toSigned y))
def iEq : EvmM Unit := binOp GasCosts.OPCODE_EQ (fun x y => boolPush (x == y))
def iIszero : EvmM Unit := unOp GasCosts.OPCODE_ISZERO (fun x => boolPush (x == 0))

/-! ## `bitwise.py` -/

def iAnd : EvmM Unit := binOp GasCosts.OPCODE_AND (fun x y => x &&& y)
def iOr : EvmM Unit := binOp GasCosts.OPCODE_OR (fun x y => x ||| y)
def iXor : EvmM Unit := binOp GasCosts.OPCODE_XOR (fun x y => x ^^^ y)
def iNot : EvmM Unit := unOp GasCosts.OPCODE_NOT (fun x => U256_MAX - x)

def iByte : EvmM Unit := binOp GasCosts.OPCODE_BYTE (fun byte_index word =>
  if byte_index ≥ 32 then 0
  else (word >>> ((31 - byte_index) * 8)) &&& 0xFF)

def iShl : EvmM Unit := binOp GasCosts.OPCODE_SHL (fun shift value =>
  if shift < 256 then wrap256 (value <<< shift) else 0)

def iShr : EvmM Unit := binOp GasCosts.OPCODE_SHR (fun shift value =>
  if shift < 256 then value >>> shift else 0)

def iSar : EvmM Unit := binOp GasCosts.OPCODE_SAR (fun shift value =>
  let sv := toSigned value
  -- Python `>>` on int is an arithmetic shift = floor division.
  if shift < 256 then fromSigned (Int.fdiv sv (2^shift))
  else if sv ≥ 0 then 0 else U256_MAX)

/-- `count_leading_zeros` (EIP-7939). -/
def iClz : EvmM Unit := unOp GasCosts.OPCODE_CLZ (fun x =>
  let bit_length := if x == 0 then 0 else Nat.log2 x + 1
  256 - bit_length)

/-! ## `keccak.py` -/

def iKeccak : EvmM Unit := do
  let memory_start_index ← stackPop
  let size ← stackPop
  let words := ceil32 size / 32
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_start_index, size)]) <$> EvmM.getEvm
  charge_gas (GasCosts.OPCODE_KECCAK256_BASE
    + GasCosts.OPCODE_KECCAK256_PER_WORD * words + extend.cost)
  extendMemory extend.expandBy
  let data := memory_read_bytes (← EvmM.getEvm).memory memory_start_index size
  stackPush (bytesBEtoNat (keccak256 data))
  pcAdd 1

/-! ## `control_flow.py` -/

def iStop : EvmM Unit := do
  EvmM.modifyEvm (fun e => { e with running := false })
  pcAdd 1

def iJump : EvmM Unit := do
  let jump_dest ← stackPop
  charge_gas GasCosts.OPCODE_JUMP
  if !(← EvmM.getEvm).validJumpDestinations.contains jump_dest then
    throw .invalidJumpDest
  EvmM.modifyEvm (fun e => { e with pc := jump_dest })

def iJumpi : EvmM Unit := do
  let jump_dest ← stackPop
  let conditional_value ← stackPop
  charge_gas GasCosts.OPCODE_JUMPI
  if conditional_value == 0 then
    pcAdd 1
  else if !(← EvmM.getEvm).validJumpDestinations.contains jump_dest then
    throw .invalidJumpDest
  else
    EvmM.modifyEvm (fun e => { e with pc := jump_dest })

def iPc : EvmM Unit := do
  charge_gas GasCosts.OPCODE_PC
  stackPush (← EvmM.getEvm).pc
  pcAdd 1

def iGas : EvmM Unit := do
  charge_gas GasCosts.OPCODE_GAS
  stackPush (← EvmM.getEvm).gasLeft
  pcAdd 1

def iJumpdest : EvmM Unit := do
  charge_gas GasCosts.OPCODE_JUMPDEST
  pcAdd 1

/-! ## `memory.py` (instructions) -/

private def chargeWithMemory (base : Uint) (extensions : List (U256 × U256)) :
    EvmM Unit := do
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length extensions)
    <$> EvmM.getEvm
  charge_gas (base + extend.cost)
  extendMemory extend.expandBy

def iMstore : EvmM Unit := do
  let start_position ← stackPop
  let value ← stackPop
  chargeWithMemory GasCosts.OPCODE_MSTORE_BASE [(start_position, 32)]
  EvmM.modifyEvm (fun e =>
    { e with memory := memory_write e.memory start_position (toBeBytes32 value) })
  pcAdd 1

def iMstore8 : EvmM Unit := do
  let start_position ← stackPop
  let value ← stackPop
  chargeWithMemory GasCosts.OPCODE_MSTORE8_BASE [(start_position, 1)]
  EvmM.modifyEvm (fun e =>
    let m := memory_write e.memory start_position [BitVec.ofNat 8 (value &&& 0xFF)]
    { e with memory := m })
  pcAdd 1

def iMload : EvmM Unit := do
  let start_position ← stackPop
  chargeWithMemory GasCosts.OPCODE_MLOAD_BASE [(start_position, 32)]
  let value := bytesBEtoNat
    (memory_read_bytes (← EvmM.getEvm).memory start_position 32)
  stackPush value
  pcAdd 1

def iMsize : EvmM Unit := do
  charge_gas GasCosts.OPCODE_MSIZE
  stackPush (← EvmM.getEvm).memory.length
  pcAdd 1

def iMcopy : EvmM Unit := do
  let destination ← stackPop
  let source ← stackPop
  let length ← stackPop
  let words := ceil32 length / 32
  chargeWithMemory (GasCosts.OPCODE_MCOPY_BASE + GasCosts.OPCODE_COPY_PER_WORD * words)
    [(source, length), (destination, length)]
  EvmM.modifyEvm (fun e =>
    let m := memory_write e.memory destination (memory_read_bytes e.memory source length)
    { e with memory := m })
  pcAdd 1

/-! ## `stack.py` (instructions) -/

def iPop : EvmM Unit := do
  let _ ← stackPop
  charge_gas GasCosts.OPCODE_POP
  pcAdd 1

/-- `push_n(evm, num_bytes)` — PUSH0 (2 gas) through PUSH32. -/
def iPushN (num_bytes : Nat) : EvmM Unit := do
  charge_gas (if num_bytes == 0 then GasCosts.OPCODE_PUSH0 else GasCosts.OPCODE_PUSH)
  let e ← EvmM.getEvm
  stackPush (bytesBEtoNat (buffer_read e.code (e.pc + 1) num_bytes))
  pcAdd (1 + num_bytes)

/-- `dup_n(evm, item_number)` — `item_number` 0-indexed from the top. -/
def iDupN (item_number : Nat) : EvmM Unit := do
  charge_gas GasCosts.OPCODE_DUP
  let e ← EvmM.getEvm
  if item_number ≥ e.stack.length then throw .stackUnderflow
  stackPush (e.stack.getD item_number 0)
  pcAdd 1

private def listSwap (l : List U256) (i j : Nat) : List U256 :=
  let a := l.getD i 0
  let b := l.getD j 0
  (l.set i b).set j a

/-- `swap_n(evm, item_number)` — swap top with position `item_number`
    from the top (1-indexed distance). -/
def iSwapN (item_number : Nat) : EvmM Unit := do
  charge_gas GasCosts.OPCODE_SWAP
  let e ← EvmM.getEvm
  if item_number ≥ e.stack.length then throw .stackUnderflow
  EvmM.modifyEvm (fun e => { e with stack := listSwap e.stack 0 item_number })
  pcAdd 1

/-- `dupn(evm)` (EIP-663 DUPN): decoded immediate `n`, duplicates
    position `n` from the top (1-indexed). -/
def iDupn : EvmM Unit := do
  charge_gas GasCosts.OPCODE_DUPN
  let e ← EvmM.getEvm
  let imm := ((buffer_read e.code (e.pc + 1) 1).headD 0).toNat
  let item_number ← match decode_single imm with
    | .ok n => pure n
    | .error err => throw err
  if item_number > e.stack.length then throw .stackUnderflow
  stackPush (e.stack.getD (item_number - 1) 0)
  pcAdd 2

/-- `swapn(evm)`: swap top with position `n+1`. -/
def iSwapn : EvmM Unit := do
  charge_gas GasCosts.OPCODE_SWAPN
  let e ← EvmM.getEvm
  let imm := ((buffer_read e.code (e.pc + 1) 1).headD 0).toNat
  let item_number ← match decode_single imm with
    | .ok n => pure n
    | .error err => throw err
  if item_number + 1 > e.stack.length then throw .stackUnderflow
  EvmM.modifyEvm (fun e => { e with stack := listSwap e.stack 0 item_number })
  pcAdd 2

/-- `exchange(evm)`: swap positions `n+1` and `m+1`. -/
def iExchange : EvmM Unit := do
  charge_gas GasCosts.OPCODE_EXCHANGE
  let e ← EvmM.getEvm
  let imm := ((buffer_read e.code (e.pc + 1) 1).headD 0).toNat
  let (n, m) ← match decode_pair imm with
    | .ok nm => pure nm
    | .error err => throw err
  if max n m + 1 > e.stack.length then throw .stackUnderflow
  EvmM.modifyEvm (fun e => { e with stack := listSwap e.stack n m })
  pcAdd 2

/-! ## `log.py` -/

/-- `log_n(evm, num_topics)`. -/
def iLogN (num_topics : Nat) : EvmM Unit := do
  let memory_start_index ← stackPop
  let size ← stackPop
  let topics ← (List.range num_topics).mapM (fun _ => do
    pure (toBeBytes32 (← stackPop)))
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_start_index, size)]) <$> EvmM.getEvm
  charge_gas (GasCosts.OPCODE_LOG_BASE
    + GasCosts.OPCODE_LOG_DATA_PER_BYTE * size
    + GasCosts.OPCODE_LOG_TOPIC * num_topics + extend.cost)
  extendMemory extend.expandBy
  let e ← EvmM.getEvm
  if e.message.isStatic then throw .writeInStaticContext
  let log : Log :=
    { address := e.message.currentTarget
      topics := topics
      data := memory_read_bytes e.memory memory_start_index size }
  EvmM.modifyEvm (fun e => { e with logs := e.logs ++ [log] })
  pcAdd 1

/-! ## `storage.py` -/

/-- Warm/cold storage-key accounting shared by `sload`/`sstore`. -/
private def isWarmStorageKey (key : Address × Bytes32) : EvmM Bool := do
  pure ((← EvmM.getEvm).accessedStorageKeys.contains key)

private def warmStorageKey (key : Address × Bytes32) : EvmM Unit :=
  EvmM.modifyEvm (fun e =>
    { e with accessedStorageKeys := setAdd e.accessedStorageKeys key })

def iSload : EvmM Unit := do
  let key := toBeBytes32 (← stackPop)
  let target := (← EvmM.getEvm).message.currentTarget
  if ← isWarmStorageKey (target, key) then
    charge_gas GasCosts.WARM_ACCESS
  else
    warmStorageKey (target, key)
    charge_gas GasCosts.COLD_STORAGE_ACCESS
  stackPush (← EvmM.liftTx (getStorage target key))
  pcAdd 1

def iSstore : EvmM Unit := do
  if (← EvmM.getEvm).message.isStatic then throw .writeInStaticContext
  let key := toBeBytes32 (← stackPop)
  let new_value ← stackPop
  let target := (← EvmM.getEvm).message.currentTarget
  -- v0.6.0: the access cost is computed and checked BEFORE the state
  -- reads record the slot in the Block Access List — post-repricing the
  -- cold access cost can exceed the EIP-2200 stipend, so the stipend
  -- sentry alone is no longer sufficient.
  let cold := !(← isWarmStorageKey (target, key))
  let access_cost := if cold then GasCosts.COLD_STORAGE_ACCESS else GasCosts.WARM_ACCESS
  check_gas (max access_cost (GasCosts.CALL_STIPEND + 1))
  if cold then warmStorageKey (target, key)
  let original_value ← EvmM.liftTx (getStorageOriginal target key)
  let current_value ← EvmM.liftTx (getStorage target key)
  let gas_cost := access_cost
    + (if original_value == current_value && current_value != new_value then
         GasCosts.STORAGE_WRITE else 0)
  if current_value != new_value then
    if original_value != 0 && current_value != 0 && new_value == 0 then
      EvmM.modifyEvm (fun e =>
        { e with refundCounter := e.refundCounter + GasCosts.REFUND_STORAGE_CLEAR })
    if original_value != 0 && current_value == 0 then
      EvmM.modifyEvm (fun e =>
        { e with refundCounter := e.refundCounter - GasCosts.REFUND_STORAGE_CLEAR })
    if original_value == new_value then
      EvmM.modifyEvm (fun e =>
        { e with refundCounter := e.refundCounter + GasCosts.STORAGE_WRITE })
  let state_gas :=
    if original_value == current_value && current_value != new_value
        && original_value == 0 then
      StateGasCosts.STORAGE_SET
    else 0
  if current_value != new_value && original_value == new_value
      && original_value == 0 then
    credit_state_gas_refund StateGasCosts.STORAGE_SET
  charge_gas gas_cost
  charge_state_gas state_gas
  EvmM.liftTx (setStorage target key new_value)
  pcAdd 1

def iTload : EvmM Unit := do
  let key := toBeBytes32 (← stackPop)
  charge_gas GasCosts.OPCODE_TLOAD
  let target := (← EvmM.getEvm).message.currentTarget
  stackPush (← EvmM.liftTx (getTransientStorage target key))
  pcAdd 1

def iTstore : EvmM Unit := do
  if (← EvmM.getEvm).message.isStatic then throw .writeInStaticContext
  let key := toBeBytes32 (← stackPop)
  let new_value ← stackPop
  charge_gas GasCosts.OPCODE_TSTORE
  let target := (← EvmM.getEvm).message.currentTarget
  EvmM.liftTx (setTransientStorage target key new_value)
  pcAdd 1

end EvmAsm.Stateless.SpecRef
