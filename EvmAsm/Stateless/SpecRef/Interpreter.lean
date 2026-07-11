/-
  EvmAsm.Stateless.SpecRef.Interpreter

  Port of the interpreter core of
  `execution-specs/src/ethereum/forks/amsterdam/vm/`
  (`@tests-zkevm@v0.5.0`, `bd8c673`) — bead `evm-asm-s1d19.5`:

  * `vm/__init__.py`: `incorporate_child_on_error`,
    `incorporate_child_on_success`, `refill_frame_state_gas`,
    `emit_transfer_log` (functions of the same names)
  * `vm/eoa_delegation.py`: `get_delegated_code_address`,
    `recover_authority`, `calculate_delegation_cost`,
    `validate_authorization`, `set_delegation` (functions of the same
    names)
  * `vm/instructions/system.py`: `generic_create`, `create`, `create2`,
    `return_`, `generic_call`, `call`, `callcode`, `selfdestruct`,
    `delegatecall`, `staticcall`, `revert` (functions of the same
    names)
  * `vm/interpreter.py`: `MessageCallOutput`, `process_message_call`,
    `process_create_message`, `process_message`, `execute_code`
    (functions/classes of the same names) and the opcode dispatch of
    `vm/instructions/__init__.py` (`Ops`, `op_implementation`)
  * `utils/address.py`: `compute_contract_address`,
    `compute_create2_contract_address` (functions of the same names)

  ## Modeling notes

  * **Recursion → fuel.**  The Python call/create recursion
    (`execute_code → system ops → process_message → execute_code`) is
    bounded by the 1024 depth limit; every function in the mutual block
    threads `fuel`, decremented per child frame, and the callers supply
    `STACK_DEPTH_LIMIT + 8` — exhaustion is unreachable (checked-before-
    recursion depth limit) and rejects rather than mis-executing.  The
    `execute_code` step loop is separately fueled by
    `gas_left + code.length + 2`: every non-halting instruction charges
    ≥ 1 gas except forward-moving zero-cost ones (`STOP` halts), and
    each jump costs ≥ 8, so total steps are < gas + code length.
    Exhaustion (unreachable) is a rejection.
  * **Frames.**  A child frame swaps its own `Evm` into the `Machine`,
    runs, and the parent's `Evm` is swapped back with the mutated
    tracker kept — realizing the Python `parent_evm` suspension.  The
    frame-boundary `try/except` becomes `tryCatch`: an `EvmError` from
    the child body carries the machine state; `process_message` folds
    it into `evm.error` exactly as Python does.
  * **Precompiles** are supplied as a parameter (`PrecompileMap`) so
    the interpreter is reviewable before the precompile stage lands;
    `process_message` dispatches on membership exactly like
    `PRE_COMPILED_CONTRACTS`.
-/

import EvmAsm.Stateless.SpecRef.InstructionsEnv
import EvmAsm.Stateless.SpecRef.SeamShell
import EvmAsm.Stateless.SpecRef.Runtime

namespace EvmAsm.Stateless.SpecRef

def STACK_DEPTH_LIMIT : Uint := 1024

namespace GasCosts
def OPCODE_SELFDESTRUCT_BASE : Uint := 5000
end GasCosts

-- `partial def`s below need inhabited result types.
instance : Inhabited SpecError := ⟨.headerDecodeError⟩
instance : Inhabited (EvmM α) := ⟨fun _ => .error default⟩

/-- The precompile dispatch table, supplied by the precompile stage:
    `(address, implementation)` pairs (`PRE_COMPILED_CONTRACTS`). -/
abbrev PrecompileMap := List (Address × EvmM Unit)

/-! ## `utils/address.py` -/

/-- `compute_contract_address(address, nonce)`. -/
def compute_contract_address (address : Address) (nonce : Uint) : Address :=
  (keccak256 (EvmAsm.EL.RLP.encode (.list
    [.bytes address, .bytes (EvmAsm.EL.RLP.Nat.toBytesBE nonce)]))).drop 12

/-- `compute_create2_contract_address(address, salt, call_data)`. -/
def compute_create2_contract_address (address : Address) (salt : Bytes)
    (call_data : Bytes) : Address :=
  (keccak256 ([0xFF] ++ address ++ salt ++ keccak256 call_data)).drop 12

/-! ## `vm/__init__.py` child incorporation -/

/-- `refill_frame_state_gas(evm)`: LIFO state-gas rollback on frame
    failure. v0.6.0: the reservoir is restored from the frame baseline
    (`message.state_gas_reservoir`) instead of replaying the deleted
    running counter. -/
def refill_frame_state_gas : EvmM Unit :=
  EvmM.modifyEvm (fun e =>
    { e with gasLeft := e.gasLeft + e.stateGasSpilled
             stateGasLeft := e.message.stateGasReservoir
             stateGasSpilled := 0 })

/-- `incorporate_child_on_error(evm, child_evm)`. -/
def incorporate_child_on_error (child : Evm) : EvmM Unit :=
  EvmM.modifyEvm (fun e =>
    { e with gasLeft := e.gasLeft + child.gasLeft
             stateGasLeft := e.stateGasLeft + child.stateGasLeft
             regularGasUsed := e.regularGasUsed + child.regularGasUsed })

/-- `incorporate_child_on_success(evm, child_evm)`. -/
def incorporate_child_on_success (child : Evm) : EvmM Unit :=
  EvmM.modifyEvm (fun e =>
    { e with gasLeft := e.gasLeft + child.gasLeft
             stateGasLeft := e.stateGasLeft + child.stateGasLeft
             stateGasSpilled := e.stateGasSpilled + child.stateGasSpilled
             logs := e.logs ++ child.logs
             refundCounter := e.refundCounter + child.refundCounter
             accountsToDelete := setUnion e.accountsToDelete child.accountsToDelete
             accessedAddresses := setUnion e.accessedAddresses child.accessedAddresses
             accessedStorageKeys := setUnion e.accessedStorageKeys child.accessedStorageKeys
             regularGasUsed := e.regularGasUsed + child.regularGasUsed })

/-- `emit_transfer_log(evm, sender, recipient, transfer_amount)`
    (EIP-7708). -/
def emit_transfer_log (sender recipient : Address) (transfer_amount : U256) :
    EvmM Unit := do
  if transfer_amount == 0 then return
  let log : Log :=
    { address := VM_SYSTEM_ADDRESS
      topics := [TRANSFER_TOPIC,
                 List.replicate 12 0x00 ++ sender,
                 List.replicate 12 0x00 ++ recipient]
      data := toBeBytes32 transfer_amount }
  EvmM.modifyEvm (fun e => { e with logs := e.logs ++ [log] })

/-! ## `vm/eoa_delegation.py` -/

def SET_CODE_TX_MAGIC : Bytes := [0x05]
def NULL_ADDRESS : Address := List.replicate 20 0x00

/-- `get_delegated_code_address(code)`. -/
def get_delegated_code_address (code : Bytes) : Option Address :=
  if is_valid_delegation code then some (code.drop 3) else none

/-- `recover_authority(authorization)` — `InvalidSignatureError`s are
    handled by the caller (`validate_authorization` returns `none`). -/
def recover_authority (auth : Authorization) : Option Address := do
  if auth.yParity ≠ 0 && auth.yParity ≠ 1 then none
  else if auth.r == 0 || auth.r ≥ SECP256K1N then none
  else if auth.s == 0 || auth.s > SECP256K1N / 2 then none
  else
    let signing_hash := keccak256 (SET_CODE_TX_MAGIC
      ++ EvmAsm.EL.RLP.encode (.list
        [.bytes (EvmAsm.EL.RLP.Nat.toBytesBE auth.chainId),
         .bytes auth.address,
         .bytes (EvmAsm.EL.RLP.Nat.toBytesBE auth.nonce)]))
    match Secp256k1.recover (bytesBEtoNat signing_hash) auth.r auth.s auth.yParity with
    | .ok (x, y) =>
        some ((keccak256 (natToBytesBE 32 x ++ natToBytesBE 32 y)).drop 12)
    | .error _ => none

/-- `calculate_delegation_cost(evm, address)`:
    `(is_delegated, code_address, delegation_gas_cost)`. -/
def calculate_delegation_cost (address : Address) :
    EvmM (Bool × Address × Uint) := do
  let code ← extCodeOf address
  if !is_valid_delegation code then
    pure (false, address, 0)
  else
    let delegated_address := code.drop 3
    let warm := (← EvmM.getEvm).accessedAddresses.contains delegated_address
    pure (true, delegated_address,
      if warm then GasCosts.WARM_ACCESS else GasCosts.COLD_ACCOUNT_ACCESS)

/-- `validate_authorization(message, auth)`, split so the recovered
    authority can be recorded on the FRAME's accessed set even when
    the later checks skip the authorization (the Python mutates
    `message.accessed_addresses` — the same set object as
    `evm.accessed_addresses` — right after recovery; `set_delegation`
    below mutates the live frame). v0.6.0 returns just the authority. -/
def validate_authorization_checks (auth : Authorization) (authority : Address) :
    EvmM (Option Address) := do
  let authority_account ← EvmM.liftTx (getAccount authority)
  let authority_code ← EvmM.liftTx (getCode authority_account.codeHash authority)
  if !authority_code.isEmpty && !is_valid_delegation authority_code then
    return none
  if authority_account.nonce ≠ auth.nonce then return none
  return some authority

/-- `set_delegation(evm)` (`vm/eoa_delegation.py:206`, v0.6.0): apply the
    EIP-7702 authorizations and charge their state-dependent costs at the
    top frame — the v0.5.0 worst-case-intrinsic + refund machinery is
    replaced by exact charges:

    - `NEW_ACCOUNT` (state) when the authority's leaf does not exist;
    - `ACCOUNT_WRITE` (regular) on the transaction's first write to the
      authority (sender written at inclusion; recipient when value > 0;
      each authority at most once);
    - `AUTH_BASE` (state) when a net-new delegation indicator is written
      (not delegated pre-tx, none set earlier in this tx, and this auth
      sets one); at most once per authority, never credited back.

    OOG throws `.outOfGas`; the caller (`process_message` depth-0 prep)
    rolls back the applied authorizations and halts the frame. -/
def set_delegation : EvmM Unit := do
  let msg := (← EvmM.getEvm).message
  -- Accounts this transaction has already written: the sender's leaf at
  -- inclusion (nonce bump, fee deduction); the recipient when value is
  -- transferred.
  let mut written_accounts : List Address := setAdd [] msg.txEnv.origin
  if msg.txEnv.value > 0 then
    written_accounts := setAdd written_accounts msg.currentTarget
  -- Authorities a delegation was set for earlier in this transaction.
  let mut delegation_set_for : List Address := []
  for auth in msg.txEnv.authorizations do
    let validated ← do
      if auth.chainId ≠ msg.blockEnv.chainId && auth.chainId ≠ 0 then
        pure none
      else if auth.nonce ≥ 2^64 - 1 then
        pure none
      else match recover_authority auth with
        | none => pure none
        | some authority => do
            EvmM.modifyEvm (fun e =>
              { e with accessedAddresses := setAdd e.accessedAddresses authority })
            validate_authorization_checks auth authority
    match validated with
    | none => pure ()
    | some authority =>
        if !(← EvmM.liftTx (accountExists authority)) then
          charge_state_gas StateGasCosts.NEW_ACCOUNT
        if !written_accounts.contains authority then
          charge_gas GasCosts.ACCOUNT_WRITE
          written_accounts := setAdd written_accounts authority
        let pre_account ← EvmM.liftTx (get_pre_state_account authority)
        let pre_code ← EvmM.liftTx (getCode pre_account.codeHash authority)
        let delegated_before_tx := is_valid_delegation pre_code
        let code_to_set ←
          if auth.address == NULL_ADDRESS then
            pure ([] : Bytes)
          else do
            if !delegated_before_tx && !delegation_set_for.contains authority then
              charge_state_gas StateGasCosts.AUTH_BASE
            delegation_set_for := setAdd delegation_set_for authority
            pure ([0xEF, 0x01, 0x00] ++ auth.address)
        EvmM.liftTx (setCode authority code_to_set)
        EvmM.liftTx (incrementNonce authority)

/-! ## `MessageCallOutput` (`vm/interpreter.py`) -/

structure MessageCallOutput where
  gasLeft : Uint
  refundCounter : U256
  logs : List Log
  accountsToDelete : List Address
  error : Option EvmError
  returnData : Bytes
  stateGasLeft : Uint
  regularGasUsed : Uint
  stateGasUsed : Int
  deriving Repr

/-! ## Non-recursive system instructions -/

/-- `return_(evm)`. -/
def iReturn : EvmM Unit := do
  let memory_start_position ← stackPop
  let memory_size ← stackPop
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_start_position, memory_size)]) <$> EvmM.getEvm
  charge_gas (GasCosts.ZERO + extend.cost)
  extendMemory extend.expandBy
  EvmM.modifyEvm (fun e =>
    { e with output := memory_read_bytes e.memory memory_start_position memory_size
             running := false })

/-- `revert(evm)`. -/
def iRevert : EvmM Unit := do
  let memory_start_index ← stackPop
  let size ← stackPop
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_start_index, size)]) <$> EvmM.getEvm
  charge_gas extend.cost
  extendMemory extend.expandBy
  EvmM.modifyEvm (fun e =>
    { e with output := memory_read_bytes e.memory memory_start_index size })
  throw .revert

/-- `selfdestruct(evm)` (EIP-6780 + EIP-7708 + EIP-8038). -/
def iSelfdestruct : EvmM Unit := do
  if (← EvmM.getEvm).message.isStatic then throw .writeInStaticContext
  let beneficiary := to_address_masked (← stackPop)
  let is_cold := !(← EvmM.getEvm).accessedAddresses.contains beneficiary
  let gas_cost := GasCosts.OPCODE_SELFDESTRUCT_BASE
    + (if is_cold then GasCosts.COLD_ACCOUNT_ACCESS else 0)
  check_gas gas_cost
  if is_cold then
    EvmM.modifyEvm (fun e =>
      { e with accessedAddresses := setAdd e.accessedAddresses beneficiary })
  let originator := (← EvmM.getEvm).message.currentTarget
  let beneficiary_dead := !(← EvmM.liftTx (isAccountAlive beneficiary))
  let originator_has_balance := (← EvmM.liftTx (getAccount originator)).balance ≠ 0
  let (state_gas, account_write_gas) :=
    if beneficiary_dead && originator_has_balance then
      (StateGasCosts.NEW_ACCOUNT, GasCosts.ACCOUNT_WRITE)
    else (0, 0)
  charge_gas (gas_cost + account_write_gas)
  charge_state_gas state_gas
  let originator_balance := (← EvmM.liftTx (getAccount originator)).balance
  EvmM.liftTx (moveEther originator beneficiary originator_balance)
  if beneficiary != originator then
    emit_transfer_log originator beneficiary originator_balance
  if (← get).txState.createdAccounts.contains originator then
    EvmM.modifyEvm (fun e =>
      { e with accountsToDelete := setAdd e.accountsToDelete originator })
  EvmM.modifyEvm (fun e => { e with running := false })

/-! ## The mutual interpreter block

Every function threads `fuel` (frame depth; see the header). -/

mutual

/-- One step of `execute_code`'s `while` loop: dispatch on
    `code[pc]` (`Ops` + `op_implementation`).  `InvalidOpcode` is the
    Python `ValueError` on an unlisted byte. -/
partial def opImplementation (pre : PrecompileMap) (fuel : Nat) (op : Nat) :
    EvmM Unit :=
  match op with
  | 0x00 => iStop
  | 0x01 => iAdd | 0x02 => iMul | 0x03 => iSub | 0x04 => iDiv
  | 0x05 => iSdiv | 0x06 => iMod | 0x07 => iSmod | 0x08 => iAddmod
  | 0x09 => iMulmod | 0x0A => iExp | 0x0B => iSignextend
  | 0x10 => iLt | 0x11 => iGt | 0x12 => iSlt | 0x13 => iSgt
  | 0x14 => iEq | 0x15 => iIszero
  | 0x16 => iAnd | 0x17 => iOr | 0x18 => iXor | 0x19 => iNot
  | 0x1A => iByte | 0x1B => iShl | 0x1C => iShr | 0x1D => iSar | 0x1E => iClz
  | 0x20 => iKeccak
  | 0x30 => iAddress | 0x31 => iBalance | 0x32 => iOrigin | 0x33 => iCaller
  | 0x34 => iCallvalue | 0x35 => iCalldataload | 0x36 => iCalldatasize
  | 0x37 => iCalldatacopy | 0x38 => iCodesize | 0x39 => iCodecopy
  | 0x3A => iGasprice | 0x3B => iExtcodesize | 0x3C => iExtcodecopy
  | 0x3D => iReturndatasize | 0x3E => iReturndatacopy | 0x3F => iExtcodehash
  | 0x40 => iBlockhash | 0x41 => iCoinbase | 0x42 => iTimestamp
  | 0x43 => iNumber | 0x44 => iPrevrandao | 0x45 => iGaslimit
  | 0x46 => iChainid | 0x47 => iSelfbalance | 0x48 => iBasefee
  | 0x49 => iBlobhash | 0x4A => iBlobbasefee | 0x4B => iSlotnum
  | 0x50 => iPop | 0x51 => iMload | 0x52 => iMstore | 0x53 => iMstore8
  | 0x54 => iSload | 0x55 => iSstore | 0x56 => iJump | 0x57 => iJumpi
  | 0x58 => iPc | 0x59 => iMsize | 0x5A => iGas | 0x5B => iJumpdest
  | 0x5C => iTload | 0x5D => iTstore | 0x5E => iMcopy
  | 0xE6 => iDupn | 0xE7 => iSwapn | 0xE8 => iExchange
  | 0xA0 => iLogN 0 | 0xA1 => iLogN 1 | 0xA2 => iLogN 2
  | 0xA3 => iLogN 3 | 0xA4 => iLogN 4
  | 0xF0 => iCreate pre fuel
  | 0xF1 => iCall pre fuel
  | 0xF2 => iCallcode pre fuel
  | 0xF3 => iReturn
  | 0xF4 => iDelegatecall pre fuel
  | 0xF5 => iCreate2 pre fuel
  | 0xFA => iStaticcall pre fuel
  | 0xFD => iRevert
  | 0xFF => iSelfdestruct
  | op =>
      if 0x5F ≤ op && op ≤ 0x7F then iPushN (op - 0x5F)
      else if 0x80 ≤ op && op ≤ 0x8F then iDupN (op - 0x80)
      else if 0x90 ≤ op && op ≤ 0x9F then iSwapN (op - 0x8F)
      else throw (.invalidOpcode op)

/-- The `while evm.running and evm.pc < len(code)` loop of
    `execute_code`, fueled by `gas + code length` (see the header). -/
partial def executeLoop (pre : PrecompileMap) (fuel : Nat) : EvmM Unit := do
  let e ← EvmM.getEvm
  if e.running && e.pc < e.code.length then
    opImplementation pre fuel (e.code.getD e.pc 0).toNat
    executeLoop pre fuel

/-- The body `process_message` runs inside its `try` (top-frame
    EIP-2780 charges, value transfer, precompile dispatch or the
    opcode loop). -/
partial def executeBody (pre : PrecompileMap) (fuel : Nat) : EvmM Unit := do
  -- Read the LIVE frame message: at depth 0 `prepare_dispatch` has
  -- rewritten code/codeAddress/disablePrecompiles after frame
  -- construction (v0.6.0 moved the top-frame charges + delegation
  -- resolution out of this body into the prep phase).
  let msg := (← EvmM.getEvm).message
  if msg.shouldTransferValue && msg.value ≠ 0 then
    EvmM.liftTx (moveEther msg.caller msg.currentTarget msg.value)
    if msg.caller != msg.currentTarget then
      emit_transfer_log msg.caller msg.currentTarget msg.value
  match msg.codeAddress.bind (fun a => (pre.find? (·.1 == a)).map (·.2)) with
  | some impl =>
      if !msg.disablePrecompiles then impl
  | none => executeLoop pre fuel

/-- `prepare_dispatch(evm)` (`vm/interpreter.py:246`, v0.6.0): charge the
    state-dependent dispatch costs and resolve the code the top frame
    will run. Runs at depth 0 after `set_delegation`, before dispatch;
    must not mutate the transaction state:

    - create tx: `NEW_ACCOUNT` (state) iff the target's pre-state leaf is
      `EMPTY_ACCOUNT`;
    - call tx: `NEW_ACCOUNT` (state) iff value > 0 and the recipient is
      not alive; resolve an EIP-7702 delegation on the recipient's code,
      charging `WARM_ACCESS` or `COLD_ACCOUNT_ACCESS` by accessed-set
      membership, and point the frame at the delegated code. -/
partial def prepare_dispatch : EvmM Unit := do
  let msg := (← EvmM.getEvm).message
  if msg.target == none then
    if (← EvmM.liftTx (get_pre_state_account msg.currentTarget)) == EMPTY_ACCOUNT then
      charge_state_gas StateGasCosts.NEW_ACCOUNT
  else
    let recipient := msg.currentTarget
    if msg.value > 0 && !(← EvmM.liftTx (isAccountAlive recipient)) then
      charge_state_gas StateGasCosts.NEW_ACCOUNT
    let recipient_code ← extCodeOf recipient
    let code ←
      match get_delegated_code_address recipient_code with
      | some delegated_address => do
          if (← EvmM.getEvm).accessedAddresses.contains delegated_address then
            charge_gas GasCosts.WARM_ACCESS
          else
            charge_gas GasCosts.COLD_ACCOUNT_ACCESS
            EvmM.modifyEvm (fun e =>
              { e with accessedAddresses := setAdd e.accessedAddresses delegated_address })
          let code ← extCodeOf delegated_address
          EvmM.modifyEvm (fun e =>
            { e with message := { e.message with
                                    disablePrecompiles := true
                                    codeAddress := some delegated_address } })
          pure code
      | none => pure recipient_code
    EvmM.modifyEvm (fun e =>
      { e with message := { e.message with code := code }
               code := code
               validJumpDestinations := validJumpDestinations code })

/-- `process_message(message)`: build the frame, run the body, fold
    halts/reverts into `evm.error`, roll back the tracker on error.
    v0.6.0: at depth 0, `set_delegation` + `prepare_dispatch` run first
    under their own snapshot — an `ExceptionalHalt` there rolls back the
    whole preparation (including applied authorizations), consumes all
    gas, and returns the errored frame without dispatching. -/
partial def process_message (pre : PrecompileMap) (fuel : Nat) (msg : Message) :
    EvmM Evm := do
  match fuel with
  | 0 => EvmM.liftSpec (throw (.executionRejected "interpreter fuel exhausted"))
  | fuel + 1 =>
  if msg.depth > STACK_DEPTH_LIMIT then throw .stackDepthLimit
  let parent := (← get).evm
  let childEvm : Evm :=
    { code := msg.code
      gasLeft := msg.gas
      stateGasLeft := msg.stateGasReservoir
      validJumpDestinations := validJumpDestinations msg.code
      message := msg
      accessedAddresses := msg.accessedAddresses
      accessedStorageKeys := msg.accessedStorageKeys }
  modify (fun s => { s with evm := childEvm })
  if msg.depth == 0 then
    let prep_snapshot ← EvmM.liftTx copyTxState
    let prep_reservoir := msg.stateGasReservoir
    let prep_ok ← tryCatch (do
        if !msg.txEnv.authorizations.isEmpty then
          set_delegation
          -- Fold the auth state-gas use into the frame baseline: record
          -- it, reset the reservoir baseline to what is left, clear the
          -- spill.
          let used := frame_state_gas_used (← EvmM.getEvm)
          EvmM.modifyEvm (fun e =>
            { e with authStateGasUsed := used
                     message := { e.message with stateGasReservoir := e.stateGasLeft }
                     stateGasSpilled := 0 })
        prepare_dispatch
        pure true)
      (fun err => do
        if !err.isHalt then throw err
        EvmM.liftTx (restoreTxState prep_snapshot)
        -- The rollback reverts any applied delegations, so the baseline
        -- fold above is undone with it and every state charge refilled.
        EvmM.modifyEvm (fun e =>
          { e with message := { e.message with stateGasReservoir := prep_reservoir }
                   authStateGasUsed := 0 })
        refill_frame_state_gas
        EvmM.modifyEvm (fun e =>
          { e with regularGasUsed := e.regularGasUsed + e.gasLeft
                   gasLeft := 0
                   error := some err })
        pure false)
    if !prep_ok then
      let result := (← get).evm
      modify (fun s => { s with evm := parent })
      return result
  let snapshot ← EvmM.liftTx copyTxState
  -- The Python try/except at the frame boundary.
  tryCatch (executeBody pre fuel)
    (fun err => do
      refill_frame_state_gas
      if err.isHalt then
        EvmM.modifyEvm (fun e =>
          { e with regularGasUsed := e.regularGasUsed + e.gasLeft
                   gasLeft := 0
                   output := []
                   error := some err })
      else
        EvmM.modifyEvm (fun e => { e with error := some err }))
  let result := (← get).evm
  if result.error.isSome then
    EvmM.liftTx (restoreTxState snapshot)
  modify (fun s => { s with evm := parent })
  pure result

/-- `process_create_message(message)`. -/
partial def process_create_message (pre : PrecompileMap) (fuel : Nat)
    (msg : Message) : EvmM Evm := do
  let snapshot ← EvmM.liftTx copyTxState
  EvmM.liftTx (destroyStorage msg.currentTarget)
  EvmM.liftTx (markAccountCreated msg.currentTarget)
  EvmM.liftTx (incrementNonce msg.currentTarget)
  let child ← process_message pre fuel msg
  if child.error.isNone then
    -- Post-processing runs in the CHILD's frame registers.
    let parent := (← get).evm
    modify (fun s => { s with evm := child })
    let contract_code := child.output
    tryCatch (do
        if contract_code.length > 0 then
          if contract_code.headD 0 == 0xEF then throw .invalidContractPrefix
        if contract_code.length > MAX_CODE_SIZE then throw .outOfGas
        charge_gas (GasCosts.OPCODE_KECCAK256_PER_WORD
          * ceil32 contract_code.length / 32)
        charge_state_gas (contract_code.length * StateGasCosts.COST_PER_STATE_BYTE)
        EvmM.liftTx (setCode msg.currentTarget contract_code))
      (fun err => do
        EvmM.liftTx (restoreTxState snapshot)
        refill_frame_state_gas
        EvmM.modifyEvm (fun e =>
          { e with regularGasUsed := e.regularGasUsed + e.gasLeft
                   gasLeft := 0
                   output := []
                   error := some err }))
    let result := (← get).evm
    modify (fun s => { s with evm := parent })
    pure result
  else do
    EvmM.liftTx (restoreTxState snapshot)
    pure child

/-- `generic_create(evm, endowment, contract_address, …)`. -/
partial def generic_create (pre : PrecompileMap) (fuel : Nat)
    (endowment : U256) (contract_address : Address)
    (memory_start_position memory_size : U256) : EvmM Unit := do
  if memory_size > MAX_INIT_CODE_SIZE then throw .outOfGas
  let e ← EvmM.getEvm
  let call_data := memory_read_bytes e.memory memory_start_position memory_size
  EvmM.modifyEvm (fun e => { e with returnData := [] })
  let sender_address := e.message.currentTarget
  let sender ← EvmM.liftTx (getAccount sender_address)
  -- v0.6.0: the balance/nonce/depth early-out touches no gas pools (the
  -- gas split and state-gas charge now happen after it).
  if sender.balance < endowment || sender.nonce == 2^64 - 1
      || e.message.depth + 1 > STACK_DEPTH_LIMIT then
    stackPush 0
    return
  EvmM.modifyEvm (fun e =>
    { e with accessedAddresses := setAdd e.accessedAddresses contract_address })
  -- v0.6.0: NEW_ACCOUNT is charged iff the target does not exist —
  -- decided by existence alone, independently of the collision outcome.
  let new_account_charged := !(← EvmM.liftTx (isAccountAlive contract_address))
  if new_account_charged then
    charge_state_gas StateGasCosts.NEW_ACCOUNT
  let create_message_gas := max_message_call_gas (← EvmM.getEvm).gasLeft
  EvmM.modifyEvm (fun e => { e with gasLeft := e.gasLeft - create_message_gas })
  if !(← EvmM.liftTx (accountDeployable contract_address)) then
    EvmM.liftTx (incrementNonce sender_address)
    EvmM.modifyEvm (fun e =>
      { e with regularGasUsed := e.regularGasUsed + create_message_gas })
    -- A storage-only collision target is non-existent: charged above,
    -- refilled here.
    if new_account_charged then
      credit_state_gas_refund StateGasCosts.NEW_ACCOUNT
    stackPush 0
    return
  -- Move full reservoir to child (no 63/64 rule for state gas).
  let reservoir := (← EvmM.getEvm).stateGasLeft
  EvmM.modifyEvm (fun e => { e with stateGasLeft := 0 })
  EvmM.liftTx (incrementNonce sender_address)
  let parentEvm ← EvmM.getEvm
  let child_message : Message :=
    { blockEnv := e.message.blockEnv
      txEnv := e.message.txEnv
      caller := e.message.currentTarget
      target := none
      gas := create_message_gas
      stateGasReservoir := reservoir
      value := endowment
      data := []
      code := call_data
      currentTarget := contract_address
      depth := e.message.depth + 1
      codeAddress := none
      shouldTransferValue := true
      isStatic := false
      accessedAddresses := parentEvm.accessedAddresses
      accessedStorageKeys := parentEvm.accessedStorageKeys
      disablePrecompiles := false }
  let child ← process_create_message pre fuel child_message
  if child.error.isSome then
    incorporate_child_on_error child
    if new_account_charged then
      credit_state_gas_refund StateGasCosts.NEW_ACCOUNT
    EvmM.modifyEvm (fun e => { e with returnData := child.output })
    stackPush 0
  else
    incorporate_child_on_success child
    EvmM.modifyEvm (fun e => { e with returnData := [] })
    stackPush (bytesBEtoNat child.message.currentTarget)

/-- `create(evm)`. -/
partial def iCreate (pre : PrecompileMap) (fuel : Nat) : EvmM Unit := do
  if (← EvmM.getEvm).message.isStatic then throw .writeInStaticContext
  let endowment ← stackPop
  let memory_start_position ← stackPop
  let memory_size ← stackPop
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_start_position, memory_size)]) <$> EvmM.getEvm
  charge_gas (GasCosts.CREATE_ACCESS + extend.cost + init_code_cost memory_size)
  extendMemory extend.expandBy
  let e ← EvmM.getEvm
  let nonce := (← EvmM.liftTx (getAccount e.message.currentTarget)).nonce
  let contract_address := compute_contract_address e.message.currentTarget nonce
  generic_create pre fuel endowment contract_address memory_start_position memory_size
  EvmM.modifyEvm (fun e => { e with pc := e.pc + 1 })

/-- `create2(evm)`. -/
partial def iCreate2 (pre : PrecompileMap) (fuel : Nat) : EvmM Unit := do
  if (← EvmM.getEvm).message.isStatic then throw .writeInStaticContext
  let endowment ← stackPop
  let memory_start_position ← stackPop
  let memory_size ← stackPop
  let salt := toBeBytes32 (← stackPop)
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_start_position, memory_size)]) <$> EvmM.getEvm
  let call_data_words := ceil32 memory_size / 32
  charge_gas (GasCosts.CREATE_ACCESS
    + GasCosts.OPCODE_KECCAK256_PER_WORD * call_data_words
    + extend.cost + init_code_cost memory_size)
  extendMemory extend.expandBy
  let e ← EvmM.getEvm
  let contract_address := compute_create2_contract_address e.message.currentTarget
    salt (memory_read_bytes e.memory memory_start_position memory_size)
  generic_create pre fuel endowment contract_address memory_start_position memory_size
  EvmM.modifyEvm (fun e => { e with pc := e.pc + 1 })

/-- `generic_call(evm, params)`. -/
partial def generic_call (pre : PrecompileMap) (fuel : Nat)
    (gas state_gas_reservoir : Uint) (value : U256) (caller to code_address : Address)
    (should_transfer_value is_staticcall : Bool)
    (memory_input_start_position memory_input_size
     memory_output_start_position memory_output_size : U256)
    (code : Bytes) (disable_precompiles : Bool)
    (new_account_charged : Bool := false) : EvmM Unit := do
  EvmM.modifyEvm (fun e => { e with returnData := [] })
  let e ← EvmM.getEvm
  if e.message.depth + 1 > STACK_DEPTH_LIMIT then
    EvmM.modifyEvm (fun e =>
      { e with gasLeft := e.gasLeft + gas
               stateGasLeft := e.stateGasLeft + state_gas_reservoir })
    if new_account_charged then
      credit_state_gas_refund StateGasCosts.NEW_ACCOUNT
    stackPush 0
    return
  let call_data := memory_read_bytes e.memory
    memory_input_start_position memory_input_size
  let child_message : Message :=
    { blockEnv := e.message.blockEnv
      txEnv := e.message.txEnv
      caller := caller
      target := some to
      gas := gas
      stateGasReservoir := state_gas_reservoir
      value := value
      data := call_data
      code := code
      currentTarget := to
      depth := e.message.depth + 1
      codeAddress := some code_address
      shouldTransferValue := should_transfer_value
      isStatic := is_staticcall || e.message.isStatic
      accessedAddresses := e.accessedAddresses
      accessedStorageKeys := e.accessedStorageKeys
      disablePrecompiles := disable_precompiles }
  let child ← process_message pre fuel child_message
  if child.error.isSome then
    incorporate_child_on_error child
    if new_account_charged then
      credit_state_gas_refund StateGasCosts.NEW_ACCOUNT
    EvmM.modifyEvm (fun e => { e with returnData := child.output })
    stackPush 0
  else
    incorporate_child_on_success child
    EvmM.modifyEvm (fun e => { e with returnData := child.output })
    stackPush CALL_SUCCESS
  let actual_output_size := min memory_output_size child.output.length
  EvmM.modifyEvm (fun e =>
    let m := memory_write e.memory memory_output_start_position
      (child.output.take actual_output_size)
    { e with memory := m })

/-- `call(evm)`. -/
partial def iCall (pre : PrecompileMap) (fuel : Nat) : EvmM Unit := do
  let gas ← stackPop
  let to := to_address_masked (← stackPop)
  let value ← stackPop
  let memory_input_start_position ← stackPop
  let memory_input_size ← stackPop
  let memory_output_start_position ← stackPop
  let memory_output_size ← stackPop
  if (← EvmM.getEvm).message.isStatic && value ≠ 0 then
    throw .writeInStaticContext
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_input_start_position, memory_input_size),
     (memory_output_start_position, memory_output_size)]) <$> EvmM.getEvm
  let is_cold := !(← EvmM.getEvm).accessedAddresses.contains to
  let access_gas_cost := if is_cold then GasCosts.COLD_ACCOUNT_ACCESS
    else GasCosts.WARM_ACCESS
  let transfer_gas_cost := if value == 0 then 0 else GasCosts.CALL_VALUE
  check_gas (access_gas_cost + transfer_gas_cost + extend.cost)
  if is_cold then
    EvmM.modifyEvm (fun e =>
      { e with accessedAddresses := setAdd e.accessedAddresses to })
  let mut extra_gas := access_gas_cost + transfer_gas_cost
  let (is_delegated, code_address, delegation_cost) ← calculate_delegation_cost to
  if is_delegated then
    extra_gas := extra_gas + delegation_cost
    check_gas (extra_gas + extend.cost)
    EvmM.modifyEvm (fun e =>
      { e with accessedAddresses := setAdd e.accessedAddresses code_address })
  let code ← extCodeOf code_address
  charge_gas (extra_gas + extend.cost)
  let new_account_charged := value ≠ 0
    && !(← EvmM.liftTx (isAccountAlive to))
  if new_account_charged then
    charge_state_gas StateGasCosts.NEW_ACCOUNT
  let message_call_gas := calculate_message_call_gas value gas
    (← EvmM.getEvm).gasLeft 0 0
  charge_gas message_call_gas.cost
  EvmM.modifyEvm (fun e =>
    { e with regularGasUsed := e.regularGasUsed - message_call_gas.subCall })
  extendMemory extend.expandBy
  let reservoir := (← EvmM.getEvm).stateGasLeft
  EvmM.modifyEvm (fun e => { e with stateGasLeft := 0 })
  let sender_balance := (← EvmM.liftTx
    (getAccount (← EvmM.getEvm).message.currentTarget)).balance
  if sender_balance < value then
    stackPush 0
    EvmM.modifyEvm (fun e =>
      { e with returnData := []
               gasLeft := e.gasLeft + message_call_gas.subCall
               stateGasLeft := e.stateGasLeft + reservoir })
    if new_account_charged then
      credit_state_gas_refund StateGasCosts.NEW_ACCOUNT
  else
    generic_call pre fuel message_call_gas.subCall reservoir value
      (← EvmM.getEvm).message.currentTarget to code_address true false
      memory_input_start_position memory_input_size
      memory_output_start_position memory_output_size code is_delegated
      new_account_charged
  EvmM.modifyEvm (fun e => { e with pc := e.pc + 1 })

/-- `callcode(evm)`. -/
partial def iCallcode (pre : PrecompileMap) (fuel : Nat) : EvmM Unit := do
  let gas ← stackPop
  let code_address0 := to_address_masked (← stackPop)
  let value ← stackPop
  let memory_input_start_position ← stackPop
  let memory_input_size ← stackPop
  let memory_output_start_position ← stackPop
  let memory_output_size ← stackPop
  let to := (← EvmM.getEvm).message.currentTarget
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_input_start_position, memory_input_size),
     (memory_output_start_position, memory_output_size)]) <$> EvmM.getEvm
  let is_cold := !(← EvmM.getEvm).accessedAddresses.contains code_address0
  let access_gas_cost := if is_cold then GasCosts.COLD_ACCOUNT_ACCESS
    else GasCosts.WARM_ACCESS
  let transfer_gas_cost := if value == 0 then 0 else GasCosts.CALL_VALUE
  check_gas (access_gas_cost + extend.cost + transfer_gas_cost)
  if is_cold then
    EvmM.modifyEvm (fun e =>
      { e with accessedAddresses := setAdd e.accessedAddresses code_address0 })
  let mut extra_gas := access_gas_cost + transfer_gas_cost
  let (is_delegated, code_address, delegation_cost) ←
    calculate_delegation_cost code_address0
  if is_delegated then
    extra_gas := extra_gas + delegation_cost
    check_gas (extra_gas + extend.cost)
    EvmM.modifyEvm (fun e =>
      { e with accessedAddresses := setAdd e.accessedAddresses code_address })
  let code ← extCodeOf code_address
  let message_call_gas := calculate_message_call_gas value gas
    (← EvmM.getEvm).gasLeft extend.cost extra_gas
  charge_gas (message_call_gas.cost + extend.cost)
  EvmM.modifyEvm (fun e =>
    { e with regularGasUsed := e.regularGasUsed - message_call_gas.subCall })
  extendMemory extend.expandBy
  let reservoir := (← EvmM.getEvm).stateGasLeft
  EvmM.modifyEvm (fun e => { e with stateGasLeft := 0 })
  let sender_balance := (← EvmM.liftTx
    (getAccount (← EvmM.getEvm).message.currentTarget)).balance
  if sender_balance < value then
    stackPush 0
    EvmM.modifyEvm (fun e =>
      { e with returnData := []
               gasLeft := e.gasLeft + message_call_gas.subCall
               stateGasLeft := e.stateGasLeft + reservoir })
  else
    generic_call pre fuel message_call_gas.subCall reservoir value
      (← EvmM.getEvm).message.currentTarget to code_address true false
      memory_input_start_position memory_input_size
      memory_output_start_position memory_output_size code is_delegated
  EvmM.modifyEvm (fun e => { e with pc := e.pc + 1 })

/-- `delegatecall(evm)`. -/
partial def iDelegatecall (pre : PrecompileMap) (fuel : Nat) : EvmM Unit := do
  let gas ← stackPop
  let code_address0 := to_address_masked (← stackPop)
  let memory_input_start_position ← stackPop
  let memory_input_size ← stackPop
  let memory_output_start_position ← stackPop
  let memory_output_size ← stackPop
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_input_start_position, memory_input_size),
     (memory_output_start_position, memory_output_size)]) <$> EvmM.getEvm
  let is_cold := !(← EvmM.getEvm).accessedAddresses.contains code_address0
  let access_gas_cost := if is_cold then GasCosts.COLD_ACCOUNT_ACCESS
    else GasCosts.WARM_ACCESS
  check_gas (access_gas_cost + extend.cost)
  if is_cold then
    EvmM.modifyEvm (fun e =>
      { e with accessedAddresses := setAdd e.accessedAddresses code_address0 })
  let mut extra_gas := access_gas_cost
  let (is_delegated, code_address, delegation_cost) ←
    calculate_delegation_cost code_address0
  if is_delegated then
    extra_gas := extra_gas + delegation_cost
    check_gas (extra_gas + extend.cost)
    EvmM.modifyEvm (fun e =>
      { e with accessedAddresses := setAdd e.accessedAddresses code_address })
  let code ← extCodeOf code_address
  let message_call_gas := calculate_message_call_gas 0 gas
    (← EvmM.getEvm).gasLeft extend.cost extra_gas
  charge_gas (message_call_gas.cost + extend.cost)
  EvmM.modifyEvm (fun e =>
    { e with regularGasUsed := e.regularGasUsed - message_call_gas.subCall })
  extendMemory extend.expandBy
  let reservoir := (← EvmM.getEvm).stateGasLeft
  EvmM.modifyEvm (fun e => { e with stateGasLeft := 0 })
  let e ← EvmM.getEvm
  generic_call pre fuel message_call_gas.subCall reservoir e.message.value
    e.message.caller e.message.currentTarget code_address false false
    memory_input_start_position memory_input_size
    memory_output_start_position memory_output_size code is_delegated
  EvmM.modifyEvm (fun e => { e with pc := e.pc + 1 })

/-- `staticcall(evm)`. -/
partial def iStaticcall (pre : PrecompileMap) (fuel : Nat) : EvmM Unit := do
  let gas ← stackPop
  let to := to_address_masked (← stackPop)
  let memory_input_start_position ← stackPop
  let memory_input_size ← stackPop
  let memory_output_start_position ← stackPop
  let memory_output_size ← stackPop
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_input_start_position, memory_input_size),
     (memory_output_start_position, memory_output_size)]) <$> EvmM.getEvm
  let is_cold := !(← EvmM.getEvm).accessedAddresses.contains to
  let access_gas_cost := if is_cold then GasCosts.COLD_ACCOUNT_ACCESS
    else GasCosts.WARM_ACCESS
  check_gas (access_gas_cost + extend.cost)
  if is_cold then
    EvmM.modifyEvm (fun e =>
      { e with accessedAddresses := setAdd e.accessedAddresses to })
  let mut extra_gas := access_gas_cost
  let (is_delegated, code_address, delegation_cost) ← calculate_delegation_cost to
  if is_delegated then
    extra_gas := extra_gas + delegation_cost
    check_gas (extra_gas + extend.cost)
    EvmM.modifyEvm (fun e =>
      { e with accessedAddresses := setAdd e.accessedAddresses code_address })
  let code ← extCodeOf code_address
  let message_call_gas := calculate_message_call_gas 0 gas
    (← EvmM.getEvm).gasLeft extend.cost extra_gas
  charge_gas (message_call_gas.cost + extend.cost)
  EvmM.modifyEvm (fun e =>
    { e with regularGasUsed := e.regularGasUsed - message_call_gas.subCall })
  extendMemory extend.expandBy
  let reservoir := (← EvmM.getEvm).stateGasLeft
  EvmM.modifyEvm (fun e => { e with stateGasLeft := 0 })
  generic_call pre fuel message_call_gas.subCall reservoir 0
    (← EvmM.getEvm).message.currentTarget to code_address true true
    memory_input_start_position memory_input_size
    memory_output_start_position memory_output_size code is_delegated
  EvmM.modifyEvm (fun e => { e with pc := e.pc + 1 })

end

/-! ## `process_message_call` (`vm/interpreter.py`) -/

/-- Frame-recursion fuel: the depth limit plus slack; exhaustion is
    unreachable (depth is checked before every recursion). -/
def INTERPRETER_FUEL : Nat := 1024 + 8

/-- `process_message_call(message)`. v0.6.0: authorizations and
    delegation resolution are handled at the top frame inside
    `process_message` (depth 0), so their state-dependent gas charges go
    through the EVM gas pools and an out-of-gas there halts the frame
    cleanly. -/
def process_message_call (pre : PrecompileMap) (msg : Message) :
    EvmM MessageCallOutput := do
  let evm ←
    if msg.target == none then do
      if ← EvmM.liftTx (accountDeployable msg.currentTarget) then
        process_create_message pre INTERPRETER_FUEL msg
      else
        return { gasLeft := 0, refundCounter := 0, logs := [],
                 accountsToDelete := [], error := some .addressCollision,
                 returnData := [], stateGasLeft := msg.stateGasReservoir,
                 regularGasUsed := msg.gas, stateGasUsed := 0 }
    else
      process_message pre INTERPRETER_FUEL msg
  let (logs, accounts_to_delete, refund_counter) :=
    if evm.error.isSome then ([], [], (0 : U256))
    else (evm.logs, evm.accountsToDelete, (evm.refundCounter.toNat : U256))
  pure { gasLeft := evm.gasLeft
         refundCounter := refund_counter
         logs := logs
         accountsToDelete := accounts_to_delete
         error := evm.error
         returnData := evm.output
         stateGasLeft := evm.stateGasLeft
         regularGasUsed := evm.regularGasUsed
         stateGasUsed := frame_state_gas_used evm + evm.authStateGasUsed }

end EvmAsm.Stateless.SpecRef
