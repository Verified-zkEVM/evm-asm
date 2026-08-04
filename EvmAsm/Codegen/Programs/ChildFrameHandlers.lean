/-
  EvmAsm.Codegen.Programs.ChildFrameHandlers

  The CALL-family + CREATE-family + precompile child-frame handler module
  (the 6 child-frame opcodes: CREATE, CALL, CALLCODE, DELEGATECALL, CREATE2,
  STATICCALL). `childFrameHandlers` builds their `OpcodeHandlerSpec`s.

  The live descent that the SHIPPED guest registry (`callFrameGuestRegistry`)
  runs is `callDescendFallThrough` — the real CALL/CALLCODE/DELEGATECALL/
  STATICCALL sub-frame entry (depth gate, caller-balance gate, callee code
  resolution via `code_at_header_state_root`, `cd_desc` build + `jal
  call_frame_descend` frame switch). `callPushZeroFallThrough` is the legacy
  push-zero no-op fall-through, now used ONLY by the standalone dispatch probes
  (`tinyInterpRegistry` / `callFrameProbeRegistry`), NOT the verdict.
  CREATE/CREATE2 decode operands inline and run the bounded init-code
  mini-interpreter (see `createUnsupportedTail`); the active precompile
  addresses (0x01..0x05, BLS12-381 G1/G2/pairing/map) have real call tails.

  (Formerly `NoopChildFrame.lean` — renamed because these handlers are no
  longer no-ops. Originally split out of Noop.lean to stay under the
  file-size cap.)
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.Modexp
import EvmAsm.Codegen.Programs.CreateRuntime
import EvmAsm.Codegen.Programs.PrecompileRuntime
import EvmAsm.Codegen.Programs.StaticContext
import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.ChildFrameHandlerTails
import EvmAsm.Codegen.Programs.ChildFrameHandlerTailsGuards
import EvmAsm.Codegen.Programs.ChildFrameCreateTail

namespace EvmAsm.Codegen

open EvmAsm.Rv64


/-- M19 child-frame opcodes (CREATE, CALL, CALLCODE, DELEGATECALL,
    CREATE2, STATICCALL). Non-precompile CALL/CALLCODE/DELEGATECALL/STATICCALL
    route through the live descent (`callDescendFallThrough`): depth +
    caller-balance gates, callee code resolution, and a `call_frame_descend`
    sub-frame switch. CREATE-family paths decode operands, derive the target
    address, and run the bounded init-code mini-interpreter
    (`createUnsupportedTail`); later slices still own the per-address code
    deposit (.8b) and self-contained-gate activation (.8c).

    Net stack delta per opcode (= pop − push, multiplied by 32):

    - **CREATE (0xf0)**: pops 3 (value, offset, size), pushes 1 (addr).
      Net = +64 bytes (= 2 × 32).
    - **CALL (0xf1)** / **CALLCODE (0xf2)**: pops 7 (gas, to, value,
      in_off, in_size, out_off, out_size), pushes 1 (success).
      Net = +192 (= 6 × 32).
    - **DELEGATECALL (0xf4)** / **STATICCALL (0xfa)**: pops 6 (gas,
      to, in_off, in_size, out_off, out_size), pushes 1 (success).
      Net = +160 (= 5 × 32).
    - **CREATE2 (0xf5)**: pops 4 (value, offset, size, salt),
      pushes 1 (addr). Net = +96 (= 3 × 32).

    EVM stack-arg ordering: `μ_s[0]` (top) is `gas`/`value` per the
    Yellow Paper; the descent and the CREATE operand decode read the args
    at these fixed offsets from x12 (the parent stack top).

    **M27 update**: CALL / STATICCALL now recognize target
    addresses 0x01..0x05 as the basic precompile frame surface.
    SHA256 (0x02) hashes input bytes through `zkvm_sha256`,
    IDENTITY (0x04) copies input bytes to caller output memory, and
    both push success = 1. SHA256 and IDENTITY charge their exact
    word-linear inner precompile gas through the shared helper.
    MODEXP (0x05) handles the zero-length-header shortcut and charges
    its 500 minimum gas before returning empty output. RIPEMD160 (0x03)
    hashes input bytes through the software `zkvm_ripemd160` kernel
    (600 + 120/word gas, 32-byte left-padded returndata).

    **M27.2 update**: CALL / STATICCALL also recognize BLS12-381 G1
    active precompile addresses 0x0b (G1 ADD) and 0x0c (G1 MSM).
    The runtime path enforces execution-specs input-length gates and
    charges G1 ADD's fixed 375 gas plus G1 MSM's discounted per-pair gas.

    **M27.3 update**: CALL / STATICCALL also recognize BLS12-381 G2
    active precompile addresses 0x0d (G2 ADD) and 0x0e (G2 MSM).
    The runtime path enforces execution-specs input-length gates and
    charges G2 ADD's fixed 600 gas plus G2 MSM's discounted per-pair gas.

    **M27.4 update**: CALL / STATICCALL also recognize BLS12-381 pairing
    and map precompile addresses 0x0f (pairing), 0x10 (map-Fp-to-G1), and
    0x11 (map-Fp2-to-G2). Valid-length inputs invoke the linkable backend
    wrappers after charging pairing's per-pair gas and each map precompile's
    fixed gas. Current ziskemu safe-fails those wrappers, so EVM observes
    precompile failure until success-output slices land.

    **M27.1 update**: inactive near-zero addresses 0x12 and 0x101
    are not precompiles in the Amsterdam active set. Route them as
    absent-account calls with success = 1 and empty returndata so the
    precompile_absence fixtures do not stop at the dispatcher surface.

    **Known limitations** (documented in CODEGEN.md M19 narrative):
    - CREATE / CREATE2 derive the target address, reject code-or-nonce
      collisions when account-witness context is attached, and run the
      bounded init-code mini-interpreter, but the deployed code is not yet
      deposited/recorded per-address (.8b) nor activated in the
      self-contained gate (.8c).
    - `callPushZeroFallThrough` (the legacy push-zero no-op) is now the
      fall-through for the standalone dispatch probes only; the shipped
      guest descent is `callDescendFallThrough`. -/
def childFrameHandlers
    (callFallThrough callcodeFallThrough delegateFallThrough staticFallThrough : String)
    (sparseWindows : Bool := false) :
    List OpcodeHandlerSpec :=
  [ { label := "h_CREATE"
    , opcodes := [0xf0]
    , preBody := stackUnderflowGuardAsm 3 ++ "\n" ++ staticContextWriteGuardAsm
    , body := []
    , tail := .custom (createUnsupportedTail 64 false) }
  , { label := "h_CALL"
    , opcodes := [0xf1]
    , preBody := stackUnderflowGuardAsm 7 ++ "\n" ++ staticContextValueTransferGuardAsm 64
    , body := []
    , tail := .custom (precompileMessageProcessorAsm "call_target" 192 96 128 160 192 (some 64) callFallThrough sparseWindows) }
  , { label := "h_CALLCODE"
    , opcodes := [0xf2]
    , preBody := stackUnderflowGuardAsm 7 ++ "\n"
    , body := []
    , tail := .custom (precompileMessageProcessorAsm "callcode_target" 192 96 128 160 192 (some 64) callcodeFallThrough sparseWindows) }
  , { label := "h_DELEGATECALL"
    , opcodes := [0xf4]
    , preBody := stackUnderflowGuardAsm 6 ++ "\n"
    , body := []
    , tail := .custom (precompileMessageProcessorAsm "delegatecall_target" 160 64 96 128 160 none delegateFallThrough sparseWindows) }
  , { label := "h_CREATE2"
    , opcodes := [0xf5]
    , preBody := stackUnderflowGuardAsm 4 ++ "\n" ++ staticContextWriteGuardAsm
    , body := []
    , tail := .custom (createUnsupportedTail 96 true) }
  , { label := "h_STATICCALL"
    , opcodes := [0xfa]
    , preBody := stackUnderflowGuardAsm 6 ++ "\n"
    , body := []
    , tail := .custom (precompileMessageProcessorAsm "staticcall_target" 160 64 96 128 160 none staticFallThrough sparseWindows) } ]

/-- M20 arithmetic no-op handlers.

    The original M20 placeholders covered MULMOD and EXP. Both have now moved
    to real dispatcher handlers in `EvmAsm/Codegen/Programs/Evm.lean`, so this
    list is intentionally empty and remains only to keep the registry assembly
    expression stable. -/
def arithNoopHandlers : List OpcodeHandlerSpec := []

/-- The original non-precompile CALL/STATICCALL fall-through: the call no-ops —
    pop the args, push a `0` (failure) result, advance the PC, and resume. Used by
    `tinyInterpRegistry` (the standalone dispatch probes keep this behaviour). -/
def callPushZeroFallThrough (netPopBytes : Nat) : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  sd x0, 0(x15)\n" ++
  "  sd x0, 8(x15)\n" ++
  "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
  "  sd x0, 0(x12)\n" ++
  "  sd x0, 8(x12)\n" ++
  "  sd x0, 16(x12)\n" ++
  "  sd x0, 24(x12)\n" ++
  "  addi x10, x10, 1\n" ++
  dispatchContinueRet

/-- The real non-precompile CALL/STATICCALL descent (bead .61.6). At the `1:`
    fall-through (regs: x10=parent pc at the CALL, x12=parent stack top with the
    args, x13=parent memory, x20=parent env, x21=parent code base), this:
      1. clears the precompile frame;
      2. depth gate: `evm_call_depth >= 1024` → push 0 (fail);
      2b. balance gate (value-bearing CALL/CALLCODE): if the caller (frame ADDRESS,
         env+0) balance < transfer value → push 0 (fail, no descent), per EVM
         `generic_call`. Skipped for STATICCALL/DELEGATECALL (no value), value==0,
         or when no account-witness context is attached (env+584 == 0);
      3. resolves the callee bytecode via `code_at_header_state_root` (witness ctx
         from env+576..616). It preserves x20/x21 but clobbers the a-regs (x10/x12/
         x13), so those are saved across the call. status 2 (EMPTY_CODE / EOA) →
         push 1 (the call succeeds, runs no code); status 1/3/5 → push 0;
      4. status 0: fill `cd_desc` and `jal call_frame_descend` (frame switch), then
         `j .dispatch_loop` to run the child at its frame.
    Used only by `callFrameGuestRegistry`. `tag` makes the local labels unique per
    call type. `valueOff` is the stack offset of the call value (unused/0 for the
    value-less kinds). `mode` selects the message-call kind (matching
    `call_frame_set_call_env`): `0 = CALL`, `1 = STATICCALL`, `2 = CALLCODE`,
    `3 = DELEGATECALL`. The value-bearing kinds (CALL, CALLCODE) run the balance
    gate and forward value/stipend; STATICCALL/DELEGATECALL carry no value
    (DELEGATECALL inherits the parent's CALLVALUE inside `call_frame_set_call_env`).
    Gas: `call_frame_descend` forwards the EIP-150 63/64 + stipend to the child;
    the caller-side value/new-account/parent charge is a follow-up (the descent is
    inert in the single-tx verdict). -/
def callDescendFallThrough
    (tag : String) (netPopBytes valueOff inOff inSize outOff outSize : Nat)
    (mode : Nat) : String :=
  let np := toString netPopBytes
  -- value-bearing message calls (CALL=0, CALLCODE=2) charge value/balance; the
  -- value-less kinds (STATICCALL=1, DELEGATECALL=3) skip the balance gate.
  let valueBearing := mode == 0 || mode == 2
  -- EIP-214 forbids CALL with nonzero value in a static context. CALLCODE is
  -- value-bearing for balance/gas accounting but is not write-protected here.
  let staticValueForbidden := mode == 0
  -- fva3w: EIP-7708 value-CALL transfer log emission is DEFERRED (see below); reset the
  -- per-CALL pending flag so a prior CALL's value transfer does not leak into this one.
  -- The snippet that emits one pending Transfer(cd_caller_be, cd_callee_be, cd_value_be)
  -- log into the CURRENT frame's env (env+472 count, via eip7708_append_transfer_log) and
  -- clears the flag. Used at .Lcd_descend (child env) and .Lcd_empty (parent env).
  -- ⛔ GH #10998: EMITTED ONLY WHERE THE FLAG CAN BE SET, so the reachability argument IS the
  -- emission condition rather than a comment.  `cd_xfer_log_pending` has exactly ONE setter --
  -- `.Lcd_tl_notself_*`, reached only by mode 0 -- because execution-specs gates
  -- `emit_transfer_log` on `should_transfer_value and value != 0` (`vm/interpreter.py:391-397`):
  -- DELEGATECALL and STATICCALL carry no value, and CALLCODE targets the caller's own context so
  -- the transfer is self-to-self and the spec's `caller != current_target` test excludes it.
  -- Emitting the consumer for those three meant 15 references reading and clearing a flag they
  -- can never write, and a leaked set would have made them emit a log the spec forbids.
  -- ⚠️ The per-CALL RESET is deliberately kept in all four modes: it is what stops a set from
  -- surviving into a later CALL, and it is a different site from the paired clear below.
  let emitPendingXferLog : String → String := fun site =>
    if mode != 0 then "" else
    "  la t0, cd_xfer_log_pending\n  ld t0, 0(t0)\n  beqz t0, .Lcd_xlog_skip_" ++ site ++ tag ++ "\n" ++
    "  la t0, cd_xfer_log_pending\n  sd x0, 0(t0)\n" ++   -- one-shot: clear before emit
    -- build from_sw/to_sw/val_sw on the stack from the canonical-BE globals (mirrors the
    -- CREATE-endowment emit in ChildFrameHandlerTails): a stack word holds the address in
    -- the LOW 20 bytes (the synthetic-log materializer reverses the WHOLE 32B slot to BE).
    -- GH #10938 cut 4: the operand staging is now the shared
    -- `eip7708TransferLogStageAsm`, which the CREATE-endowment site also uses.  Only the
    -- one-shot pending-flag guard above and below is CALL-specific.
    eip7708TransferLogStageAsm "cd_caller_be" "cd_callee_be" "cd_value_be"
      (".Lcd_xlog_from_" ++ site ++ tag) (".Lcd_xlog_to_" ++ site ++ tag)
      (".Lcd_xlog_val_" ++ site ++ tag)
      (restoreLabel := ".Lcd_xlog_restore_" ++ site ++ tag) ++
    ".Lcd_xlog_skip_" ++ site ++ tag ++ ":\n"
  let refundNewAccountStateGas : String → String := fun site =>
    -- execution-specs `credit_state_gas_refund(NEW_ACCOUNT)`: refund in LIFO
    -- order (gas_left spill first, then state reservoir) and reduce state_gas_used.
    "  li t2, 183600
" ++
    "  la t0, evm_state_gas_spilled
  ld t1, 0(t0)
  li t3, 0
" ++
    "  beqz t1, .Lcd_nacc_refund_no_spill_" ++ site ++ tag ++ "
" ++
    "  mv t3, t1
  bleu t1, t2, .Lcd_nacc_refund_spill_le_" ++ site ++ tag ++ "
  mv t3, t2
" ++
    ".Lcd_nacc_refund_spill_le_" ++ site ++ tag ++ ":
" ++
    "  sub t1, t1, t3
  sd t1, 0(t0)
  ld t4, 568(x20)
  add t4, t4, t3
  sd t4, 568(x20)
  sub t2, t2, t3
" ++
    ".Lcd_nacc_refund_no_spill_" ++ site ++ tag ++ ":
" ++
    "  beqz t2, .Lcd_nacc_refund_used_" ++ site ++ tag ++ "
" ++
    "  la t0, evm_state_gas_left
  ld t1, 0(t0)
  add t1, t1, t2
  sd t1, 0(t0)
" ++
    ".Lcd_nacc_refund_used_" ++ site ++ tag ++ ":
" ++
    "  la t0, evm_state_gas_used
  ld t1, 0(t0)
  li t2, 183600
" ++
    "  bltu t1, t2, .Lcd_nacc_refund_done_" ++ site ++ tag ++ "
" ++
    "  sub t1, t1, t2
  sd t1, 0(t0)
" ++
    ".Lcd_nacc_refund_done_" ++ site ++ tag ++ ":
"
  "  la t0, cd_xfer_log_pending\n  sd x0, 0(t0)\n" ++
  "  la t0, cd_xfer_gas_precharged\n  sd x0, 0(t0)\n" ++
  "  la t0, cd_new_account_charged_current\n  sd x0, 0(t0)\n" ++
  "  la t0, cd_callee_alive_before_value\n  sd x0, 0(t0)\n" ++
  -- Stale cd_value_be / nse_callee_be from a prior CALLCODE (or any prior message-call)
  -- must not survive into this opcode. CALLCODE fills cd_value_be for its balance gate
  -- but does not consume it for move_ether (self-transfer, mode 2). A later CALL with
  -- stack value 0 skips the nse_callee fill, yet post-descend record_message_value_transfer
  -- still runs with a3=1 and reads the leftover cd_value_be — crediting nse_callee_be
  -- (still zero) and creating account 0x0 with the leaked wei (fc=1 GASPRICE-debug b19).
  -- Mirror the per-CALL pending-flag reset above. Spec: interpreter.py:385-391 move_ether
  -- only when should_transfer_value and value != 0 for THIS message.
  "  la t0, cd_value_be\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t0, nse_callee_be\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  mv s10, x10                           # preserve parent PC through CALL fallthrough helpers\n" ++
  "  la x15, evm_precompile_frame\n" ++
  "  sd x0, 0(x15)\n" ++
  "  sd x0, 8(x15)\n" ++
  -- depth gate
  "  la t0, evm_call_depth\n" ++
  "  ld t0, 0(t0)\n" ++
  "  li t1, 1024\n" ++
  "  bgeu t0, t1, .Lcd_fail_" ++ tag ++ "\n" ++
  -- Static-context value transfer gate. STATICCALL itself is value-less; only
  -- CALL with a nonzero value exceptional-fails in a static context.
  (if !staticValueForbidden then "" else
    "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
    "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  beqz t3, .Lcd_static_ok_" ++ tag ++ "\n" ++
    "  ld t4, " ++ toString staticContextFlagOff ++ "(x20)\n" ++
    "  bnez t4, .exit_static_violation\n" ++
    ".Lcd_static_ok_" ++ tag ++ ":\n") ++
  -- balance gate (value-bearing CALL only): EVM `generic_call` rejects the call
  -- with a pushed 0 when the caller's balance is below the transfer value
  -- (vm/instructions/system.py; the value is NOT transferred and the sub-call is
  -- not entered). Mirrors the verified CREATE-path caller-balance lookup: the
  -- caller is the current frame's ADDRESS (env+0) as canonical 20-byte BE, and
  -- the value is the stack word at valueOff. STATICCALL has no value (skipped).
  (if !valueBearing then "" else
    "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
    "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  beqz t3, .Lcd_balok_" ++ tag ++ "\n" ++       -- value == 0: no transfer, skip
    "  ld t3, 584(x20)\n" ++
    "  beqz t3, .Lcd_balok_" ++ tag ++ "\n" ++        -- no account-witness ctx: skip
    -- caller address env+19..env+0 -> cd_caller_be (canonical 20-byte big-endian)
    "  la t0, cd_caller_be\n" ++
    "  addi t1, x20, 19\n" ++
    "  li t2, 20\n" ++
    ".Lcd_addr_" ++ tag ++ ":\n" ++
    "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n" ++
    "  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n" ++
    "  bnez t2, .Lcd_addr_" ++ tag ++ "\n" ++
    -- value word x12+valueOff (32 B) -> cd_value_be (big-endian: read +31..+0)
    "  la t0, cd_value_be\n" ++
    "  addi t1, x12, " ++ toString (valueOff+31) ++ "\n" ++
    "  li t2, 32\n" ++
    ".Lcd_val_" ++ tag ++ ":\n" ++
    "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n" ++
    "  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n" ++
    "  bnez t2, .Lcd_val_" ++ tag ++ "\n" ++
    -- balance_at_header_state_root(caller) -> cd_balance_be. Save x10/x12/x13
    -- (helper clobbers the a-regs that alias them); it preserves x20/x21.
    -- drj99.1: use the caller's LIVE selfBalance (env+32), NOT the PRE-STATE balance_at_header_state_root
    -- lookup. The pre-state lookup returns 0 for a freshly-CREATEd contract (absent pre-block) -> the gate
    -- would falsely deem its value-CALL insufficient -> .Lcd_fail -> no transfer -> the created contract's
    -- balance AND the callee credit are mis-recorded (bv_fail=44/45, initcode_calls_with_value etc.). env+32
    -- is the authoritative current balance (authenticated pre-state + the create endowment-credit + live
    -- debits), and the .Lcd_notself transfer below ALSO debits env+32, so gate and transfer now agree (the
    -- prior split was unsound for a 2nd same-frame value-CALL: the pre-state read is stale-high). env+32 is
    -- LE -> reverse to BE into cd_balance_be. At worst conservative (env+32 missing -> 0 -> false-reject,
    -- never false-accept). cd_caller_be (built above) still feeds the .Lcd_notself self-call guard.
    "  addi t0, x20, 63\n  la t1, cd_balance_be\n  li t2, 32\n" ++
    ".Lcd_livebal_" ++ tag ++ ":\n" ++
    "  lbu t3, 0(t0)\n  sb t3, 0(t1)\n  addi t0, t0, -1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  bnez t2, .Lcd_livebal_" ++ tag ++ "\n" ++
    -- compare cd_balance_be (now the live env+32, BE) vs cd_value_be (32-byte big-endian, MSB first)
    "  la t0, cd_balance_be\n" ++
    "  la t1, cd_value_be\n" ++
    "  li t2, 32\n" ++
    ".Lcd_cmp_" ++ tag ++ ":\n" ++
    "  lbu t3, 0(t0)\n  lbu t4, 0(t1)\n" ++
    "  bltu t3, t4, .Lcd_insuffbal_" ++ tag ++ "\n" ++ -- balance < value: insufficient (charge the value-CALL net gas, then fail)
    "  bltu t4, t3, .Lcd_balok_" ++ tag ++ "\n" ++    -- balance > value: sufficient
    "  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n" ++
    "  bnez t2, .Lcd_cmp_" ++ tag ++ "\n" ++
    ".Lcd_balok_" ++ tag ++ ":\n" ++
    -- 5em02.1: debit the caller's LIVE balance (env+32 = .selfBalance, big-endian) by the
    -- transferred value so SELFBALANCE reads B-V mid-execution. The transfer was inert, so
    -- SELFBALANCE read the staged pre-state balance -> false-reject for value-moving
    -- contracts. CALL (mode 0) only: CALLCODE keeps the value in the caller's own context
    -- (transfer-to-self, no balance change). Guards: value!=0 + account-witness ctx present
    -- (so cd_value_be is the valid BE value the gate populated above) + borrow-check (the
    -- gate verified PRE-state balance>=value; the LIVE env+32 may be lower from an earlier
    -- value-CALL in this frame -> skip on underflow, conservative no-op). u256_sub_be
    -- clobbers a-regs aliasing x10/x12/x13; x20 is preserved.
    (if mode != 0 then "" else
      "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
      "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
      "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
      "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
      "  beqz t3, .Lcd_deb_done_" ++ tag ++ "\n" ++       -- value == 0: no debit
      "  ld t3, 584(x20)\n  beqz t3, .Lcd_deb_done_" ++ tag ++ "\n" ++   -- no ctx -> cd_value_be stale -> skip
      -- self-call guard: if the callee (x12+32, 20-byte BE) == the caller (cd_caller_be,
      -- the gate's 20-byte BE), the value returns to self -> net-zero. The per-frame env
      -- model would otherwise leave the caller frame at B-V after return -> false-reject.
      "  la t0, cd_caller_be\n  addi t1, x12, 32\n  li t2, 20\n" ++
      ".Lcd_selfchk_" ++ tag ++ ":\n" ++
      "  beqz t2, .Lcd_deb_done_" ++ tag ++ "\n" ++        -- all 20 bytes equal -> self-call -> skip
      "  lbu t3, 0(t0)\n  lbu t4, 0(t1)\n  bne t3, t4, .Lcd_notself_" ++ tag ++ "\n" ++
      "  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  j .Lcd_selfchk_" ++ tag ++ "\n" ++
      ".Lcd_notself_" ++ tag ++ ":\n" ++
      "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
      -- env+32 (.selfBalance) is LITTLE-ENDIAN (stack-word: byte 0 = LSB), the same convention as
      -- CALLVALUE@96 (which NoopHalt reverses x20+127->+96 to obtain BE); u256_sub_be is big-endian
      -- (byte 31 = LSB, U256.lean). The prior code fed env+32 STRAIGHT to u256_sub_be -> byte-scrambled
      -- selfBalance debit (drj99.1 part 4). Reverse env[32..63] (LE) -> cd_caller_newbal (BE), subtract
      -- in place (a0==a2 is byte-safe: u256_sub_be reads a0[i] then writes a2[i] at the same index),
      -- then reverse the result back to env+32 (LE).
      "  addi t0, x20, 63\n  la t1, cd_caller_newbal\n  li t2, 32\n" ++
      ".Lcd_sbrev_" ++ tag ++ ":\n" ++
      "  lbu t3, 0(t0)\n  sb t3, 0(t1)\n  addi t0, t0, -1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  bnez t2, .Lcd_sbrev_" ++ tag ++ "\n" ++
      "  la a0, cd_caller_newbal\n" ++                     -- a0 = caller LIVE balance, now BE
      "  la a1, cd_value_be\n" ++                          -- a1 = transferred value (BE)
      "  la a2, cd_caller_newbal\n" ++                     -- a2 = out (in place = balance - value, BE)
      "  jal ra, u256_sub_be\n" ++
      "  mv t0, a0\n" ++                                   -- t0 = borrow flag (before x10=a0 restore)
      "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
      "  bnez t0, .Lcd_deb_done_" ++ tag ++ "\n" ++        -- underflow (live < value): conservative skip
      -- reverse cd_caller_newbal (BE) back into env+32 (LE)
      "  la t0, cd_caller_newbal\n  addi t1, x20, 63\n  li t2, 32\n" ++
      ".Lcd_sbwb_" ++ tag ++ ":\n" ++
      "  lbu t3, 0(t0)\n  sb t3, 0(t1)\n  addi t0, t0, 1\n  addi t1, t1, -1\n  addi t2, t2, -1\n  bnez t2, .Lcd_sbwb_" ++ tag ++ "\n" ++
      -- GH #11001: mark upcoming child depth so frame_return can re-credit parent
      -- env+32 if the child reverts (debit is pre-snapshot; rmv is post-snapshot).
      "  la t0, evm_call_depth\n  ld t0, 0(t0)\n  addi t0, t0, 1\n" ++
      "  slli t0, t0, 3\n  la t1, live_balance_debited_by_depth\n  add t1, t1, t0\n  li t2, 1\n  sd t2, 0(t1)\n" ++
      -- The committing child must still update its live env balance here.  The
      -- paired balance-effect records are published below by the shared
      -- `record_message_value_transfer` producer, using this site-resolved
      -- caller pre-balance and the callee's resolved pre-balance.
      -- The shared producer below publishes the paired debit/credit from the
      -- caller's site-resolved `cd_balance_be` and callee pre-balance.  The
      -- former caller-only nonce/post calculation was solely for the retired
      -- local record and must not remain as a second transfer implementation.
      ".Lcd_deb_done_" ++ tag ++ ":\n") ++
    -- fva3w.BAL: the callee-credit non-storage effect + the EIP-7708 pending transfer log
    -- below are CALL (mode 0) ONLY. CALLCODE (mode 2) runs the code at `code_address` but
    -- keeps execution in the caller's context: the spec sets `to = current_target = caller`
    -- (system.py:537) and process_message moves ether caller->current_target(=caller), a
    -- net-zero SELF-transfer, and emits NO transfer log (interpreter.py:307-318: the log
    -- only fires when caller != current_target). The stack `to` word (x12+32) for CALLCODE is
    -- the CODE address (e.g. 5fecc07e), which receives nothing — recording a balance credit
    -- for it was a false non-storage effect (the BAL omits it) -> bv_fail=44
    -- (bal_callcode_nested_value_transfer, nonexistent_account_access_value_transfer-callcode).
    (if mode != 0 then "" else
    -- i3djw.1: record the value-transfer NON-STORAGE effect for the callee so the
    -- all-accounts non-storage comparator (i3djw.3) can validate it against the BAL.
    -- The callee receives `value`; record (callee, pre_balance, pre+value, nonce, nonce)
    -- — value transfer does not bump the callee nonce. INERT until i3djw.3 wires the
    -- comparator (nothing reads exec_nonstorage_effect_log yet), so over-recording a
    -- value-CALL that later fails code resolution is harmless now; success-gating is
    -- deferred to i3djw.3. a0/a2/a3 alias x10/x12/x13 (PC/stack/mem-base), so the
    -- dispatcher invariants are saved/restored around every helper call.
    "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
    "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  beqz t3, .Lcd_nse_done_" ++ tag ++ "\n" ++       -- value == 0: no transfer, skip
    -- r4x4y.1: convert the callee address into nse_callee_be as CANONICAL big-endian.
    -- The EVM stack word at x12+32 stores the address in word (LE-limb) order, so copy it
    -- BACKWARD (byte 19 down to 0), mirroring cd_callee_be's code-lookup conversion. The
    -- prior FORWARD copy left nse_callee_be byte-reversed, so (a) account_at_header_state_root
    -- looked up the wrong account and (b) the BAL all-accounts non-storage compare
    -- (i3djw.3 forward/reverse) never matched the recorded address -> block_gas_used_call_new_account
    -- false-reject bv_fail=45 (the new account looked "omitted" by the BAL).
    "  addi t0, x12, " ++ toString (32 + 19) ++ "\n  la t1, nse_callee_be\n  li t2, 20\n" ++  -- x12+32+19 (to-word high byte)
    ".Lcd_nse_cpaddr_" ++ tag ++ ":\n" ++
    "  beqz t2, .Lcd_nse_cpaddr_d_" ++ tag ++ "\n" ++
    "  lbu t3, 0(t0)\n  sb t3, 0(t1)\n  addi t0, t0, -1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  j .Lcd_nse_cpaddr_" ++ tag ++ "\n" ++
    ".Lcd_nse_cpaddr_d_" ++ tag ++ ":\n" ++
    -- pre fields: account_at_header_state_root(callee) -> nse_acct (nonce, balance)
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  ld a0, 576(x20)\n  ld a1, 584(x20)\n  la a2, nse_callee_be\n  li a3, 20\n  ld a4, 592(x20)\n  ld a5, 600(x20)\n  la a6, nse_acct\n" ++
    "  jal ra, account_at_header_state_root_tracked\n" ++
    "  mv t0, a0\n" ++                                  -- status (capture before restoring x10=a0)
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  beqz t0, .Lcd_nse_header_found_" ++ tag ++ "\n" ++
    "  li t1, 1\n  beq t0, t1, .Lcd_nse_zero_pre_" ++ tag ++ "\n" ++
    "  li t1, 2\n  beq t0, t1, .Lcd_nse_zero_pre_" ++ tag ++ "\n" ++
    "  la t0, cd_callee_alive_before_value; li t1, 1; sd t1, 0(t0); j .Lcd_nse_done_" ++ tag ++ "\n" ++
                                                        -- decode/header errors -> skip charge (conservative)
    ".Lcd_nse_header_found_" ++ tag ++ ":\n" ++
    "  la t0, nse_acct; ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2; ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2; ld t2, 32(t0); or t1, t1, t2\n" ++
    "  bnez t1, .Lcd_nse_header_alive_" ++ tag ++ "\n" ++
    "  la t1, cd_empty_code_hash; ld t2, 72(t0); ld t3, 0(t1); bne t2, t3, .Lcd_nse_header_alive_" ++ tag ++ "\n" ++
    "  ld t2, 80(t0); ld t3, 8(t1); bne t2, t3, .Lcd_nse_header_alive_" ++ tag ++ "\n" ++
    "  ld t2, 88(t0); ld t3, 16(t1); bne t2, t3, .Lcd_nse_header_alive_" ++ tag ++ "\n" ++
    "  ld t2, 96(t0); ld t3, 24(t1); beq t2, t3, .Lcd_nse_have_pre_" ++ tag ++ "\n" ++
    ".Lcd_nse_header_alive_" ++ tag ++ ":\n" ++
    "  la t0, cd_callee_alive_before_value; li t1, 1; sd t1, 0(t0); j .Lcd_nse_have_pre_" ++ tag ++ "\n" ++
    ".Lcd_nse_zero_pre_" ++ tag ++ ":\n" ++
    "  la t0, nse_acct\n  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0); sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); sd zero, 56(t0); sd zero, 64(t0); sd zero, 72(t0); sd zero, 80(t0); sd zero, 88(t0); sd zero, 96(t0)\n" ++
    ".Lcd_nse_have_pre_" ++ tag ++ ":\n" ++
    -- sr5m3.1: overlay the callee credit's pre_balance with the latest same-transaction
    -- non-storage effect when one exists. Header pre-state alone is stale for a pre-existing
    -- account that already moved value in this transaction, e.g. CALL target runs
    -- SELFDESTRUCT first (recording target balance 1 -> 0) and is then called with value 1;
    -- the second CALL credit must record 0 -> 1, not header 1 -> 2. The nonce still comes
    -- from header pre-state because value transfer does not bump it. The helper overwrites
    -- nse_acct+8 only on a hit; miss keeps the header/zero pre_balance above.
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  la a0, nse_callee_be\n  la a1, nse_acct\n  addi a1, a1, 8\n" ++
    "  jal ra, account_state_latest_balance\n  mv t6, a0\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  beqz t6, .Lcd_nse_prior_alive_done_" ++ tag ++ "\n" ++
    "  la t0, nse_acct; ld t1, 8(t0); ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2; ld t2, 32(t0); or t1, t1, t2\n" ++
    "  beqz t1, .Lcd_nse_prior_alive_done_" ++ tag ++ "\n" ++
    "  la t0, cd_callee_alive_before_value; li t1, 1; sd t1, 0(t0)\n" ++
    ".Lcd_nse_prior_alive_done_" ++ tag ++ ":\n" ++
    -- The site has now resolved both live pre-balances: `cd_balance_be` was
    -- captured from the parent env before the debit, and `nse_acct+8` is the
    -- callee header/live-overlay value.  Keep these descriptors in their
    -- stable scratch cells until after `call_frame_descend`: `process_message`
    -- snapshots first, then moves ether, so the shared producer must run in
    -- the child rollback interval below.  Transfer-log scheduling remains at
    -- the caller; `record_message_value_transfer` has no log policy.
    -- Pinned execution-specs v0.5.0 clears a same-tx SELFDESTRUCTed account while
    -- preserving its balance. A later value CALL therefore leaves the credit above
    -- intact; do not append a synthetic zero-balance effect or Burn log.
    -- fhsxz.2.4.2.63.1.6.2.6: EIP-7708 emit_transfer_log for this CALL value move, so the
    -- value-bearing tx's receipt logs/bloom are complete. from = parent ADDRESS (env+0),
    -- to = callee (x12+32), value = value word (x12+valueOff), ALL passed as raw EVM stack
    -- words (LE-limb). The log materializer (log_records_encode_rlp / materialize_log_records)
    -- byte-reverses each 32B topic slot to the canonical BE topic, and the appender byte-
    -- reverses the value into the descriptor's canonical-BE amount — so every field must enter
    -- in stack-word form. `from` (env.ADDRESS) already is; the callee `to` arg and the value
    -- arg on the parent stack are the same form, so they pass verbatim. (The earlier BE right-
    -- aligned `to` into [12:32] and BE `cd_value_be` produced wrong-order topics/data: the
    -- materializer reverses the WHOLE 32B slot, so the address must sit in the low 20 bytes,
    -- not the high 12. Latent until receipt-consensus enforcement un-gates.)
    -- x12 = parent stack top here (restored after record_nonstorage_effect above); the appender
    -- reads through the a1/a2 pointers into EVM memory, which its own sp frame does not disturb.
    -- fva3w (EIP-7708 child-revert rollback): do NOT emit the value-CALL transfer log here
    -- (parent, pre-descent). The spec emits emit_transfer_log INSIDE the child's
    -- process_message (interpreter.py:307-316), so incorporate_child_on_error discards it
    -- when the child REVERTs/exceptional-halts. Emitting it at the parent survived a child
    -- revert -> an extra receipt log -> receipts_root mismatch (bv_fail=53;
    -- bal_4788/2935_invalid_calldata_size with_value). Instead, record that a (non-self)
    -- value transfer is pending in cd_xfer_log_pending and emit LATER: at .Lcd_descend in the
    -- CHILD env (rolled back by frame_return on revert, propagated on success) and at
    -- .Lcd_empty in the parent env (committed: an empty callee runs nothing, cannot revert).
    -- Self-suppression (caller==current_target) still applies: spec only logs to a DIFFERENT
    -- account (interpreter.py:315). For CALL/CALLCODE current_target==callee, so compare
    -- cd_caller_be vs the LIVE callee. nse_callee_be (built just above from x12+32 as canonical
    -- 20B BE) is THIS CALL's callee; cd_callee_be is NOT populated until code resolution (later)
    -- and would be STALE from a prior CALL here (a nested CALL chain then sees caller==stale-
    -- callee and wrongly suppresses the log). Use nse_callee_be.
    "  la t0, cd_caller_be\n  la t1, nse_callee_be\n  li t2, 20\n" ++
    ".Lcd_tl_selfchk_" ++ tag ++ ":\n" ++
    "  beqz t2, .Lcd_nse_done_" ++ tag ++ "\n" ++       -- all 20 bytes equal -> self-call -> no pending log
    "  lbu t3, 0(t0)\n  lbu t4, 0(t1)\n  bne t3, t4, .Lcd_tl_notself_" ++ tag ++ "\n" ++
    "  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  j .Lcd_tl_selfchk_" ++ tag ++ "\n" ++
    ".Lcd_tl_notself_" ++ tag ++ ":\n" ++
    "  la t0, cd_xfer_log_pending\n  li t1, 1\n  sd t1, 0(t0)\n" ++
    ".Lcd_nse_done_" ++ tag ++ ":\n")) ++
  -- bbow4.1.1 / bbow4.2.5.8: EIP-150 value-transfer gas charge. Amsterdam
  -- `generic_call` charges `access_gas + transfer_gas + extend_memory` before
  -- STATE ACCESS / delegation resolution and before EIP-8037 NEW_ACCOUNT state gas.
  -- Access/memory are already charged before this fall-through, so charge the residual
  -- value-transfer 10300 here and arm a one-shot flag. `call_frame_descend` consumes the
  -- flag instead of charging again; empty-code paths refund the 2300 stipend, giving the
  -- same net 8000 as execution-specs while preserving the pre-state-gas ordering.
  (if valueBearing then
     "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
     "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
     "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
     "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
     "  beqz t3, .Lcd_xfergas_ok_" ++ tag ++ "\n" ++   -- value == 0: no transfer
     "  ld t3, 568(x20)\n  li t4, 10300\n  bltu t3, t4, .exit_outofgas\n" ++
     "  sub t3, t3, t4\n  sd t3, 568(x20)\n" ++
     "  la t4, cd_xfer_gas_precharged\n  li t3, 1\n  sd t3, 0(t4)\n" ++
     ".Lcd_xfergas_ok_" ++ tag ++ ":\n"
   else "") ++
  -- nxio8.8 (EIP-8037): CALL (mode 0) with value!=0 to a not-alive callee creates the
  -- account -> charge_state_gas(NEW_ACCOUNT = STATE_BYTES_PER_NEW_ACCOUNT(120)*COST_PER_STATE_BYTE(1530)
  -- = 183600). Spec vm/instructions/system.py:463-464: `if value != 0 and not is_account_alive(to):
  -- charge_state_gas(NEW_ACCOUNT)`. Charged in the PARENT here (before the frame switch). NOT
  -- refunded on child failure: the spec charges it BEFORE saving call_state_gas_reservoir (line 480),
  -- so state_gas_used stays; and a not-alive callee has no code -> the CALL routes to .Lcd_empty
  -- (no child frame at all), so the charge simply stands. CALLCODE(mode 2) recipient is
  -- current_target (always alive) -> excluded; STATICCALL/DELEGATECALL carry no value. Mirrors the
  -- SELFDESTRUCT new-beneficiary charge (#8789): same is_account_alive helpers + charge_state_gas.
  (if mode != 0 then "" else
    "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
    "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  beqz t3, .Lcd_nacc_done_" ++ tag ++ "\n" ++           -- value == 0: no charge
    "  ld t3, 584(x20)\n  beqz t3, .Lcd_nacc_done_" ++ tag ++ "\n" ++   -- no account-witness ctx: skip
    -- callee (`to`) word at x12+32: build cd_callee_be = reverse(mem[x12+32 .. x12+51]) = canonical
    -- 20-byte big-endian (stack words are LE-stored; mirrors the SELFDESTRUCT beneficiary / cd_caller_be).
    "  la t0, cd_callee_be\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n  addi t1, x12, " ++ toString (32+19) ++ "\n  li t2, 20\n" ++
    ".Lcd_nacc_addr_" ++ tag ++ ":\n" ++
    "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n" ++
    "  bnez t2, .Lcd_nacc_addr_" ++ tag ++ "\n" ++
    -- EIP-7702: authorization processing runs before message execution. A same-block
    -- delegation marker therefore makes the original CALL recipient alive even when it was
    -- absent from the block-pre witness. execution-specs tests is_account_alive(to), not the
    -- delegated code address. Resolve the BAL marker as a pure probe (a3=2: no
    -- charge, no free-warm — is_account_alive never touches accessed_addresses);
    -- status 0 (code target) or 2 (precompile target) proves the recipient is
    -- alive, while status 1 is a miss.
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  la a0, cd_callee_be\n  ld a1, 592(x20)\n  ld a2, 600(x20)\n  li a3, 2\n" ++
    "  ld a4, 608(x20)\n" ++                                -- evm-asm-uzb6b: resolver codes base (descend re-adds 608(x20))
    "  jal ra, account_state_delegation_code_resolve\n" ++
    "  mv t6, a0\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  li t5, 1; bne t6, t5, .Lcd_nacc_done_" ++ tag ++ "\n" ++
    -- A callee created earlier in the block is live even when absent from the
    -- pre-block witness.  Ask the shared current AccountState rather than the
    -- append-only comparator log.
    -- is True -> no NEW_ACCOUNT state-gas charge. It is ABSENT from the block-pre witness, so
    -- account_exists_at_header_state_root below would falsely report "not exists" -> wrongly charge the
    -- 183600 new-account state gas -> OOG (.exit_outofgas) -> the value-CALL exceptional-fails and the
    -- child never descends/runs.  Status 1 is live; status 2 needs the bal-zero
    -- tombstone discriminant below (pin is_account_alive); status 3 is a
    -- finalized deletion and must charge.
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  la a0, cd_callee_be\n  jal ra, account_state_lookup_current\n" ++
    "  mv t6, a0\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    -- GH #11334: status 2 conflates a balance-preserved EIP-6780 tombstone
    -- (alive, clear_account_preserving_balance) with a balance-zero one
    -- (dropped from the trie, must read as non-existent), because the writer
    -- keys the tombstone flags on balance OR nonce.  The 32 balance bytes are
    -- the discriminant: only when the tombstone balance is all zero does the
    -- status-2 callee fail is_account_alive and owe the new-account charge.
    "  li t5, 2; bne t6, t5, .Lcd_nacc_std_" ++ tag ++ "\n" ++
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  la a0, cd_callee_be\n  jal ra, account_state_tombstone_balance_zero\n" ++
    "  mv t5, a0\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  bnez t5, .Lcd_nacc_seenentry_" ++ tag ++ "\n" ++
    "  li t6, 2\n" ++
    ".Lcd_nacc_std_" ++ tag ++ ":\n" ++
    codeStateStatusIsLiveAsm "t6" ++
    "  bnez t6, .Lcd_nacc_done_" ++ tag ++ "\n" ++           -- created this tx -> alive -> no charge
    ".Lcd_nacc_seenentry_" ++ tag ++ ":\n" ++
    -- SELFDESTRUCT moves the origin balance to zero but leaves the account alive until tx end.
    "  la t0, evm_selfdestruct_seen_overflow; ld t0, 0(t0); bnez t0, .Lcd_nacc_seen_done_" ++ tag ++ "\n" ++
    "  la t0, evm_selfdestruct_seen_count; ld t1, 0(t0); beqz t1, .Lcd_nacc_seen_done_" ++ tag ++ "\n" ++
    "  la t2, evm_selfdestruct_seen_table\n" ++
    ".Lcd_nacc_seen_scan_" ++ tag ++ ":\n" ++
    "  mv t3, t2; la t4, cd_callee_be; li t5, 20\n" ++
    ".Lcd_nacc_seen_cmp_" ++ tag ++ ":\n" ++
    "  beqz t5, .Lcd_nacc_done_" ++ tag ++ "\n" ++
    "  lbu t6, 0(t3); lbu a0, 0(t4); bne t6, a0, .Lcd_nacc_seen_next_" ++ tag ++ "\n" ++
    "  addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lcd_nacc_seen_cmp_" ++ tag ++ "\n" ++
    ".Lcd_nacc_seen_next_" ++ tag ++ ":\n" ++
    "  addi t2, t2, 32; addi t1, t1, -1; bnez t1, .Lcd_nacc_seen_scan_" ++ tag ++ "\n" ++
    ".Lcd_nacc_seen_done_" ++ tag ++ ":\n" ++
    -- c83ty.2: a constructor-SELFDESTRUCTed same-tx account has no code-effect record, but it is
    -- still alive until transaction end; a later value CALL to it preserves the credited balance and
    -- must not pay a second NEW_ACCOUNT state-gas charge.
    "  la t0, evm_selfdestruct_destroyed_overflow; ld t0, 0(t0); bnez t0, .Lcd_nacc_sdskip_done_" ++ tag ++ "\n" ++
    "  la t0, evm_selfdestruct_destroyed_count; ld t1, 0(t0); beqz t1, .Lcd_nacc_sdskip_done_" ++ tag ++ "\n" ++
    "  la t2, evm_selfdestruct_destroyed_table\n" ++
    ".Lcd_nacc_sdskip_scan_" ++ tag ++ ":\n" ++
    "  mv t3, t2; la t4, cd_callee_be; li t5, 20\n" ++
    ".Lcd_nacc_sdskip_cmp_" ++ tag ++ ":\n" ++
    "  beqz t5, .Lcd_nacc_done_" ++ tag ++ "\n" ++
    "  lbu t6, 0(t3); lbu a0, 0(t4); bne t6, a0, .Lcd_nacc_sdskip_next_" ++ tag ++ "\n" ++
    "  addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lcd_nacc_sdskip_cmp_" ++ tag ++ "\n" ++
    ".Lcd_nacc_sdskip_next_" ++ tag ++ ":\n" ++
    "  addi t2, t2, 32; addi t1, t1, -1; bnez t1, .Lcd_nacc_sdskip_scan_" ++ tag ++ "\n" ++
    ".Lcd_nacc_sdskip_done_" ++ tag ++ ":\n" ++
    -- A previous same-tx value transfer makes an absent callee alive. The flag was
    -- captured before appending this CALL's own credit, so the current transfer cannot
    -- falsely satisfy its own precondition.
    "  la t0, cd_callee_alive_before_value; ld t1, 0(t0); bnez t1, .Lcd_nacc_done_" ++ tag ++ "\n" ++
    -- Header/live balance, nonce, and code liveness was captured before this CALL appended
    -- its own credit. A zero flag therefore means the recipient is absent or EIP-161-empty.
    ".Lcd_nacc_charge_" ++ tag ++ ":\n" ++
    -- charge_state_gas(112 * runtime cost): drain evm_state_gas_left, spill remainder into the frame
    -- gas_left (568(x20)), OOG -> .exit_outofgas when both reservoirs short; state_gas_used += charge.
    liStateGasRuntime "t0" amsterdamStateBytesPerNewAccountV2 ++   -- new-account state gas = 120 * 1530 = 183600 (v0.4.0)
    "  la t1, evm_state_gas_left\n  ld t2, 0(t1)\n" ++
    "  bgeu t2, t0, .Lcd_nacc_res_" ++ tag ++ "\n" ++
    "  sub t3, t0, t2\n" ++
    "  ld t2, 568(x20)\n  bltu t2, t3, .exit_outofgas\n" ++
    "  sd x0, 0(t1)\n" ++
    "  sub t2, t2, t3\n  sd t2, 568(x20)\n" ++
    "  la t1, evm_state_gas_spilled\n  ld t2, 0(t1)\n  add t2, t2, t3\n  sd t2, 0(t1)\n" ++
    "  j .Lcd_nacc_used_" ++ tag ++ "\n" ++
    ".Lcd_nacc_res_" ++ tag ++ ":\n" ++
    "  sub t2, t2, t0\n  sd t2, 0(t1)\n" ++
    ".Lcd_nacc_used_" ++ tag ++ ":\n" ++
    "  la t1, evm_state_gas_used\n  ld t2, 0(t1)\n  add t2, t2, t0\n  sd t2, 0(t1)\n" ++
    "  la t1, cd_new_account_charged_current\n  li t2, 1\n  sd t2, 0(t1)\n" ++
    ".Lcd_nacc_done_" ++ tag ++ ":\n") ++
  -- resolve callee code (save x10/x12/x13 — code_at_header_state_root clobbers a-regs)
  -- `account_at_address` expects a canonical 20-byte big-endian address, while
  -- the EVM stack word stores the low 20 address bytes in word order. Mirror the
  -- new-account helper's conversion before code lookup for every CALL-family mode.
  "  la t0, cd_callee_be\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n  addi t1, x12, " ++ toString (32+19) ++ "\n  li t2, 20\n" ++
  ".Lcd_code_addr_" ++ tag ++ ":\n" ++
  "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n" ++
  "  bnez t2, .Lcd_code_addr_" ++ tag ++ "\n" ++
  -- Layered execution lookup: pending/durable AccountState is authoritative over
  -- the block-pre witness.  In particular a durable tx1 CREATE must be seen by
  -- tx2 even though absent from the header, while a tx-end same-tx deletion
  -- masks stale header code.  Only an overlay miss may query the witness.
  "  addi sp, sp, -64\n" ++
  "  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
  "  la a0, cd_callee_be; jal ra, account_state_lookup_current\n" ++
  "  sd a0, 24(sp); sd a1, 32(sp); sd a2, 40(sp)\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); ld t0, 24(sp); ld t1, 32(sp); ld t2, 40(sp); addi sp, sp, 64\n" ++
  "  bnez t0, .Lcd_acst_done_" ++ tag ++ "\n" ++
  -- AccountState missed: a transaction-finalized EIP-6780 deletion (AccountState
  -- delete-pending tombstone, written by account_state_commit_pending) makes
  -- the callee non-existent in every later transaction, so descend on empty
  -- code rather than stale witness bytes.  Within the destroying transaction
  -- no tombstone exists yet, so same-tx semantics are unchanged.
  "  addi sp, sp, -64\n" ++
  "  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
  "  la a0, cd_callee_be; jal ra, account_state_lookup_current\n" ++
  "  sd a0, 24(sp)\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); ld t0, 24(sp); addi sp, sp, 64\n" ++
  "  li t3, 2; beq t0, t3, .Lcd_empty_" ++ tag ++ "\n" ++
  "  li t3, 3; beq t0, t3, .Lcd_empty_" ++ tag ++ "\n" ++
  "  j .Lcd_header_lookup_" ++ tag ++ "\n" ++
  ".Lcd_acst_done_" ++ tag ++ ":\n" ++
  "  li t3, 1; bne t0, t3, .Lcd_empty_" ++ tag ++ "\n" ++
  "  la t3, cahsr_code_length; sd t2, 0(t3)\n" ++
  "  ld t3, 608(x20); sub t1, t1, t3; la t3, cahsr_code_offset; sd t1, 0(t3)\n" ++
  -- A current CodeState entry may itself be the 23-byte EIP-7702
  -- delegation designator.  Treating that marker as executable code skips
  -- the mode-0 resolver below (the old header path did not have this entry),
  -- so the delegated target is never selected and the child returns failure.
  -- Re-enter the existing header/marker path instead of duplicating its
  -- status handling: it invokes the mode-0 resolver for same-block markers,
  -- preserves status-2 precompile/empty bails, and falls through to the
  -- established prior-block mode-1 path when the immutable header supplies
  -- the marker.  Non-marker CodeState remains the direct descend path.
  "  li t4, 23; bne t2, t4, .Lcd_descend_" ++ tag ++ "\n" ++
  "  ld t3, 608(x20); la t4, cahsr_code_offset; ld t4, 0(t4); add t3, t3, t4\n" ++
  "  lbu t4, 0(t3); li t5, 0xef; bne t4, t5, .Lcd_descend_" ++ tag ++ "\n" ++
  "  lbu t4, 1(t3); li t5, 0x01; bne t4, t5, .Lcd_descend_" ++ tag ++ "\n" ++
  "  lbu t4, 2(t3); bnez t4, .Lcd_descend_" ++ tag ++ "\n" ++
  "  j .Lcd_header_lookup_" ++ tag ++ "\n" ++
  ".Lcd_header_lookup_" ++ tag ++ ":\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
  "  ld a0, 576(x20)\n" ++
  "  ld a1, 584(x20)\n" ++
  "  la a2, cd_callee_be\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  ld a5, 608(x20)\n" ++
  "  ld a6, 616(x20)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  mv t2, a0\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  -- EIP-7702: a CALL to a delegated account runs the TARGET's code, never the
  -- 0xef0100||addr delegation marker itself. code_at_header_state_root resolves
  -- the raw account code, so a same-block-delegated callee whose marker code is
  -- present at the lookup header (e.g. a self-tx reentry into tx.to == sender,
  -- staged with its post-state marker) returns status 0 with the 23-byte marker.
  -- Descending on that runs 0xef (invalid) as code instead of the delegated body
  -- (5tmlt.3: pointer_to_static_reentry self-tx false-reject). Detect the marker
  -- (len 23, prefix ef 01 00 — 0xef can't begin real code per EIP-3541) and route
  -- to the same-block delegation resolver, exactly like the code-lookup MISS path.
  "  bnez t2, .Lcd_resolve_" ++ tag ++ "\n" ++
  "  la t3, cahsr_code_length; ld t3, 0(t3); li t4, 23; bne t3, t4, .Lcd_descend_" ++ tag ++ "\n" ++
  "  ld t3, 608(x20); la t4, cahsr_code_offset; ld t4, 0(t4); add t3, t3, t4\n" ++
  "  lbu t4, 0(t3); li t5, 0xef; bne t4, t5, .Lcd_descend_" ++ tag ++ "\n" ++
  "  lbu t4, 1(t3); li t5, 0x01; bne t4, t5, .Lcd_descend_" ++ tag ++ "\n" ++
  "  lbu t4, 2(t3); bnez t4, .Lcd_descend_" ++ tag ++ "\n" ++
  -- coc3g.7: PRIOR-BLOCK (witness pre-state) EIP-7702 delegation follow on the nested CALL.
  -- The callee's CURRENT code (resolved via code_at_header_state_root) is a 23-byte
  -- 0xef0100||target marker -- a delegated EOA whose delegation lives in the WITNESS PRE-STATE
  -- (not the same-block BAL). The spec (system.py call -> calculate_delegation_cost is SINGLE-HOP
  -- -> get_code(code_address)) runs the SINGLE-HOP TARGET's code in the callee's storage context,
  -- never the marker bytes themselves (call_to_delegated_account_with_value: CALL 0x9098.. ->
  -- delegated to 0x37f5.. = STOP -> succeeds, value transferred + EIP-7708 log emitted; routing to
  -- .Lcd_fail dropped the value-net REGULAR gas -> bv_fail=41). Extract the 20-byte target (marker
  -- bytes 3..22) and re-resolve its code against the SAME witness header (env+576/584), exactly like
  -- #9078's dtrc-path follow. The same-block resolver below only covers in-block (BAL) delegations;
  -- this handles a target whose delegation lives in the pre-state witness. On a target-code MISS fall
  -- through to .Lcd_resolve_; env.ADDRESS stays the callee EOA (call_frame_descend keys storage by
  -- `to`, matching current_target = the EOA). Soundness: descending runs the EXACT code the spec
  -- runs (single-hop target), recording more exec effects -- it cannot accept a block the spec
  -- rejects (the BAL comparator independently checks each declared final).
  -- Same-block EIP-7702 authorizations overwrite the callee's delegation
  -- marker before message execution. Prefer the BAL final marker over the
  -- stale pre-state marker; only fall back to this prior-block path on miss.
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); sd t3, 24(sp)\n" ++
  "  la a0, cd_callee_be; ld a1, 592(x20); ld a2, 600(x20); li a3, 0\n" ++
  "  ld a4, 608(x20)\n" ++
  "  jal ra, account_state_delegation_code_resolve\n" ++
  "  mv t2, a0\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); ld t3, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  -- Status 2 selects an active precompile as the delegated code address.  It
  -- follows the empty-code route rather than descending, but execution has
  -- nevertheless committed to that target, so record it before the route.
  "  li t4, 2; bne t2, t4, .Lcd_same_block_not_precompile_" ++ tag ++ "\n" ++
  recordDelegatedPrecompileTargetAsm ++
  "  j .Lcd_empty_" ++ tag ++ "\n" ++
  ".Lcd_same_block_not_precompile_" ++ tag ++ ":\n" ++
  "  beqz t2, .Lcd_descend_" ++ tag ++ "\n" ++
  "  la t4, cd_deleg_target; addi t5, t3, 3; li t6, 20\n" ++
  ".Lcd_pdeleg_copy_" ++ tag ++ ":\n" ++
  "  beqz t6, .Lcd_pdeleg_copied_" ++ tag ++ "\n" ++
  "  lbu t2, 0(t5); sb t2, 0(t4); addi t5, t5, 1; addi t4, t4, 1; addi t6, t6, -1; j .Lcd_pdeleg_copy_" ++ tag ++ "\n" ++
  ".Lcd_pdeleg_copied_" ++ tag ++ ":\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
  "  ld a0, 576(x20)\n  ld a1, 584(x20)\n  la a2, cd_deleg_target\n  ld a3, 592(x20)\n  ld a4, 600(x20)\n  ld a5, 608(x20)\n  ld a6, 616(x20)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  mv t2, a0\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
  "  bnez t2, .Lcd_resolve_" ++ tag ++ "\n" ++   -- target code MISS -> try same-block resolver
  "  j .Lcd_descend_" ++ tag ++ "\n" ++           -- target code found -> descend on it (cahsr_* now name the target's code)
  ".Lcd_resolve_" ++ tag ++ ":\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); sd t2, 24(sp)\n" ++
  "  la a0, cd_callee_be; ld a1, 592(x20); ld a2, 600(x20); li a3, 1\n" ++
  "  ld a4, 608(x20)\n" ++
  "  jal ra, account_state_delegation_code_resolve\n" ++
  "  mv t3, a0\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); ld t2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  -- As above, a same-block resolution to a precompile executes the selected
  -- target through the precompile route.  The BAL touch is unconditional on
  -- that execution and must not depend on the target having bytecode.
  "  li t4, 2; bne t3, t4, .Lcd_resolve_not_precompile_" ++ tag ++ "\n" ++
  recordDelegatedPrecompileTargetAsm ++
  "  j .Lcd_empty_" ++ tag ++ "\n" ++
  ".Lcd_resolve_not_precompile_" ++ tag ++ ":\n" ++
  "  beqz t3, .Lcd_descend_" ++ tag ++ "\n" ++
  -- CALL into a contract created earlier in this block.  Resolve the current
  -- mutable AccountState before treating a header-witness miss as an empty EOA.
  -- ABSENT from the block-pre witness, so code_at_header_state_root returns status 1 (account
  -- not in state trie) and the delegation resolver also misses -> the call falsely routed to
  -- .Lcd_empty (empty EOA, push 1) and the child's runtime (e.g. its SELFDESTRUCT / outgoing
  -- value-CALLs) NEVER ran in re-execution -> its deletion / beneficiary credit were never
  -- recorded -> the exec-vs-BAL non-storage comparator false-rejects (bv_fail=44 on
  -- selfdestruct_same_tx_via_call + create-then-call families). The CREATE deposit already
  -- published the child's deployed code into AccountState. On the code-lookup miss, resolve
  -- `cd_callee_be` from the shared overlay; on a hit, point the descend code/len at its retained
  -- byte arena (code pointer + length) by setting cahsr_code_offset/length so
  -- record+40) by setting cahsr_code_offset/length so 608(x20)+offset == record+48 (the existing
  -- .Lcd_descend_ path computes code_ptr = 608(x20)+cahsr_code_offset), then DESCEND so the child
  -- runtime runs. Soundness: descending records MORE exec effects (never a SKIP), and the BAL
  -- comparator independently checks each declared final, so this can only fix false-REJECTs, never
  -- introduce a false-accept. The caller-debit / callee-credit / EIP-7708 transfer log above are
  -- recorded ONCE before this decision (unchanged whether we descend or not), so descending does
  -- not double-count them; the child's own SELFDESTRUCT records the deletion / beneficiary credit
  -- separately. The resolver is shared with EXTCODE*/collision/NACC so recreate and
  -- cross-transaction visibility use one current-state rule.
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); sd t2, 24(sp)\n" ++
  "  la a0, cd_callee_be; jal ra, account_state_lookup_current\n" ++
  "  mv t4, a0; mv t5, a1; mv t6, a2\n" ++             -- status, code ptr, code len
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); ld t2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  li t3, 1; bne t4, t3, .Lcd_callee_nocreate_" ++ tag ++ "\n" ++
  "  la t3, cahsr_code_length; sd t6, 0(t3)\n" ++       -- AccountState code length
  "  ld t3, 608(x20); sub t5, t5, t3\n" ++              -- code offset from codes base
  "  la t3, cahsr_code_offset; sd t5, 0(t3)\n" ++
  "  j .Lcd_descend_" ++ tag ++ "\n" ++
  ".Lcd_callee_nocreate_" ++ tag ++ ":\n" ++
  "  li t3, 1\n" ++
  "  beq t2, t3, .Lcd_empty_" ++ tag ++ "\n" ++
  -- coc3g.9.3 (#9458 follow-up, bv_fail=53): status 5 = code_hash not found in
  -- witness.codes. An EXISTING EOA is in the state trie (step 2 ok) but its
  -- code_hash is EMPTY_CODE_HASH (keccak ""), which is never stored in the codes
  -- section -> status 5. A value-CALL to such an existing EOA is a VALID
  -- empty-code callee: the spec runs no code, transfers value, and bills the net
  -- 8000 value gas (10300 - 2300 stipend) -- exactly .Lcd_empty_. Without this the
  -- call routed to .Lcd_fail_ (push 0), skipping the value gas -> receipt
  -- cumulative under-counted by 8000 -> receipts-root mismatch (bv_fail=53 on the
  -- 48 non-allowlisted blob_gas_subtraction_tx cases). Distinguish a genuine
  -- witness-miss (non-empty code hash absent from codes -> fail) from a legitimate
  -- empty-code EOA by checking cahsr_acct_struct.code_hash == EMPTY_CODE_HASH.
  "  li t3, 5\n" ++
  "  bne t2, t3, .Lcd_fail_" ++ tag ++ "\n" ++
  "  la t3, cd_empty_code_hash\n" ++
  "  la t4, cahsr_acct_struct\n" ++
  "  ld t5,  0(t3); ld t6,  72(t4); bne t5, t6, .Lcd_fail_" ++ tag ++ "\n" ++
  "  ld t5,  8(t3); ld t6,  80(t4); bne t5, t6, .Lcd_fail_" ++ tag ++ "\n" ++
  "  ld t5, 16(t3); ld t6,  88(t4); bne t5, t6, .Lcd_fail_" ++ tag ++ "\n" ++
  "  ld t5, 24(t3); ld t6,  96(t4); bne t5, t6, .Lcd_fail_" ++ tag ++ "\n" ++
  "  j .Lcd_empty_" ++ tag ++ "\n" ++
  -- fail (status 2/3/4): pop args, push 0
  ".Lcd_fail_" ++ tag ++ ":\n" ++
  (if valueBearing then
     "  la t0, cd_xfer_gas_precharged\n  ld t1, 0(t0)\n  beqz t1, .Lcd_fail_xfer_done_" ++ tag ++ "\n" ++
     "  sd x0, 0(t0)\n  li t1, 2300\n  ld t2, 568(x20)\n  add t2, t2, t1\n  sd t2, 568(x20)\n" ++
     ".Lcd_fail_xfer_done_" ++ tag ++ ":\n"
   else "") ++
  "  mv x10, s10                           # restore parent PC before direct CALL failure resume\n" ++
  "  addi x12, x12, " ++ np ++ "\n" ++
  "  sd x0, 0(x12); sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)\n" ++
  "  addi x10, x10, 1\n" ++
  dispatchContinueRet ++ "\n" ++
  -- coc3g.7 (bv_fail=41): a value-bearing CALL (mode 0/2) whose caller balance < value
  -- still pays the value-transfer REGULAR gas, then fails (push 0). The balance gate jumps
  -- here (NOT to the shared .Lcd_fail_) so this charge does NOT touch the depth-gate or the
  -- code-resolution-failure arrivals: Amsterdam charges CALL_VALUE before resolution and
  -- returns only the 2300 stipend, so the 8000 ACCOUNT_WRITE portion remains billed. Spec vm/instructions/system.py: charge_gas(extra_gas = access +
  -- CALL_VALUE(10300)) and charge_gas(message_call_gas.cost) run BEFORE the
  -- `sender_balance < value` check (system.py:464/477/488); on insufficient balance only the
  -- sub-call gas (forwarded gas + GAS_CALL_STIPEND(2300)) is returned
  -- (`evm.gas_left += message_call_gas.sub_call`), so the NET regular consumed for the value
  -- transfer is 10300 - 2300 = 8000 (access is already charged via runtime_access_account_charge
  -- before the gate; the value!=0 gate guard guarantees value>0 here so the 8000 is
  -- unconditional). Charge the full 10300 before the duplicated NEW_ACCOUNT state-gas
  -- check below, then return the 2300 stipend only after that check survives; this matches
  -- execution-specs' order (`charge_gas(extra_gas)`, `charge_state_gas`, then the
  -- insufficient-balance branch returns `message_call_gas.sub_call`). Without that order a
  -- one-gas-short state charge can incorrectly survive because the stipend was returned too
  -- early. x12 is still the parent stack top; jump back to .Lcd_fail_ to pop+push 0.
  (if valueBearing then
     ".Lcd_insuffbal_" ++ tag ++ ":\n" ++
     "  # GH #11410: spec reads the stack target's code BEFORE the balance\n" ++
     "  # precheck (generic_call, system.py:461/584). Mirror: record the callee\n" ++
     "  # code read through code_at_header_state_root (code_read_fetch) before\n" ++
     "  # charging and failing, so precheck-failed CALL/CALLCODE still land in\n" ++
     "  # the block code-read set the dynamic preimage gate iterates.\n" ++
     "  la t0, cd_callee_be; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
     "  addi t0, t0, 31; addi t1, x12, 32+19; li t2, 20\n" ++
     ".Lcd_ib_addr_fill_" ++ tag ++ ":\n" ++
     "  lbu t3, 0(t1); sb t3, 0(t0); addi t0, t0, -1; addi t1, t1, -1; addi t2, t2, -1; bnez t2, .Lcd_ib_addr_fill_" ++ tag ++ "\n" ++
     "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
     "  la a0, cd_callee_be; addi a0, a0, 12\n" ++
     "  ld a1, 576(x20); ld a2, 584(x20); ld a3, 592(x20); ld a4, 600(x20); ld a5, 608(x20); ld a6, 616(x20)\n" ++
     "  jal ra, code_at_header_state_root\n" ++
     "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
     "  li t0, 10300\n" ++
     "  ld t1, 568(x20)\n  bltu t1, t0, .exit_outofgas\n" ++
     "  sub t1, t1, t0\n  sd t1, 568(x20)\n" ++
     -- bbow4.2.2 (bv41): the NEW_ACCOUNT state-gas charge (nxio8.8, below) lives in the
     -- descend tail, which this insufficient-balance early-exit BYPASSES. Spec
     -- system.py:463-465 charges `if value != 0 and not is_account_alive(to):
     -- charge_state_gas(NEW_ACCOUNT)` BEFORE the balance check, so it stands even when the
     -- value-CALL fails on insufficient balance. Mirror the nxio8.8 charge here (mode 0 only;
     -- CALLCODE mode 2 recipient = current_target, always alive). value>0 is guaranteed
     -- (insuffbal => caller balance < value, balance>=0). x12 is still the parent stack top
     -- (callee at x12+32); x20 the parent env (witness ctx env+576..616). Without it
     -- bvgr_tx_exec_state_gas under-counts by 183600 -> block_state under-count -> bv41.
     (if mode != 0 then "" else
       "  ld t3, 584(x20)\n  beqz t3, .Lcd_ibnacc_done_" ++ tag ++ "\n" ++   -- no witness ctx -> conservative skip
       "  la t0, cd_callee_be\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n  addi t1, x12, " ++ toString (32+19) ++ "\n  li t2, 20\n" ++
       ".Lcd_ibnacc_addr_" ++ tag ++ ":\n" ++
       "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n" ++
       "  bnez t2, .Lcd_ibnacc_addr_" ++ tag ++ "\n" ++
       -- created this tx -> alive -> no charge
       "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
        "  la a0, cd_callee_be\n  jal ra, account_state_lookup_current\n  mv t6, a0\n" ++
        "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
        -- pin is_account_alive (state_tracker.py:445-463) + system.py:465: same
        -- status-2 / bal-zero-tombstone split as the main nacc site (#11334 /
        -- #11362). Bare codeStateStatusIsLiveAsm treats every status-2 as alive
        -- and undercharges NEW_ACCOUNT 183600 on EMPTY EIP-6780 tombstones.
        "  li t5, 2; bne t6, t5, .Lcd_ibnacc_std_" ++ tag ++ "\n" ++
        "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
        "  la a0, cd_callee_be\n  jal ra, account_state_tombstone_balance_zero\n" ++
        "  mv t5, a0\n" ++
        "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
        "  bnez t5, .Lcd_ibnacc_sdskip_done_" ++ tag ++ "\n" ++
        "  li t6, 2\n" ++
        ".Lcd_ibnacc_std_" ++ tag ++ ":\n" ++
        codeStateStatusIsLiveAsm "t6" ++
        "  bnez t6, .Lcd_ibnacc_done_" ++ tag ++ "\n" ++
        -- c83ty.2: same-tx SELFDESTRUCTed accounts are alive until transaction end, so an
        -- insufficient-balance CALL to one also skips NEW_ACCOUNT state gas.
       "  la t0, evm_selfdestruct_destroyed_overflow; ld t0, 0(t0); bnez t0, .Lcd_ibnacc_sdskip_done_" ++ tag ++ "\n" ++
       "  la t0, evm_selfdestruct_destroyed_count; ld t1, 0(t0); beqz t1, .Lcd_ibnacc_sdskip_done_" ++ tag ++ "\n" ++
       "  la t2, evm_selfdestruct_destroyed_table\n" ++
       ".Lcd_ibnacc_sdskip_scan_" ++ tag ++ ":\n" ++
       "  mv t3, t2; la t4, cd_callee_be; li t5, 20\n" ++
       ".Lcd_ibnacc_sdskip_cmp_" ++ tag ++ ":\n" ++
       "  beqz t5, .Lcd_ibnacc_done_" ++ tag ++ "\n" ++
       "  lbu t6, 0(t3); lbu a0, 0(t4); bne t6, a0, .Lcd_ibnacc_sdskip_next_" ++ tag ++ "\n" ++
       "  addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lcd_ibnacc_sdskip_cmp_" ++ tag ++ "\n" ++
       ".Lcd_ibnacc_sdskip_next_" ++ tag ++ ":\n" ++
       "  addi t2, t2, 32; addi t1, t1, -1; bnez t1, .Lcd_ibnacc_sdskip_scan_" ++ tag ++ "\n" ++
       ".Lcd_ibnacc_sdskip_done_" ++ tag ++ ":\n" ++
       -- account_exists_at_header_state_root(callee)
       "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
       "  ld a0, 576(x20)\n  ld a1, 584(x20)\n  la a2, cd_callee_be\n  ld a3, 592(x20)\n  ld a4, 600(x20)\n" ++
       "  jal ra, account_exists_at_header_state_root\n  mv t6, a0\n" ++
       "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
       "  bnez t6, .Lcd_ibnacc_done_" ++ tag ++ "\n" ++           -- lookup err -> conservative skip
       "  la t0, aex_predicate\n  ld t1, 0(t0)\n" ++
       "  beqz t1, .Lcd_ibnacc_charge_" ++ tag ++ "\n" ++         -- not exists -> not alive -> charge
       -- exists: account_is_empty_at_header_state_root(callee)
       "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
       "  ld a0, 576(x20)\n  ld a1, 584(x20)\n  la a2, cd_callee_be\n  ld a3, 592(x20)\n  ld a4, 600(x20)\n" ++
       "  jal ra, account_is_empty_at_header_state_root\n  mv t6, a0\n" ++
       "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
       "  bnez t6, .Lcd_ibnacc_done_" ++ tag ++ "\n" ++           -- lookup err -> skip
       "  la t0, aie_predicate\n  ld t1, 0(t0)\n" ++
       "  beqz t1, .Lcd_ibnacc_done_" ++ tag ++ "\n" ++           -- exists & not empty = alive -> no charge
       ".Lcd_ibnacc_charge_" ++ tag ++ ":\n" ++
       liStateGasRuntime "t0" amsterdamStateBytesPerNewAccountV2 ++   -- NEW_ACCOUNT state gas = 120*1530 = 183600
       "  la t1, evm_state_gas_left\n  ld t2, 0(t1)\n" ++
       "  bgeu t2, t0, .Lcd_ibnacc_res_" ++ tag ++ "\n" ++
       "  sub t3, t0, t2\n" ++
       "  ld t2, 568(x20)\n  bltu t2, t3, .exit_outofgas\n" ++
       "  sd x0, 0(t1)\n" ++
       "  sub t2, t2, t3\n  sd t2, 568(x20)\n" ++
       "  la t1, evm_state_gas_spilled\n  ld t2, 0(t1)\n  add t2, t2, t3\n  sd t2, 0(t1)\n" ++
       "  j .Lcd_ibnacc_used_" ++ tag ++ "\n" ++
       ".Lcd_ibnacc_res_" ++ tag ++ ":\n" ++
       "  sub t2, t2, t0\n  sd t2, 0(t1)\n" ++
       ".Lcd_ibnacc_used_" ++ tag ++ ":\n" ++
       "  la t1, evm_state_gas_used\n  ld t2, 0(t1)\n  add t2, t2, t0\n  sd t2, 0(t1)\n" ++
       refundNewAccountStateGas "ib" ++
       ".Lcd_ibnacc_done_" ++ tag ++ ":\n") ++
     "  li t0, 2300\n" ++
     "  ld t1, 568(x20)\n  add t1, t1, t0\n  sd t1, 568(x20)\n" ++
     "  j .Lcd_fail_" ++ tag ++ "\n"
   else "") ++
  -- empty code (EOA): the call succeeds, runs nothing → push 1
  ".Lcd_empty_" ++ tag ++ ":\n" ++
  -- bnctz: a value-bearing CALL/CALLCODE (mode 0/2) to an empty/non-existent callee still pays the
  -- value-transfer REGULAR gas. Spec system.py:444 charges extra_gas = access + CALL_VALUE(10300);
  -- message_call_gas then funds the empty callee with the 2300 stipend, which returns unused, so
  -- the NET regular consumed is 10300 - 2300 = 8000 (access is already charged via
  -- runtime_access_account_charge; the new-account STATE gas is charged above). The .Lcd_empty
  -- fast-path takes no child frame, so charge that 8000 net here. Without it, block_inc0 (and the
  -- receipt = block_regular + tx_state) under-count by 8000 -> block_gas_used_call_new_account
  -- bv_fail=53.
  -- coc3g.7 (bv_fail=41, bal_nonexistent callcode_positive_value): CALLCODE (mode 2) with value to a
  -- nonexistent CODE target (`to = current_target`, code from the popped address = empty) also runs
  -- nothing and pays this 8000 net (spec callcode: transfer_gas_cost = CALL_VALUE(10300), stipend 2300
  -- refunded). CALLCODE charges NO new-account state gas (its recipient is current_target, always
  -- alive) so this regular 8000 is the only value cost. STATICCALL/DELEGATECALL are value-less, so
  -- gate on `valueBearing` (mode 0 OR 2). x12 is still the parent stack top (value at x12+valueOff).
  (if valueBearing then
     "  ld t0, " ++ toString valueOff ++ "(x12)\n" ++
     "  ld t1, " ++ toString (valueOff+8) ++ "(x12)\n  or t0, t0, t1\n" ++
     "  ld t1, " ++ toString (valueOff+16) ++ "(x12)\n  or t0, t0, t1\n" ++
     "  ld t1, " ++ toString (valueOff+24) ++ "(x12)\n  or t0, t0, t1\n" ++
     "  beqz t0, .Lcd_empty_noval_" ++ tag ++ "\n" ++
     "  la t2, cd_xfer_gas_precharged\n  ld t3, 0(t2)\n  beqz t3, .Lcd_empty_charge_net_" ++ tag ++ "\n" ++
     "  sd x0, 0(t2)\n  li t0, 2300\n  ld t1, 568(x20)\n  add t1, t1, t0\n  sd t1, 568(x20)\n" ++
     "  j .Lcd_empty_noval_" ++ tag ++ "\n" ++
     ".Lcd_empty_charge_net_" ++ tag ++ ":\n" ++
     "  li t0, 8000\n" ++
     "  ld t1, 568(x20)\n  bltu t1, t0, .exit_outofgas\n" ++
     "  sub t1, t1, t0\n  sd t1, 568(x20)\n" ++
     ".Lcd_empty_noval_" ++ tag ++ ":\n"
   else "") ++
   -- An empty-code CALL still enters `process_message`: after its body snapshot,
   -- `move_ether` commits the paired debit and credit even though no child frame
   -- is needed to execute bytecode.  Every arrival here (AccountState non-live,
   -- both delegation status-2 paths, absent header account, and EMPTY_CODE_HASH)
   -- bypasses `.Lcd_descend`, the only other balance-effect publisher.  Publish
   -- the already-resolved descriptors once before the successful empty-call return.
   -- GH #11001: transfer commits here (no child frame_return) — clear the
   -- pre-descend debit mark so a later failing sibling cannot re-credit it.
   (if mode != 0 then "" else
     "  la t0, evm_call_depth\n  ld t0, 0(t0)\n  addi t0, t0, 1\n" ++
     "  slli t0, t0, 3\n  la t1, live_balance_debited_by_depth\n  add t1, t1, t0\n  sd x0, 0(t1)\n" ++
     recordMessageValueTransferAsm "cd_caller_be" "nse_callee_be" "cd_value_be" "li a3, 1"
       "cd_balance_be" "nse_acct" (recipientPreAdjust := "addi a5, a5, 8")) ++
  -- fva3w: empty callee runs nothing and cannot revert, so the value transfer (and its
  -- EIP-7708 log) is committed. Emit the deferred log in the PARENT env (x20 unchanged here).
  -- x12 still = parent stack top; emitPendingXferLog saves/restores it before the pop below.
  emitPendingXferLog "empty_" ++
  "  mv x10, s10                           # restore parent PC before empty CALL resume\n" ++
  "  addi x12, x12, " ++ np ++ "\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(x12); sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)\n" ++
  "  addi x10, x10, 1\n" ++
  dispatchContinueRet ++ "\n" ++
  -- descend (status 0): build the call descriptor then switch frames
  ".Lcd_descend_" ++ tag ++ ":\n" ++
  "  ld t0, 608(x20)\n" ++
  "  la t1, cahsr_code_offset; ld t1, 0(t1)\n" ++
  "  add t0, t0, t1\n" ++                       -- t0 = code_ptr
  "  la t1, cahsr_code_length; ld t1, 0(t1)\n" ++ -- t1 = code_len
  "  la t2, cd_desc\n" ++
  "  addi t3, x12, 32\n  sd t3, 0(t2)\n" ++      -- to_ptr
  -- value_ptr: the value-bearing kinds (CALL/CALLCODE) pass the stack value;
  -- STATICCALL/DELEGATECALL pass the zero word (set_call_env zeroes/inherits it).
  (if valueBearing then
     "  addi t3, x12, " ++ toString valueOff ++ "\n  sd t3, 8(t2)\n"
   else
     "  la t3, cd_zero_word\n  sd t3, 8(t2)\n") ++
  -- desc+16 = mode (0 CALL / 1 STATICCALL / 2 CALLCODE / 3 DELEGATECALL), read by
  -- call_frame_set_call_env via call_frame_descend.
  "  li t3, " ++ toString mode ++ "\n  sd t3, 16(t2)\n" ++
  "  ld t3, " ++ toString inOff ++ "(x12)\n  sd t3, 24(t2)\n" ++   -- argsOff
  "  ld t3, " ++ toString inSize ++ "(x12)\n  sd t3, 32(t2)\n" ++  -- argsLen
  "  ld t3, " ++ toString outOff ++ "(x12)\n  sd t3, 40(t2)\n" ++  -- outOff
  "  ld t3, " ++ toString outSize ++ "(x12)\n  sd t3, 48(t2)\n" ++ -- outSize
  "  li t3, " ++ np ++ "\n  sd t3, 56(t2)\n" ++                    -- netPopBytes
  "  sd t0, 64(t2)\n" ++                                           -- code_ptr
  "  sd t1, 72(t2)\n" ++                                           -- code_len
  "  ld t3, 0(x12)\n  sd t3, 80(t2)\n" ++                          -- requested_gas
  (if !valueBearing then
     "  sd x0, 88(t2)\n"                                           -- value_nonzero = 0
   else
     "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
     "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
     "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
     "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
     "  snez t3, t3\n  sd t3, 88(t2)\n") ++                        -- value_nonzero
  "  mv x10, s10                           # restore parent PC for frame_save_regs\n" ++
  "  la a1, cd_desc\n" ++
  "  jal ra, call_frame_descend\n" ++
  -- The child snapshot is now established.  Publish the paired value-transfer
  -- BAL effects from the pre-resolved stable descriptors so frame_return drops
  -- them with a reverting child, matching process_message's snapshot→move_ether
  -- ordering. The helper performs no state lookup; it only consumes these
  -- caller-supplied pointers, so the switched x12/x20 registers are irrelevant.
  -- This is deliberately before the first child dispatch: cd_caller_be,
  -- nse_callee_be, cd_value_be, cd_balance_be, and nse_acct are static scratch
  -- reused by nested calls, so they are valid only in this post-descend,
  -- pre-dispatch window.
   (if mode != 0 then "" else
     -- GH #10938: the setup is the shared `recordMessageValueTransferAsm`, which the
     -- CREATE-endowment site also uses.  The spec has ONE `move_ether` for both, since
     -- `process_create_message` delegates to `process_message` (`interpreter.py:212`).
     recordMessageValueTransferAsm "cd_caller_be" "nse_callee_be" "cd_value_be" "li a3, 1"
       "cd_balance_be" "nse_acct" (recipientPreAdjust := "addi a5, a5, 8") ++
     -- Credit child env+32 (.selfBalance) with the transferred value so nested-frame
     -- SELFBALANCE and the child's own CREATE value-gate see pre + call.value.
     -- call_frame_descend stages env+32 from pre-transfer balance only; the parent
     -- debit above updates the caller frame, but until now nothing wrote the callee
     -- frame. CREATE already credits its child after descend (ChildFrameCreateTail
     -- drj99.1 part 2); mirror that here. Inside the child rollback interval: a
     -- REVERT/exceptional halt discards the frame, so the credit dies with it.
     -- Skip value==0 (cd_value_be may be stale) and self-call (net-zero; parent debit
     -- also skips — adding V would make SELFBALANCE read B+V).
     "  la t0, cd_value_be\n" ++
     "  ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2\n" ++
     "  ld t2, 16(t0); or t1, t1, t2\n" ++
     "  ld t2, 24(t0); or t1, t1, t2\n" ++
     "  beqz t1, .Lcd_child_sb_done_" ++ tag ++ "\n" ++
     "  la t0, cd_caller_be\n  la t1, nse_callee_be\n  li t2, 20\n" ++
     ".Lcd_child_sb_self_" ++ tag ++ ":\n" ++
     "  beqz t2, .Lcd_child_sb_done_" ++ tag ++ "\n" ++
     "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lcd_child_sb_credit_" ++ tag ++ "\n" ++
     "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
     "  j .Lcd_child_sb_self_" ++ tag ++ "\n" ++
     ".Lcd_child_sb_credit_" ++ tag ++ ":\n" ++
     "  addi t0, x20, 63\n  la t1, cd_caller_newbal\n  li t2, 32\n" ++
     ".Lcd_child_sb_rev_" ++ tag ++ ":\n" ++
     "  lbu t3, 0(t0); sb t3, 0(t1)\n" ++
     "  addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1\n" ++
     "  bnez t2, .Lcd_child_sb_rev_" ++ tag ++ "\n" ++
      -- Save set = write set of the helper args: a0=x10, a1=x11, a2=x12.
      -- (Inherited CREATE comment claimed a0-a2 alias x10/x12/x13 — wrong.)
      "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x11, 8(sp)\n  sd x12, 16(sp)\n" ++
      "  la a0, cd_caller_newbal\n  la a1, cd_value_be\n  la a2, cd_caller_newbal\n" ++
      "  jal ra, u256_add_be\n" ++
      "  ld x10, 0(sp)\n  ld x11, 8(sp)\n  ld x12, 16(sp)\n  addi sp, sp, 32\n" ++
      "  la t0, cd_caller_newbal\n  addi t1, x20, 63\n  li t2, 32\n" ++
      ".Lcd_child_sb_wb_" ++ tag ++ ":\n" ++
      "  lbu t3, 0(t0); sb t3, 0(t1)\n" ++
      "  addi t0, t0, 1; addi t1, t1, -1; addi t2, t2, -1\n" ++
      "  bnez t2, .Lcd_child_sb_wb_" ++ tag ++ "\n" ++
      ".Lcd_child_sb_done_" ++ tag ++ ":\n") ++
   -- fva3w: x20 now = CHILD env (call_frame_descend repointed it; eventLogCheckpoint@480 is
   -- set to the current count). Emit the deferred EIP-7708 value-CALL transfer log HERE so it
   -- lands in the child frame's logs: frame_return rolls it back on a child REVERT/exceptional
   -- halt and propagates it on success -- matching spec emit_transfer_log inside process_message.
   emitPendingXferLog "desc_" ++
  -- Every successfully descended CALL-family kind reaches the existing
  -- dispatcher resume sequence through the child entry. The entry is after all
  -- root-only setup and begins with the dispatcher-resume sequence that
  -- `dispatchContinueRet` previously entered after its return. CALLCODE
  -- (mode 2) retains its separate pre-descent value-bearing balance gate.
  (if mode == 0 || mode == 1 || mode == 2 || mode == 3 then
    "  j .runtime_tx_child_message_entry"
   else
    dispatchContinueRet)

end EvmAsm.Codegen
