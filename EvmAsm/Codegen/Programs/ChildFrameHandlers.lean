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
    (callFallThrough callcodeFallThrough delegateFallThrough staticFallThrough : String) :
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
    , tail := .custom (basicPrecompileCallTail "call_target" 192 96 128 160 192 callFallThrough) }
  , { label := "h_CALLCODE"
    , opcodes := [0xf2]
    , preBody := stackUnderflowGuardAsm 7 ++ "\n" ++ staticContextValueTransferGuardAsm 64
    , body := []
    , tail := .custom (basicPrecompileCallTail "callcode_target" 192 96 128 160 192 callcodeFallThrough) }
  , { label := "h_DELEGATECALL"
    , opcodes := [0xf4]
    , preBody := stackUnderflowGuardAsm 6 ++ "\n"
    , body := []
    , tail := .custom (basicPrecompileCallTail "delegatecall_target" 160 64 96 128 160 delegateFallThrough) }
  , { label := "h_CREATE2"
    , opcodes := [0xf5]
    , preBody := stackUnderflowGuardAsm 4 ++ "\n" ++ staticContextWriteGuardAsm
    , body := []
    , tail := .custom (createUnsupportedTail 96 true) }
  , { label := "h_STATICCALL"
    , opcodes := [0xfa]
    , preBody := stackUnderflowGuardAsm 6 ++ "\n"
    , body := []
    , tail := .custom (basicPrecompileCallTail "staticcall_target" 160 64 96 128 160 staticFallThrough) } ]

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
  "  j .dispatch_loop"

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
  "  la x15, evm_precompile_frame\n" ++
  "  sd x0, 0(x15)\n" ++
  "  sd x0, 8(x15)\n" ++
  -- depth gate
  "  la t0, evm_call_depth\n" ++
  "  ld t0, 0(t0)\n" ++
  "  li t1, 1024\n" ++
  "  bgeu t0, t1, .Lcd_fail_" ++ tag ++ "\n" ++
  -- Static-context value transfer gate. STATICCALL itself is value-less, but
  -- CALL/CALLCODE with a nonzero value is state-changing and must exceptional-fail.
  (if !valueBearing then "" else
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
    "  addi sp, sp, -32\n" ++
    "  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    "  ld a0, 576(x20)\n" ++
    "  ld a1, 584(x20)\n" ++
    "  la a2, cd_caller_be\n" ++
    "  ld a3, 592(x20)\n" ++
    "  ld a4, 600(x20)\n" ++
    "  la a5, cd_balance_be\n" ++
    "  jal ra, balance_at_header_state_root\n" ++
    "  mv t2, a0\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp)\n" ++
    "  addi sp, sp, 32\n" ++
    "  bnez t2, .Lcd_fail_" ++ tag ++ "\n" ++         -- lookup failed/absent -> balance 0 < value
    -- compare cd_balance_be vs cd_value_be (32-byte big-endian, MSB first)
    "  la t0, cd_balance_be\n" ++
    "  la t1, cd_value_be\n" ++
    "  li t2, 32\n" ++
    ".Lcd_cmp_" ++ tag ++ ":\n" ++
    "  lbu t3, 0(t0)\n  lbu t4, 0(t1)\n" ++
    "  bltu t3, t4, .Lcd_fail_" ++ tag ++ "\n" ++     -- balance < value: insufficient
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
      ".Lcd_deb_done_" ++ tag ++ ":\n") ++
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
    -- pre fields: account_at_header_state_root(callee) -> nse_acct (nonce@0, balance@8)
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  ld a0, 576(x20)\n  ld a1, 584(x20)\n  la a2, nse_callee_be\n  li a3, 20\n  ld a4, 592(x20)\n  ld a5, 600(x20)\n  la a6, nse_acct\n" ++
    "  jal ra, account_at_header_state_root\n" ++
    "  mv t0, a0\n" ++                                  -- status (capture before restoring x10=a0)
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  beqz t0, .Lcd_nse_have_pre_" ++ tag ++ "\n" ++
    "  li t1, 1\n  beq t0, t1, .Lcd_nse_zero_pre_" ++ tag ++ "\n" ++
    "  li t1, 2\n  beq t0, t1, .Lcd_nse_zero_pre_" ++ tag ++ "\n" ++
    "  j .Lcd_nse_done_" ++ tag ++ "\n" ++       -- decode/header errors -> skip (conservative)
    ".Lcd_nse_zero_pre_" ++ tag ++ ":\n" ++
    "  la t0, nse_acct\n  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0); sd zero, 32(t0)\n" ++
    ".Lcd_nse_have_pre_" ++ tag ++ ":\n" ++
    -- post_balance = pre_balance (nse_acct+8) + value (cd_value_be, populated above)
    "  addi sp, sp, -16\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n" ++
    "  la a0, nse_acct\n  addi a0, a0, 8\n  la a1, cd_value_be\n  la a2, nse_post_bal\n" ++
    "  jal ra, u256_add_be\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  addi sp, sp, 16\n" ++
    -- append (addr, pre_balance, post_balance, pre_nonce, post_nonce)
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  la t0, nse_acct\n  ld a3, 0(t0)\n  mv a4, a3\n" ++   -- pre_nonce == post_nonce (unchanged by value transfer)
    "  la a0, nse_callee_be\n  la a1, nse_acct\n  addi a1, a1, 8\n  la a2, nse_post_bal\n" ++
    "  jal ra, record_nonstorage_effect\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
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
    -- Still inside the value!=0 guard. eip7708_append_transfer_log no-ops on a zero value and
    -- (on the 1024-descriptor cap) drops without appending; ignore its status (the receipts
    -- encoder gates conservatively on the descriptor/data overflow flags).
    -- h2cv5: EIP-7708 self-suppression. The spec emits the transfer log only to a DIFFERENT
    -- account -- at the value-bearing call only when caller != current_target (amsterdam
    -- interpreter.py:314). The value DEBIT above already skips self-calls (CALLCODE keeps the
    -- value in the caller's own context; CALL-to-self is net-zero) via the same
    -- cd_caller_be == x12+32 comparison; mirror it here so a self value-move does NOT emit a
    -- spurious transfer log -> extra receipt log -> receipts_root/logs_bloom mismatch.
    "  la t0, cd_caller_be\n  addi t1, x12, 32\n  li t2, 20\n" ++
    ".Lcd_tl_selfchk_" ++ tag ++ ":\n" ++
    "  beqz t2, .Lcd_nse_done_" ++ tag ++ "\n" ++       -- all 20 bytes equal -> self-call -> suppress log
    "  lbu t3, 0(t0)\n  lbu t4, 0(t1)\n  bne t3, t4, .Lcd_tl_notself_" ++ tag ++ "\n" ++
    "  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  j .Lcd_tl_selfchk_" ++ tag ++ "\n" ++
    ".Lcd_tl_notself_" ++ tag ++ ":\n" ++
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  mv a0, x20\n  addi a1, x12, 32\n  addi a2, x12, " ++ toString valueOff ++ "\n" ++
    "  jal ra, eip7708_append_transfer_log\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    ".Lcd_nse_done_" ++ tag ++ ":\n") ++
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
    "  la t0, cd_callee_be\n  addi t1, x12, " ++ toString (32+19) ++ "\n  li t2, 20\n" ++
    ".Lcd_nacc_addr_" ++ tag ++ ":\n" ++
    "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n" ++
    "  bnez t2, .Lcd_nacc_addr_" ++ tag ++ "\n" ++
    -- account_exists_at_header_state_root(callee) -> aex_predicate (helper clobbers a-regs aliasing x10/x12/x13)
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  ld a0, 576(x20)\n  ld a1, 584(x20)\n  la a2, cd_callee_be\n  ld a3, 592(x20)\n  ld a4, 600(x20)\n" ++
    "  jal ra, account_exists_at_header_state_root\n" ++
    "  mv t6, a0\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  bnez t6, .Lcd_nacc_done_" ++ tag ++ "\n" ++           -- lookup err -> conservative skip (no charge)
    "  la t0, aex_predicate\n  ld t1, 0(t0)\n" ++
    "  beqz t1, .Lcd_nacc_charge_" ++ tag ++ "\n" ++         -- not exists -> not alive -> charge
    -- exists: account_is_empty_at_header_state_root(callee) -> aie_predicate
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  ld a0, 576(x20)\n  ld a1, 584(x20)\n  la a2, cd_callee_be\n  ld a3, 592(x20)\n  ld a4, 600(x20)\n" ++
    "  jal ra, account_is_empty_at_header_state_root\n" ++
    "  mv t6, a0\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  bnez t6, .Lcd_nacc_done_" ++ tag ++ "\n" ++           -- lookup err -> skip
    "  la t0, aie_predicate\n  ld t1, 0(t0)\n" ++
    "  beqz t1, .Lcd_nacc_done_" ++ tag ++ "\n" ++           -- exists & not empty = alive -> no charge
    ".Lcd_nacc_charge_" ++ tag ++ ":\n" ++
    -- charge_state_gas(183600): drain evm_state_gas_left, spill remainder into the frame gas_left
    -- (568(x20)), OOG -> .exit_outofgas when both reservoirs short; state_gas_used += 183600.
    "  li t0, 183600\n" ++
    "  la t1, evm_state_gas_left\n  ld t2, 0(t1)\n" ++
    "  bgeu t2, t0, .Lcd_nacc_res_" ++ tag ++ "\n" ++
    "  sub t3, t0, t2\n  sd x0, 0(t1)\n" ++
    "  ld t2, 568(x20)\n  bltu t2, t3, .exit_outofgas\n" ++
    "  sub t2, t2, t3\n  sd t2, 568(x20)\n  j .Lcd_nacc_used_" ++ tag ++ "\n" ++
    ".Lcd_nacc_res_" ++ tag ++ ":\n" ++
    "  sub t2, t2, t0\n  sd t2, 0(t1)\n" ++
    ".Lcd_nacc_used_" ++ tag ++ ":\n" ++
    "  la t1, evm_state_gas_used\n  ld t2, 0(t1)\n  add t2, t2, t0\n  sd t2, 0(t1)\n" ++
    ".Lcd_nacc_done_" ++ tag ++ ":\n") ++
  -- resolve callee code (save x10/x12/x13 — code_at_header_state_root clobbers a-regs)
  -- `account_at_address` expects a canonical 20-byte big-endian address, while
  -- the EVM stack word stores the low 20 address bytes in word order. Mirror the
  -- new-account helper's conversion before code lookup for every CALL-family mode.
  "  la t0, cd_callee_be\n  addi t1, x12, " ++ toString (32+19) ++ "\n  li t2, 20\n" ++
  ".Lcd_code_addr_" ++ tag ++ ":\n" ++
  "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n" ++
  "  bnez t2, .Lcd_code_addr_" ++ tag ++ "\n" ++
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
  ".Lcd_resolve_" ++ tag ++ ":\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); sd t2, 24(sp)\n" ++
  "  la a0, cd_callee_be; ld a1, 592(x20); ld a2, 600(x20); li a3, 1\n" ++
  "  jal ra, bal_same_block_delegation_code_resolve\n" ++
  "  mv t3, a0\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); ld t2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  beqz t3, .Lcd_descend_" ++ tag ++ "\n" ++
  "  li t3, 1\n" ++
  "  beq t2, t3, .Lcd_empty_" ++ tag ++ "\n" ++
  -- fail (status 2/3/4/5): pop args, push 0
  ".Lcd_fail_" ++ tag ++ ":\n" ++
  "  addi x12, x12, " ++ np ++ "\n" ++
  "  sd x0, 0(x12); sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)\n" ++
  "  addi x10, x10, 1\n" ++
  "  j .dispatch_loop\n" ++
  -- empty code (EOA): the call succeeds, runs nothing → push 1
  ".Lcd_empty_" ++ tag ++ ":\n" ++
  -- bnctz: a value-bearing CALL (mode 0) to an empty/non-existent callee still pays the
  -- value-transfer REGULAR gas. Spec system.py:444 charges extra_gas = access + CALL_VALUE(9000);
  -- message_call_gas then funds the empty callee with the 2300 stipend, which returns unused, so
  -- the NET regular consumed is 9000 - 2300 = 6700 (access is already charged via
  -- runtime_access_account_charge; the new-account STATE gas is charged above). The .Lcd_empty
  -- fast-path takes no child frame, so charge that 6700 net here. Without it, block_inc0 (and the
  -- receipt = block_regular + tx_state) under-count by 6700 -> block_gas_used_call_new_account
  -- bv_fail=53. x12 is still the parent stack top (value at x12+valueOff) before the pop below.
  (if mode == 0 then
     "  ld t0, " ++ toString valueOff ++ "(x12)\n" ++
     "  ld t1, " ++ toString (valueOff+8) ++ "(x12)\n  or t0, t0, t1\n" ++
     "  ld t1, " ++ toString (valueOff+16) ++ "(x12)\n  or t0, t0, t1\n" ++
     "  ld t1, " ++ toString (valueOff+24) ++ "(x12)\n  or t0, t0, t1\n" ++
     "  beqz t0, .Lcd_empty_noval_" ++ tag ++ "\n" ++
     "  li t0, 6700\n" ++
     "  ld t1, 568(x20)\n  bltu t1, t0, .exit_outofgas\n" ++
     "  sub t1, t1, t0\n  sd t1, 568(x20)\n" ++
     ".Lcd_empty_noval_" ++ tag ++ ":\n"
   else "") ++
  "  addi x12, x12, " ++ np ++ "\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(x12); sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)\n" ++
  "  addi x10, x10, 1\n" ++
  "  j .dispatch_loop\n" ++
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
  "  la a1, cd_desc\n" ++
  "  jal ra, call_frame_descend\n" ++
  "  j .dispatch_loop"

end EvmAsm.Codegen
