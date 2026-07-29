/-
  EvmAsm.Codegen.Programs.ChildFrameHandlerTailHelpers

  The per-effect helpers used by `basicPrecompileCallTail`: EIP-7702 delegation
  access charging, the precompile value-balance gate, and the value-effect
  log/record/refund/new-account-gas sequences.

  Split out of `ChildFrameHandlerTails.lean` to keep it under the 1500-line
  `Codegen/Programs` cap (`scripts/check-file-size.sh`, no per-file exception).
  That file had 18 lines of headroom, and this tail is where producer inserts
  keep landing -- so the next such change would have breached the cap and read
  as the author's own fault rather than inherited crowding.

  Behaviour-neutral: definitions are moved verbatim, so emission is
  byte-identical and no layout regen is required.
-/

import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.EvmStorageAccessGas
import EvmAsm.Codegen.Programs.Modexp
import EvmAsm.Codegen.Programs.PrecompileRuntime
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Rv64.Program
import EvmAsm.Stateless.SpecRef.Gas
namespace EvmAsm.Codegen
open EvmAsm.Rv64

/-- Charge the EIP-7702 delegation target access for a CALL-family callee when
    the callee is a `0xef0100||addr` delegation marker. -/
def callDelegationAccessChargeAsm (tag : String) : String :=
  "  addi sp, sp, -32\n  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
  "  ld a0, 576(x20)\n  ld a1, 584(x20)\n  la a2, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
  "  ld a3, 592(x20)\n  ld a4, 600(x20)\n  ld a5, 608(x20)\n  ld a6, 616(x20)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  mv t2, a0\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
  -- not found / error -> not delegated -> no charge
  "  bnez t2, .Lcdac_done_" ++ tag ++ "\n" ++
  "  la t3, cahsr_code_length; ld t3, 0(t3); li t4, 23; bne t3, t4, .Lcdac_done_" ++ tag ++ "\n" ++
  "  ld t3, 608(x20); la t4, cahsr_code_offset; ld t4, 0(t4); add t3, t3, t4\n" ++  -- t3 = code ptr
  "  lbu t4, 0(t3); li t5, 0xef; bne t4, t5, .Lcdac_done_" ++ tag ++ "\n" ++
  "  lbu t4, 1(t3); li t5, 0x01; bne t4, t5, .Lcdac_done_" ++ tag ++ "\n" ++
  "  lbu t4, 2(t3); bnez t4, .Lcdac_done_" ++ tag ++ "\n" ++
  -- Same-block EIP-7702 authorizations update the account's code before message
  -- execution. If the BAL has a final delegation marker for this callee, it is
  -- the tx-state code execution-specs sees; charge/follow that marker instead
  -- of the stale pre-state marker returned by code_at_header_state_root.
  "  addi sp, sp, -32\n  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); sd t3, 24(sp)\n" ++
  "  la a0, " ++ runtimeAccessSeedScratchLabel ++ "; ld a1, 592(x20); ld a2, 600(x20); li a3, 1\n" ++
  "  ld a4, 608(x20)\n" ++                                -- evm-asm-uzb6b: resolver codes base (descend re-adds 608(x20))
  "  jal ra, bal_same_block_delegation_code_resolve\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); ld t3, 24(sp)\n  addi sp, sp, 32\n" ++
  "  li t4, 1; bne t6, t4, .Lcdac_done_" ++ tag ++ "\n" ++
  -- delegation marker: target = code[3..22] (20-byte canonical BE) at t3+3.
  -- runtime_access_account_charge reads 20 bytes from a0 (read-only), so pass it
  -- the in-place marker bytes; it debits 2500 + inserts on cold, 0 on warm.
  "  addi sp, sp, -32\n  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
  "  addi a0, t3, 3\n  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
  -- add the 100 warm-floor the helper omits, so total = 3000 cold / 100 warm.
  s!"  ld t0, 568(x20)\n  li t1, {EvmAsm.Stateless.SpecRef.GasCosts.WARM_ACCESS}\n  bltu t0, t1, .exit_outofgas\n" ++
  "  sub t0, t0, t1\n  sd t0, 568(x20)\n" ++
  ".Lcdac_done_" ++ tag ++ ":\n"

def precompileValueBalanceGateAsm (tag : String) (netPopBytes valueOff : Nat) : String :=
  -- Value-bearing CALL/CALLCODE to a precompile still runs the generic-call
  -- caller-balance check before entering the precompile. The precompile fast
  -- path charges CALL_VALUE on the successful balance path; insufficient
  -- balance keeps the net value-call charge and returns 0.
  "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
  "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
  "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
  "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
  "  beqz t3, .L" ++ tag ++ "_precompile_balok\n" ++
  "  ld t3, 584(x20)\n" ++
  "  beqz t3, .L" ++ tag ++ "_precompile_value_balok\n" ++
  "  la t0, cd_value_be\n" ++
  "  addi t1, x12, " ++ toString (valueOff+31) ++ "\n" ++
  "  li t2, 32\n" ++
  ".L" ++ tag ++ "_precompile_val:\n" ++
  "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n" ++
  "  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n" ++
  "  bnez t2, .L" ++ tag ++ "_precompile_val\n" ++
  "  addi t0, x20, 63\n  la t1, cd_balance_be\n  li t2, 32\n" ++
  ".L" ++ tag ++ "_precompile_livebal:\n" ++
  "  lbu t3, 0(t0)\n  sb t3, 0(t1)\n" ++
  "  addi t0, t0, -1\n  addi t1, t1, 1\n  addi t2, t2, -1\n" ++
  "  bnez t2, .L" ++ tag ++ "_precompile_livebal\n" ++
  "  la t0, cd_balance_be\n" ++
  "  la t1, cd_value_be\n" ++
  "  li t2, 32\n" ++
  ".L" ++ tag ++ "_precompile_cmp:\n" ++
  "  lbu t3, 0(t0)\n  lbu t4, 0(t1)\n" ++
  "  bltu t3, t4, .L" ++ tag ++ "_precompile_insuffbal\n" ++
  "  bltu t4, t3, .L" ++ tag ++ "_precompile_value_balok\n" ++
  "  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n" ++
  "  bnez t2, .L" ++ tag ++ "_precompile_cmp\n" ++
  ".L" ++ tag ++ "_precompile_value_balok:\n" ++
  "  li t0, 10300\n" ++
  "  ld t1, 568(x20)\n  bltu t1, t0, .exit_outofgas\n" ++
  "  sub t1, t1, t0\n  sd t1, 568(x20)\n" ++
  ".L" ++ tag ++ "_precompile_balok:\n" ++
  "  j .L" ++ tag ++ "_precompile_dispatch\n" ++
  ".L" ++ tag ++ "_precompile_insuffbal:\n" ++
  "  li t0, 8000\n" ++
  "  ld t1, 568(x20)\n  bltu t1, t0, .exit_outofgas\n" ++
  "  sub t1, t1, t0\n  sd t1, 568(x20)\n" ++
  "  la x15, evm_precompile_frame\n" ++
  "  sd x0, 0(x15)\n" ++
  "  sd x0, 8(x15)\n" ++
  "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
  "  sd x0, 0(x12)\n" ++
  "  sd x0, 8(x12)\n" ++
  "  sd x0, 16(x12)\n" ++
  "  sd x0, 24(x12)\n" ++
  "  addi x10, x10, 1\n" ++
  dispatchContinueRet ++ "\n" ++
  ".L" ++ tag ++ "_precompile_dispatch:\n"

def emitSuccessfulPrecompileValueLogAsm (tag : String) (valueOff? : Option Nat) : String :=
  if tag != "call_target" then "" else
  match valueOff? with
  | none => ""
  | some valueOff =>
    -- Value-bearing precompile calls are successful child messages when they
    -- reach the shared success tail. Emit the EIP-7708 transfer log here, not
    -- before dispatch, so failed precompile calls keep the ordinary child
    -- rollback behavior. The appender expects raw EVM stack-word pointers:
    -- env.ADDRESS at x20, callee at x12+32, and value at x12+valueOff.
    "  ld t0, " ++ toString valueOff ++ "(x12)\n" ++
    "  ld t1, " ++ toString (valueOff+8) ++ "(x12)\n  or t0, t0, t1\n" ++
    "  ld t1, " ++ toString (valueOff+16) ++ "(x12)\n  or t0, t0, t1\n" ++
    "  ld t1, " ++ toString (valueOff+24) ++ "(x12)\n  or t0, t0, t1\n" ++
    "  beqz t0, .L" ++ tag ++ "_precompile_xlog_skip\n" ++
    "  mv t0, x20\n  addi t1, x12, 32\n  li t2, 20\n" ++
    ".L" ++ tag ++ "_precompile_xlog_selfcmp:\n" ++
    "  beqz t2, .L" ++ tag ++ "_precompile_xlog_skip\n" ++
    "  lbu t3, 0(t0)\n  lbu t4, 0(t1)\n" ++
    "  bne t3, t4, .L" ++ tag ++ "_precompile_xlog_emit\n" ++
    "  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n" ++
    "  j .L" ++ tag ++ "_precompile_xlog_selfcmp\n" ++
    ".L" ++ tag ++ "_precompile_xlog_emit:\n" ++
    "  addi sp, sp, -32\n  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    "  mv a0, x20\n  addi a1, x12, 32\n  addi a2, x12, " ++ toString valueOff ++ "\n" ++
    "  jal ra, eip7708_append_transfer_log\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    ".L" ++ tag ++ "_precompile_xlog_skip:\n"

/-- Record the successful value move of the CALL-to-precompile fast path.
    `basicPrecompileCallTail` bypasses `callDescendFallThrough`, so it must mirror
    that path's debit/credit rows before returning success. -/
def recordSuccessfulPrecompileValueEffectsAsm (tag : String) (valueOff? : Option Nat) : String :=
  if tag != "call_target" then "" else
  match valueOff? with
  | none => ""
  | some valueOff =>
    "  ld t0, " ++ toString valueOff ++ "(x12); ld t1, " ++ toString (valueOff + 8) ++ "(x12); or t0, t0, t1\n" ++
    "  ld t1, " ++ toString (valueOff + 16) ++ "(x12); or t0, t0, t1; ld t1, " ++ toString (valueOff + 24) ++ "(x12); or t0, t0, t1\n" ++
    "  beqz t0, .L" ++ tag ++ "_precompile_nse_done\n" ++
    "  ld t0, 584(x20); beqz t0, .L" ++ tag ++ "_precompile_nse_done\n" ++
    -- Keep the dispatcher context across the whole inline sequence. Some
    -- precompile kernels do not preserve the s-register snapshot used by the
    -- tail, so restore from this explicit ABI frame rather than from s9-s11.
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    -- `precompileValueBalanceGateAsm` has already populated cd_balance_be and
    -- cd_value_be from the live caller state, and rejected an insufficient value.
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    "  la a0, cd_balance_be; la a1, cd_value_be; la a2, cd_caller_newbal\n" ++
    "  jal ra, u256_sub_be; mv t0, a0\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    "  bnez t0, .L" ++ tag ++ "_precompile_nse_restore\n" ++
    -- Keep the caller frame's live balance in lock-step with the emitted debit.
    "  la t0, cd_caller_newbal; addi t1, x20, 63; li t2, 32\n" ++
    ".L" ++ tag ++ "_precompile_nse_caller_write:\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, -1; addi t2, t2, -1; bnez t2, .L" ++ tag ++ "_precompile_nse_caller_write\n" ++
    -- Canonical BE caller and callee addresses for the effect records.
    "  addi t0, x20, 19; la t1, cd_caller_be; li t2, 20\n" ++
    ".L" ++ tag ++ "_precompile_nse_caller_addr:\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .L" ++ tag ++ "_precompile_nse_caller_addr\n" ++
    "  addi t0, x12, 51; la t1, nse_callee_be; li t2, 20\n" ++
    ".L" ++ tag ++ "_precompile_nse_callee_addr:\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .L" ++ tag ++ "_precompile_nse_callee_addr\n" ++
    -- Caller nonce: header value, overlaid by an earlier same-tx effect.
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    "  ld a0, 576(x20); ld a1, 584(x20); la a2, cd_caller_be; li a3, 20; ld a4, 592(x20); ld a5, 600(x20); la a6, nse_acct\n" ++
    "  jal ra, account_at_header_state_root_tracked; mv t0, a0\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    "  beqz t0, .L" ++ tag ++ "_precompile_nse_caller_nonce; la t0, nse_acct; sd zero, 0(t0)\n" ++
    ".L" ++ tag ++ "_precompile_nse_caller_nonce:\n" ++
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); la a0, cd_caller_be; la a1, nse_acct; jal ra, account_state_latest_nonce\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    "  la t0, nse_acct; ld a3, 0(t0); mv a4, a3\n" ++
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); la a0, cd_caller_be; la a1, cd_balance_be; la a2, cd_caller_newbal; jal ra, record_nonstorage_effect\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    -- Callee credit: use its header state (or zero) plus any earlier same-tx credit.
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    "  ld a0, 576(x20); ld a1, 584(x20); la a2, nse_callee_be; li a3, 20; ld a4, 592(x20); ld a5, 600(x20); la a6, nse_acct\n" ++
    "  jal ra, account_at_header_state_root_tracked; mv t0, a0\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    "  beqz t0, .L" ++ tag ++ "_precompile_nse_callee_pre; la t0, nse_acct; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
    ".L" ++ tag ++ "_precompile_nse_callee_pre:\n" ++
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); la a0, nse_callee_be; la a1, nse_acct; addi a1, a1, 8; jal ra, account_state_latest_balance; ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); la a0, nse_callee_be; la a1, nse_acct; jal ra, account_state_latest_nonce; ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    "  addi sp, sp, -16; sd x10, 0(sp); sd x12, 8(sp); la a0, nse_acct; addi a0, a0, 8; la a1, cd_value_be; la a2, nse_post_bal; jal ra, u256_add_be; ld x10, 0(sp); ld x12, 8(sp); addi sp, sp, 16\n" ++
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); la t0, nse_acct; ld a3, 0(t0); mv a4, a3; la a0, nse_callee_be; addi a1, t0, 8; la a2, nse_post_bal; jal ra, record_nonstorage_effect\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    ".L" ++ tag ++ "_precompile_nse_restore:\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    ".L" ++ tag ++ "_precompile_nse_done:\n"

def refundSuccessfulPrecompileValueStipendAsm (tag : String) (valueOff? : Option Nat) : String :=
  match valueOff? with
  | none => ""
  | some valueOff =>
    -- execution-specs funds every value-bearing CALL/CALLCODE child with the
    -- 2300-gas stipend after charging CALL_VALUE (10300). A successful
    -- precompile consumes only its own inner gas, so the unused stipend is
    -- returned with the rest of the child allotment. The fast path has no
    -- child frame and charged the full 10300 in precompileValueBalanceGateAsm;
    -- return the stipend at the shared success join to preserve the same net
    -- 8000 value-transfer charge. Zero-value calls receive no stipend.
    "  ld t0, " ++ toString valueOff ++ "(x12)\n" ++
    "  ld t1, " ++ toString (valueOff+8) ++ "(x12)\n  or t0, t0, t1\n" ++
    "  ld t1, " ++ toString (valueOff+16) ++ "(x12)\n  or t0, t0, t1\n" ++
    "  ld t1, " ++ toString (valueOff+24) ++ "(x12)\n  or t0, t0, t1\n" ++
    "  beqz t0, .L" ++ tag ++ "_precompile_stipend_done\n" ++
    "  ld t0, 568(x20)\n  li t1, 2300\n  add t0, t0, t1\n  sd t0, 568(x20)\n" ++
    ".L" ++ tag ++ "_precompile_stipend_done:\n"

def successfulPrecompileNewAccountStateGasAsm (tag : String) (valueOff? : Option Nat) : String :=
  if tag != "call_target" then "" else
  match valueOff? with
  | none => ""
  | some valueOff =>
    -- CALL with nonzero value creates the callee account when it was not alive
    -- before the call. Active precompiles execute through this fast path, so mirror
    -- generic CALL's EIP-8037 NEW_ACCOUNT state-gas charge before child gas is
    -- allotted. Successful precompile transfers emit EIP-7708 descriptors in
    -- this frame, so scan existing Transfer logs for prior same-tx liveness.
    "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
    "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  beqz t3, .L" ++ tag ++ "_pc_nacc_done\n" ++
    "  ld t3, 584(x20)\n  beqz t3, .L" ++ tag ++ "_pc_nacc_done\n" ++
    "  ld t1, 472(x20); beqz t1, .L" ++ tag ++ "_pc_nacc_prev_done\n" ++
    "  li t2, 0; la t3, evm_event_logs\n" ++
    ".L" ++ tag ++ "_pc_nacc_prev_scan:\n" ++
    "  beq t2, t1, .L" ++ tag ++ "_pc_nacc_prev_done\n" ++
    "  ld t4, 0(t3); li t5, 3; bne t4, t5, .L" ++ tag ++ "_pc_nacc_prev_next\n" ++
    "  addi t4, t3, 96; addi t5, x12, 32; li t6, 20\n" ++
    ".L" ++ tag ++ "_pc_nacc_prev_cmp:\n" ++
    "  beqz t6, .L" ++ tag ++ "_pc_nacc_done\n" ++
    "  lbu x16, 0(t4); lbu x17, 0(t5); bne x16, x17, .L" ++ tag ++ "_pc_nacc_prev_next\n" ++
    "  addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .L" ++ tag ++ "_pc_nacc_prev_cmp\n" ++
    ".L" ++ tag ++ "_pc_nacc_prev_next:\n" ++
    "  addi t3, t3, 256; addi t2, t2, 1; j .L" ++ tag ++ "_pc_nacc_prev_scan\n" ++
    ".L" ++ tag ++ "_pc_nacc_prev_done:\n" ++
    ".L" ++ tag ++ "_pc_nacc_charge:\n" ++
    liStateGasRuntime "t0" amsterdamStateBytesPerNewAccountV2 ++
    "  la t1, evm_state_gas_left\n  ld t2, 0(t1)\n" ++
    "  bgeu t2, t0, .L" ++ tag ++ "_pc_nacc_res\n" ++
    "  sub t3, t0, t2\n  sd x0, 0(t1)\n" ++
    "  ld t2, 568(x20)\n  bltu t2, t3, .exit_outofgas\n" ++
    "  sub t2, t2, t3\n  sd t2, 568(x20)\n" ++
    "  la t1, evm_state_gas_spilled\n  ld t2, 0(t1)\n  add t2, t2, t3\n  sd t2, 0(t1)\n" ++
    "  j .L" ++ tag ++ "_pc_nacc_used\n" ++
    ".L" ++ tag ++ "_pc_nacc_res:\n" ++
    "  sub t2, t2, t0\n  sd t2, 0(t1)\n" ++
    ".L" ++ tag ++ "_pc_nacc_used:\n" ++
    "  la t1, evm_state_gas_used\n  ld t2, 0(t1)\n  add t2, t2, t0\n  sd t2, 0(t1)\n" ++
    "  la t1, cd_new_account_charged_current\n  li t2, 1\n  sd t2, 0(t1)\n" ++
    ".L" ++ tag ++ "_pc_nacc_done:\n"


end EvmAsm.Codegen
