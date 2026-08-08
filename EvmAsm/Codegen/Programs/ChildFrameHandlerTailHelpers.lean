/-
  EvmAsm.Codegen.Programs.ChildFrameHandlerTailHelpers

  The per-effect helpers used by `precompileMessageProcessorAsm`: EIP-7702 delegation
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

/-- Check the generic CALL/CALLCODE value-gas floor without charging it.

    `system.py` performs the combined access + CALL_VALUE + memory check before
    any target state access. The actual CALL_VALUE charge remains in the
    branch-specific fall-through below; this probe only prevents
    `account_read_record` from publishing a target when that later charge would
    immediately OOG. -/
def callValueGasAvailabilityGateAsm (tag : String) (valueOff : Nat) : String :=
  "  ld t3, " ++ toString valueOff ++ "(x12); ld t4, " ++ toString (valueOff + 8) ++ "(x12); or t3, t3, t4\n" ++
  "  ld t4, " ++ toString (valueOff + 16) ++ "(x12); or t3, t3, t4; ld t4, " ++ toString (valueOff + 24) ++ "(x12); or t3, t3, t4\n" ++
  "  beqz t3, .Lcvga_zero_" ++ tag ++ "\n" ++
  s!"  ld t3, 568(x20); li t4, {EvmAsm.Stateless.SpecRef.GasCosts.CALL_VALUE}; bltu t3, t4, .exit_outofgas\n" ++
  ".Lcvga_zero_" ++ tag ++ ":\n"

/-- Charge the EIP-7702 delegation target access for a CALL-family callee when
    the callee is a `0xef0100||addr` delegation marker.

    Spec (eoa_delegation.calculate_delegation_cost + system.py CALL):
    `check_gas(access + CALL_VALUE + mem + delegation)` then
    `get_account(target)`. Guest charges access/mem first, then this helper
    charges delegation. Target `account_read_record` must NOT run until the
    remaining CALL_VALUE floor still fits — otherwise OOG-before-target
    fixtures (#code60 call_7702_oog / callcode_7702_oog) publish an empty
    AccountChanges shell the rebuild hashes and the supplied BAL omits. -/
def callDelegationAccessChargeAsm (tag : String) (valueOff? : Option Nat := none) : String :=
  "  addi sp, sp, -32\n  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
  "  ld a0, 576(x20)\n  ld a1, 584(x20)\n  la a2, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
  "  ld a3, 592(x20)\n  ld a4, 600(x20)\n  ld a5, 608(x20)\n  ld a6, 616(x20)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  mv t2, a0\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
  -- #11526 / #11508 family: raise compiles to rejection, not "not delegated".
  -- code_at_header_state_root a0:
  --   0 = code found → inspect marker below
  --   1 = account absent from trie → empty account, not delegated → no charge
  --   2/3/4 = MPT / account_decode / header malform → REJECT (spec would not
  --           reach calculate_delegation_cost with a broken witness)
  --   5 = code_hash missing from witness.codes → only EMPTY_CODE_HASH is a
  --       legitimate empty EOA (witness_state.py:204-212); any other hash is
  --       a missing preimage raise → REJECT. Match → not a marker → no charge.
  -- Branch targets MUST differ (11527 conv lesson): done ≠ fail.
  "  beqz t2, .Lcdac_have_code_" ++ tag ++ "\n" ++
  "  li t3, 1; beq t2, t3, .Lcdac_done_" ++ tag ++ "\n" ++
  "  li t3, 5; bne t2, t3, .Lcd_fail_" ++ tag ++ "\n" ++
  "  la t3, cd_empty_code_hash\n" ++
  "  la t4, cahsr_acct_struct\n" ++
  "  ld t5, 0(t3); ld t6, 72(t4); bne t5, t6, .Lcd_fail_" ++ tag ++ "\n" ++
  "  ld t5, 8(t3); ld t6, 80(t4); bne t5, t6, .Lcd_fail_" ++ tag ++ "\n" ++
  "  ld t5, 16(t3); ld t6, 88(t4); bne t5, t6, .Lcd_fail_" ++ tag ++ "\n" ++
  "  ld t5, 24(t3); ld t6, 96(t4); bne t5, t6, .Lcd_fail_" ++ tag ++ "\n" ++
  "  j .Lcdac_done_" ++ tag ++ "\n" ++
  ".Lcdac_have_code_" ++ tag ++ ":\n" ++
  "  la t3, cahsr_code_length; ld t3, 0(t3); li t4, 23; bne t3, t4, .Lcdac_done_" ++ tag ++ "\n" ++
  "  ld t3, 608(x20); la t4, cahsr_code_offset; ld t4, 0(t4); add t3, t3, t4\n" ++  -- t3 = code ptr
  "  lbu t4, 0(t3); li t5, 0xef; bne t4, t5, .Lcdac_done_" ++ tag ++ "\n" ++
  "  lbu t4, 1(t3); li t5, 0x01; bne t4, t5, .Lcdac_done_" ++ tag ++ "\n" ++
  "  lbu t4, 2(t3); bnez t4, .Lcdac_done_" ++ tag ++ "\n" ++
  -- Same-block EIP-7702 authorizations update the account's code before message
  -- execution. If the BAL has a final delegation marker for this callee, it is
  -- the tx-state code execution-specs sees; charge/follow that marker instead
  -- of the stale pre-state marker returned by code_at_header_state_root.
  --
  -- a3=2 PROBE: resolve must not charge/seed. This helper owns the single
  -- access charge below (cold delta + WARM floor). a3=1 used to charge inside
  -- resolve and again here on status 0 → +100 over-debit (#11547 sender bal;
  -- residual 2ffdac after AUTH_BASE #11585). Status 2 (precompile target) must
  -- also take the charge path — probe no longer pre-charges it.
  "  addi sp, sp, -32\n  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); sd t3, 24(sp)\n" ++
  "  la a0, " ++ runtimeAccessSeedScratchLabel ++ "; ld a1, 592(x20); ld a2, 600(x20); li a3, 2\n" ++
  "  ld a4, 608(x20)\n" ++                                -- evm-asm-uzb6b: resolver codes base (descend re-adds 608(x20))
  "  jal ra, account_state_delegation_code_resolve\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); ld t3, 24(sp)\n  addi sp, sp, 32\n" ++
  -- The resolver returns:
  --   0 = selected transaction-state delegation marker (charge target)
  --   1 = no current account-write code fact → retain prior-block marker
  --       from `code_at_header_state_root` at `t3 + 3` (pre-state fallback)
  --   2 = live marker whose target is empty/deleted or a precompile (charge)
  --   3 = current write proves authority is NOT a live delegation (clear or
  --       non-marker code) → NO charge, NO pre-state fallback (#11542 A)
  -- Status 0/2 export the selected target to `bsbd_deleg_target`. Status 1
  -- and 3 are distinct: collapsing empty/clear into status 1 re-charged the
  -- stale pre-state designator after EIP-7702 set_delegation cleared code.
  "  beqz t6, .Lcdac_sameblock_" ++ tag ++ "\n" ++
  "  li t4, 2; beq t6, t4, .Lcdac_sameblock_" ++ tag ++ "\n" ++
  "  li t4, 1; bne t6, t4, .Lcdac_done_" ++ tag ++ "\n" ++
  "  addi t4, t3, 3\n" ++
  "  j .Lcdac_target_selected_" ++ tag ++ "\n" ++
  ".Lcdac_sameblock_" ++ tag ++ ":\n" ++
  "  la t4, bsbd_deleg_target\n" ++
  ".Lcdac_target_selected_" ++ tag ++ ":\n" ++
  -- Preserve the selected target across the access-charge call.  The charge
  -- helper is caller-clobbering, while the final BAL read must use the same
  -- address that was charged.
  "  addi sp, sp, -32\n  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); sd t4, 24(sp)\n" ++
  "  mv a0, t4\n  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); ld t4, 24(sp)\n  addi sp, sp, 32\n" ++
  -- add the 100 warm-floor the helper omits, so total = 3000 cold / 100 warm.
  s!"  ld t0, 568(x20)\n  li t1, {EvmAsm.Stateless.SpecRef.GasCosts.WARM_ACCESS}\n  bltu t0, t1, .exit_outofgas\n" ++
  "  sub t0, t0, t1\n  sd t0, 568(x20)\n" ++
  -- Spec folds CALL_VALUE into check_gas *before* get_account(target). The
  -- early callValueGasAvailabilityGateAsm ran before this helper debited
  -- delegation; re-probe the floor now so OOG on the later CALL_VALUE charge
  -- cannot leave a phantom target shell in account_reads (#code60 +27).
  -- Gate clobbers t3/t4 — park target ptr (t4) across it.
  "  addi sp, sp, -16\n  sd t4, 0(sp)\n" ++
  (match valueOff? with
  | none => ""
  | some valueOff => callValueGasAvailabilityGateAsm ("post_deleg_" ++ tag) valueOff) ++
  "  ld t4, 0(sp)\n  addi sp, sp, 16\n" ++
  -- `calculate_delegation_cost` selected this `code_address`; the spec records
  -- it only after the full (access+CALL_VALUE+mem+delegation) gas check.
  -- Record the resolved delegate here, not the original CALL target (caller
  -- records that separately after the initial static check).
  "  addi sp, sp, -32\n  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); sd t4, 24(sp)\n" ++
  "  mv a0, t4\n" ++
  "  jal ra, account_read_record\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); ld t4, 24(sp)\n  addi sp, sp, 32\n" ++
  ".Lcdac_done_" ++ tag ++ ":\n"

def recordDelegatedPrecompileTargetAsm : String :=
  "  addi sp, sp, -32\n  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
  "  la a0, bsbd_deleg_target\n  jal ra, account_read_record\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n"

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

/-- Reject a precompile call at the EVM child-depth limit.  The guard belongs
    after the initial access and memory-expansion charges, which the spec keeps,
    and before precompile-specific child allotment and state-gas paths, which a
    depth failure never reaches.  It is self-contained because probe registries
    do not define the shipped guest's `.Lcd_fail_*` labels. -/
def precompileDepthGateAsm (labelStem : String) (netPopBytes : Nat) : String :=
  "  la t0, evm_call_depth\n" ++
  "  ld t0, 0(t0)\n" ++
  "  li t1, 1024\n" ++
  "  bltu t0, t1, .L" ++ labelStem ++ "_ok\n" ++
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
  ".L" ++ labelStem ++ "_ok:\n"

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
    `precompileMessageProcessorAsm` bypasses `callDescendFallThrough`, so it must mirror
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
    -- The fast path has no callee frame whose post-CALL read can witness the
    -- transfer, so observe the caller immediately after the live debit.
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); la a0, cd_caller_be; addi a1, x20, 32; li a2, 3; li a3, 0; jal ra, account_agreement_mutation_checkpoint; ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    -- Canonical BE caller and callee addresses for the effect records.
    "  addi t0, x20, 19; la t1, cd_caller_be; li t2, 20\n" ++
    ".L" ++ tag ++ "_precompile_nse_caller_addr:\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .L" ++ tag ++ "_precompile_nse_caller_addr\n" ++
    "  addi t0, x12, 51; la t1, nse_callee_be; li t2, 20\n" ++
    ".L" ++ tag ++ "_precompile_nse_callee_addr:\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .L" ++ tag ++ "_precompile_nse_callee_addr\n" ++
    -- The shared producer owns both balance-only records; this fast path has
    -- no caller-nonce bookkeeping of its own.
    -- Callee credit: use its header state (or zero) plus any earlier same-tx credit.
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    "  ld a0, 576(x20); ld a1, 584(x20); la a2, nse_callee_be; li a3, 20; ld a4, 592(x20); ld a5, 600(x20); la a6, nse_acct\n" ++
    "  jal ra, account_at_header_state_root_tracked; mv t0, a0\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    "  beqz t0, .L" ++ tag ++ "_precompile_nse_callee_pre; la t0, nse_acct; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
    ".L" ++ tag ++ "_precompile_nse_callee_pre:\n" ++
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); la a0, nse_callee_be; la a1, nse_acct; addi a1, a1, 8; li a2, 6; jal ra, account_writes_latest_balance; ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    -- `process_message` moves ether before selecting the precompile executor;
    -- use the same producer as the dispatching CALL path with this fast path's
    -- own resolved operands.  It does not force a child-frame descent.
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp); la a0, cd_caller_be; la a1, nse_callee_be; la a2, cd_value_be; li a3, 1; la a4, cd_balance_be; la a5, nse_acct; addi a5, a5, 8; jal ra, record_message_value_transfer\n" ++
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
