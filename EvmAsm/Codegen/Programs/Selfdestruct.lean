/-
  EvmAsm.Codegen.Programs.Selfdestruct

  SELFDESTRUCT runtime assembly helpers split out of `Programs.Noop` to keep
  the halt-handler module under the file-size guardrail.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.AccountBalance
import EvmAsm.Codegen.Programs.EIP7708Logs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def selfdestructNewAccountSurchargeAsm : String :=
  "  ld t0, 584(x20)\n" ++
  "  beqz t0, .L_selfdestruct_surcharge_done\n" ++
  "  mv t0, x20\n" ++
  "  la t1, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
  runtimeAccessWordToBe20Asm "selfdestruct_origin" "t0" "t1" "t2" "t3" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  ld a0, 576(x20)\n" ++
  "  ld a1, 584(x20)\n" ++
  "  la a2, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  la a5, bal_output_scratch\n" ++
  "  jal ra, balance_at_header_state_root\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_surcharge_done\n" ++
  "  la t0, bal_output_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  bnez t1, .L_selfdestruct_origin_nonzero\n" ++
  "  ld t1, 8(t0)\n" ++
  "  bnez t1, .L_selfdestruct_origin_nonzero\n" ++
  "  ld t1, 16(t0)\n" ++
  "  bnez t1, .L_selfdestruct_origin_nonzero\n" ++
  "  ld t1, 24(t0)\n" ++
  "  beqz t1, .L_selfdestruct_surcharge_done\n" ++
  ".L_selfdestruct_origin_nonzero:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  ld a0, 576(x20)\n" ++
  "  ld a1, 584(x20)\n" ++
  "  la a2, evm_selfdestruct_beneficiary\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  jal ra, account_exists_at_header_state_root\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_surcharge_done\n" ++
  "  la t0, aex_predicate\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .L_selfdestruct_charge_new_account\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  ld a0, 576(x20)\n" ++
  "  ld a1, 584(x20)\n" ++
  "  la a2, evm_selfdestruct_beneficiary\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  jal ra, account_is_empty_at_header_state_root\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_surcharge_done\n" ++
  "  la t0, aie_predicate\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .L_selfdestruct_surcharge_done\n" ++
  ".L_selfdestruct_charge_new_account:\n" ++
  -- nxio8.8 (EIP-8037 state dimension): SELFDESTRUCT to a new (not-alive) beneficiary with a
  -- non-zero originator balance creates the beneficiary account, costing
  -- StateGasCosts.NEW_ACCOUNT = STATE_BYTES_PER_NEW_ACCOUNT(120)*COST_PER_STATE_BYTE(1530) = 183600
  -- in the STATE dimension (spec amsterdam vm/instructions/system.py:660-671), NOT the legacy
  -- 25000 GAS-dim surcharge that this replaces. The GAS-dim cost is only base(5000, dispatch) +
  -- cold(2600, ee21v access gas); the new-account cost moved entirely to the state dimension under
  -- EIP-8037. Mirror charge_state_gas (ChildFrameHandlerTails / Storage.lean): drain
  -- evm_state_gas_left, spill the remainder into the frame gas_left (568(x20)), OOG when both
  -- reservoirs are short; state_gas_used += charge. No refund snapshot -- the spec does not
  -- credit_state_gas_refund for SELFDESTRUCT (the charge is permanent within the frame, like the
  -- 25000 it replaces; the frame-entry 624/632 state-gas snapshot already rolls it back if a parent
  -- reverts the frame's effects).
  "  li t0, 183600\n" ++
  "  la t1, evm_state_gas_left\n  ld t2, 0(t1)\n" ++
  "  bgeu t2, t0, .L_selfdestruct_csg_res\n" ++
  "  sub t3, t0, t2\n  sd x0, 0(t1)\n" ++
  "  ld t2, 568(x20)\n  bltu t2, t3, .exit_outofgas\n" ++
  "  sub t2, t2, t3\n  sd t2, 568(x20)\n  j .L_selfdestruct_csg_used\n" ++
  ".L_selfdestruct_csg_res:\n" ++
  "  sub t2, t2, t0\n  sd t2, 0(t1)\n" ++
  ".L_selfdestruct_csg_used:\n" ++
  "  la t1, evm_state_gas_used\n  ld t2, 0(t1)\n  add t2, t2, t0\n  sd t2, 0(t1)\n" ++
  ".L_selfdestruct_surcharge_done:\n"

/--
Load the origin and beneficiary account RLP payloads needed by the later
SELFDESTRUCT balance-transfer/rewrite step.

The helper runs only when the runtime input carried the account-witness
context. It keeps today's no-witness runtime behavior unchanged by recording a
status and continuing the opcode tail.

Scratch outputs:
  `sdai_status`          : 0 success, 1 no context, 2 header root failure,
                           3 origin lookup failure, 4 beneficiary lookup failure
  `sdai_origin_len`      : raw origin account RLP length on success
  `sdai_beneficiary_len` : raw beneficiary account RLP length on success
  `sdai_origin_rlp` / `sdai_beneficiary_rlp` hold the raw account RLP bytes.
-/
def selfdestructLoadAccountInputsAsm : String :=
  "  la t0, sdai_status\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(t0)\n" ++
  "  la t0, sdai_origin_len\n" ++
  "  sd x0, 0(t0)\n" ++
  "  la t0, sdai_beneficiary_len\n" ++
  "  sd x0, 0(t0)\n" ++
  "  ld t0, 584(x20)\n" ++
  "  beqz t0, .L_selfdestruct_accounts_done\n" ++
  "  mv t0, x20\n" ++
  "  la t1, sdai_origin_address\n" ++
  runtimeAccessWordToBe20Asm "selfdestruct_account_origin" "t0" "t1" "t2" "t3" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  ld a0, 576(x20)\n" ++
  "  ld a1, 584(x20)\n" ++
  "  la a2, sdai_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_accounts_header_fail\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  la a0, sdai_origin_address\n" ++
  "  li a1, 20\n" ++
  "  la a2, sdai_state_root\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  la a5, sdai_origin_rlp\n" ++
  "  la a6, sdai_origin_len\n" ++
  "  jal ra, mpt_lookup_by_key\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_accounts_origin_fail\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  la a0, evm_selfdestruct_beneficiary\n" ++
  "  li a1, 20\n" ++
  "  la a2, sdai_state_root\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  la a5, sdai_beneficiary_rlp\n" ++
  "  la a6, sdai_beneficiary_len\n" ++
  "  jal ra, mpt_lookup_by_key\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_accounts_beneficiary_fail\n" ++
  "  la t0, sdai_status\n" ++
  "  sd x0, 0(t0)\n" ++
  "  j .L_selfdestruct_accounts_done\n" ++
  ".L_selfdestruct_accounts_header_fail:\n" ++
  "  la t0, sdai_status\n" ++
  "  li t1, 2\n" ++
  "  sd t1, 0(t0)\n" ++
  "  j .L_selfdestruct_accounts_done\n" ++
  ".L_selfdestruct_accounts_origin_fail:\n" ++
  "  la t0, sdai_status\n" ++
  "  li t1, 3\n" ++
  "  sd t1, 0(t0)\n" ++
  "  j .L_selfdestruct_accounts_done\n" ++
  ".L_selfdestruct_accounts_beneficiary_fail:\n" ++
  "  la t0, sdai_status\n" ++
  "  li t1, 4\n" ++
  "  sd t1, 0(t0)\n" ++
  ".L_selfdestruct_accounts_done:\n"

/--
Apply the loaded SELFDESTRUCT account RLPs through
`selfdestruct_balance_transfer` when account inputs are available.

This stages the rewritten account RLPs in `sdai_transfer_output` for the
post-state descriptor integration step. It deliberately records a precise
status and continues the existing runtime exit path so no-witness opcode tests
keep their current behavior.

Scratch outputs:
  `sdai_transfer_status`          : 0 success, 1 skipped/no loaded inputs,
                                    2 helper failure
  `sdai_transfer_origin_len`      : rewritten origin account RLP length
  `sdai_transfer_beneficiary_len` : rewritten beneficiary account RLP length
  `sdai_transfer_output`          : helper output buffer
-/
def selfdestructBalanceTransferRuntimeAsm : String :=
  "  la t0, sdai_transfer_status\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(t0)\n" ++
  "  la t0, sdai_transfer_origin_len\n" ++
  "  sd x0, 0(t0)\n" ++
  "  la t0, sdai_transfer_beneficiary_len\n" ++
  "  sd x0, 0(t0)\n" ++
  "  la t0, sdai_status\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .L_selfdestruct_transfer_full\n" ++
  -- status 4 = beneficiary lookup missed because it is a NEW account. The balance
  -- move to the new beneficiary is already applied (recomputed state root matches),
  -- but the spec still emits the EIP-7708 Transfer log to it. The full transfer
  -- staging below needs the beneficiary RLP (absent for a new account), so instead
  -- just clear sdai_transfer_status to let selfdestructEip7708LogRuntimeAsm emit the
  -- log: it reads the transferred amount from the (valid) origin RLP and no-ops on a
  -- zero balance, so this is correct for both funded and empty new-beneficiary cases.
  -- status 1/2/3 (no context / header / origin failure) keep skipping (status stays 1).
  "  li t2, 4\n" ++
  "  bne t1, t2, .L_selfdestruct_transfer_done\n" ++
  "  la t0, sdai_transfer_status\n" ++
  "  sd x0, 0(t0)\n" ++
  "  j .L_selfdestruct_transfer_done\n" ++
  ".L_selfdestruct_transfer_full:\n" ++
  "  la t0, sdai_origin_len\n" ++
  "  ld a1, 0(t0)\n" ++
  "  la t0, sdai_beneficiary_len\n" ++
  "  ld a3, 0(t0)\n" ++
  "  la t0, sdai_origin_address\n" ++
  "  la t1, evm_selfdestruct_beneficiary\n" ++
  "  li t2, 20\n" ++
  "  li t3, 1\n" ++
  ".L_selfdestruct_same_address_loop:\n" ++
  "  lbu t4, 0(t0)\n" ++
  "  lbu t5, 0(t1)\n" ++
  "  bne t4, t5, .L_selfdestruct_same_address_no\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .L_selfdestruct_same_address_loop\n" ++
  "  j .L_selfdestruct_same_address_done\n" ++
  ".L_selfdestruct_same_address_no:\n" ++
  "  li t3, 0\n" ++
  ".L_selfdestruct_same_address_done:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  la a0, sdai_origin_rlp\n" ++
  "  la a2, sdai_beneficiary_rlp\n" ++
  "  mv a4, t3\n" ++
  "  la t0, evm_selfdestruct_created_in_tx\n" ++
  "  ld a5, 0(t0)\n" ++
  "  la a6, sdai_transfer_output\n" ++
  "  jal ra, selfdestruct_balance_transfer\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_transfer_fail\n" ++
  "  la t0, sdai_transfer_output\n" ++
  "  ld t1, 0(t0)\n" ++
  "  la t2, sdai_transfer_origin_len\n" ++
  "  sd t1, 0(t2)\n" ++
  "  ld t1, 8(t0)\n" ++
  "  la t2, sdai_transfer_beneficiary_len\n" ++
  "  sd t1, 0(t2)\n" ++
  "  la t0, sdai_transfer_status\n" ++
  "  sd x0, 0(t0)\n" ++
  "  j .L_selfdestruct_transfer_done\n" ++
  ".L_selfdestruct_transfer_fail:\n" ++
  "  la t0, sdai_transfer_status\n" ++
  "  li t1, 2\n" ++
  "  sd t1, 0(t0)\n" ++
  ".L_selfdestruct_transfer_done:\n"

/--
Append the EIP-7708 synthetic Transfer/Burn log for a successful
SELFDESTRUCT balance transfer.

The runtime already has the pre-transfer origin account RLP, beneficiary,
same-address relation, and created-in-transaction marker. This mirrors
execution-specs:
  * created-in-tx selfdestruct-to-self emits Burn(origin, balance);
  * different beneficiary emits Transfer(origin, beneficiary, balance);
  * zero balance and pre-existing selfdestruct-to-self emit no log.

`evm_selfdestruct_log_status` records 0 success/no-log, 1 skipped because the
account-transfer stage did not run, 2 origin balance parse failure, 3 synthetic
log append failure. -/
def selfdestructEip7708LogRuntimeAsm : String :=
  "  la t0, evm_selfdestruct_log_status\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(t0)\n" ++
  "  la t0, sdai_transfer_status\n" ++
  "  ld t1, 0(t0)\n" ++
  "  bnez t1, .L_selfdestruct_eip7708_done\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  la a0, sdai_origin_rlp\n" ++
  "  la t0, sdai_origin_len\n" ++
  "  ld a1, 0(t0)\n" ++
  "  la a2, evm_selfdestruct_balance_scratch\n" ++
  "  jal ra, account_extract_balance\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_eip7708_balance_fail\n" ++
  "  la t0, evm_selfdestruct_balance_scratch\n" ++
  "  addi t1, t0, 31\n" ++
  "  li t2, 16\n" ++
  ".L_selfdestruct_eip7708_balance_rev:\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  lbu t4, 0(t1)\n" ++
  "  sb t4, 0(t0)\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .L_selfdestruct_eip7708_balance_rev\n" ++
  -- Build stack-word LE forms of the from/to addresses for the EIP-7708 log topics.
  -- sdai_origin_address / evm_selfdestruct_beneficiary are canonical 20-byte BE, but
  -- the receipt log encoder byte-reverses each 32B topic slot (like the CALL value-
  -- transfer log, which passes env.ADDRESS / stack words), so the address must enter
  -- as [20-byte LE][12 zero] to come out canonical right-aligned BE.
  "  la t0, sd_eip7708_from_sw\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, sdai_origin_address; addi t1, t1, 19; li t2, 20\n" ++
  ".L_sd7708_from_le:\n" ++
  "  lbu t4, 0(t1); sb t4, 0(t0); addi t1, t1, -1; addi t0, t0, 1; addi t2, t2, -1; bnez t2, .L_sd7708_from_le\n" ++
  "  la t0, sd_eip7708_to_sw\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, evm_selfdestruct_beneficiary; addi t1, t1, 19; li t2, 20\n" ++
  ".L_sd7708_to_le:\n" ++
  "  lbu t4, 0(t1); sb t4, 0(t0); addi t1, t1, -1; addi t0, t0, 1; addi t2, t2, -1; bnez t2, .L_sd7708_to_le\n" ++
  "  la t0, sdai_origin_address\n" ++
  "  la t1, evm_selfdestruct_beneficiary\n" ++
  "  li t2, 20\n" ++
  "  li t3, 1\n" ++
  ".L_selfdestruct_eip7708_same_loop:\n" ++
  "  lbu t4, 0(t0)\n" ++
  "  lbu t5, 0(t1)\n" ++
  "  bne t4, t5, .L_selfdestruct_eip7708_not_same\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .L_selfdestruct_eip7708_same_loop\n" ++
  "  j .L_selfdestruct_eip7708_same_ready\n" ++
  ".L_selfdestruct_eip7708_not_same:\n" ++
  "  li t3, 0\n" ++
  ".L_selfdestruct_eip7708_same_ready:\n" ++
  "  beqz t3, .L_selfdestruct_eip7708_transfer\n" ++
  "  la t0, evm_selfdestruct_created_in_tx\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .L_selfdestruct_eip7708_success\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  la a0, sd_eip7708_from_sw\n" ++
  "  la a1, evm_selfdestruct_balance_scratch\n" ++
  "  jal ra, eip7708_append_burn_log\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_eip7708_append_fail\n" ++
  "  j .L_selfdestruct_eip7708_success\n" ++
  ".L_selfdestruct_eip7708_transfer:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  la a0, sd_eip7708_from_sw\n" ++
  "  la a1, sd_eip7708_to_sw\n" ++
  "  la a2, evm_selfdestruct_balance_scratch\n" ++
  "  jal ra, eip7708_append_transfer_log\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_eip7708_append_fail\n" ++
  ".L_selfdestruct_eip7708_success:\n" ++
  "  la t0, evm_selfdestruct_log_status\n" ++
  "  sd x0, 0(t0)\n" ++
  "  j .L_selfdestruct_eip7708_done\n" ++
  ".L_selfdestruct_eip7708_balance_fail:\n" ++
  "  la t0, evm_selfdestruct_log_status\n" ++
  "  li t1, 2\n" ++
  "  sd t1, 0(t0)\n" ++
  "  j .L_selfdestruct_eip7708_done\n" ++
  ".L_selfdestruct_eip7708_append_fail:\n" ++
  "  la t0, evm_selfdestruct_log_status\n" ++
  "  li t1, 3\n" ++
  "  sd t1, 0(t0)\n" ++
  ".L_selfdestruct_eip7708_done:\n"

/--
ednoc / i3djw.3: record the SELFDESTRUCT beneficiary's non-storage balance effect so the
all-accounts non-storage FORWARD check (`bal_all_accounts_nonstorage_consistent`, bv_fail=44)
reproduces the BAL's declared beneficiary balance change.

Hooks off `evm_selfdestruct_staged` (NOT `sdai_transfer_status==0`) so it also covers a NEW
beneficiary, whose account lookup fails (`sdai_status=4`) and skips the runtime transfer staging
-- yet the post-state recompute still creates it. transferred = origin pre-balance
(`sdai_origin_rlp`, BE, valid for status 0 or 4); beneficiary pre = its balance if it existed
(`sdai_status==0`) else 0; post = pre + transferred; nonce unchanged (0/0). Zero transfer or
self-destruct-to-self records nothing (the balance-0 self-destruct rows that pass via
conservative-accept stay unaffected). The all-accounts wrapper skips {sender,recipient,coinbase};
`record_nonstorage_effect`/`account_extract_balance`/`u256_add_be` are dispatcher-linked. Saves/
restores the dispatcher's x10/x12 around each helper call (mirrors the eip7708 fragment). -/
def selfdestructBeneficiaryNonstorageAsm : String :=
  "  la t0, evm_selfdestruct_staged; ld t0, 0(t0); beqz t0, .L_sdbn_done\n" ++
  "  la t0, sdai_status; ld t0, 0(t0); beqz t0, .L_sdbn_origin_ok\n" ++
  "  li t1, 4; bne t0, t1, .L_sdbn_done\n" ++
  ".L_sdbn_origin_ok:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd x10, 96(sp); sd x12, 104(sp)\n" ++
  "  la a0, sdai_origin_rlp; la t0, sdai_origin_len; ld a1, 0(t0); addi a2, sp, 64\n" ++
  "  jal ra, account_extract_balance\n" ++
  "  ld t0, 64(sp); ld t1, 72(sp); or t0, t0, t1; ld t1, 80(sp); or t0, t0, t1; ld t1, 88(sp); or t0, t0, t1\n" ++
  "  beqz t0, .L_sdbn_restore\n" ++
  "  la t0, sdai_origin_address; la t1, evm_selfdestruct_beneficiary; li t2, 20\n" ++
  ".L_sdbn_cmp:\n" ++
  "  beqz t2, .L_sdbn_restore\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .L_sdbn_diff\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L_sdbn_cmp\n" ++
  ".L_sdbn_diff:\n" ++
  "  la t0, sdai_status; ld t0, 0(t0); bnez t0, .L_sdbn_pre_zero\n" ++
  "  la a0, sdai_beneficiary_rlp; la t0, sdai_beneficiary_len; ld a1, 0(t0); mv a2, sp\n" ++
  "  jal ra, account_extract_balance\n" ++
  "  j .L_sdbn_have_pre\n" ++
  ".L_sdbn_pre_zero:\n" ++
  "  sd zero, 0(sp); sd zero, 8(sp); sd zero, 16(sp); sd zero, 24(sp)\n" ++
  ".L_sdbn_have_pre:\n" ++
  "  mv a0, sp; addi a1, sp, 64; addi a2, sp, 32\n" ++
  "  jal ra, u256_add_be\n" ++
  "  la a0, evm_selfdestruct_beneficiary; mv a1, sp; addi a2, sp, 32; li a3, 0; li a4, 0\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  ".L_sdbn_restore:\n" ++
  "  ld x10, 96(sp); ld x12, 104(sp); addi sp, sp, 112\n" ++
  ".L_sdbn_done:\n"

/--
Runtime-layout probe for `selfdestructLoadAccountInputsAsm`.

Input is the normal `scripts/pack-bytecode.py` runtime payload. The bytecode
segment is interpreted as a 20-byte SELFDESTRUCT beneficiary address; the
origin address comes from `evm_env`, matching the real runtime opcode path.

Output:
  bytes   0..  8 : load status
  bytes   8.. 16 : origin account RLP length
  bytes  16.. 24 : beneficiary account RLP length
  bytes  24.. 32 : decoded header state-root field length
  bytes  32.. 40 : transfer status
  bytes  40.. 48 : transfer origin result RLP length
  bytes  48.. 56 : transfer beneficiary result RLP length
  bytes  56.. 64 : EIP-7708 log status
  bytes  64..160 : origin account RLP bytes, zero-padded/truncated
  bytes 160..256 : beneficiary account RLP bytes, zero-padded/truncated
-/
def runtimeSelfdestructAccountInputsPrologue : String :=
  emitRuntimeDispatcherSetup ++ "\n" ++
  "  la t0, evm_selfdestruct_created_in_tx\n" ++
  "  sd x0, 0(t0)\n" ++
  "  la t0, evm_selfdestruct_beneficiary\n" ++
  "  li t1, 20\n" ++
  "  mv t2, x21\n" ++
  ".L_rsda_copy_beneficiary:\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .L_rsda_copy_beneficiary\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  la t0, evm_selfdestruct_created_in_tx\n" ++
  "  sd t3, 0(t0)\n" ++
  selfdestructLoadAccountInputsAsm ++
  selfdestructBalanceTransferRuntimeAsm ++
  selfdestructEip7708LogRuntimeAsm ++
  "  li t0, 0xa0010000\n" ++
  "  la t1, sdai_status\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 0(t0)\n" ++
  "  la t1, sdai_origin_len\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 8(t0)\n" ++
  "  la t1, sdai_beneficiary_len\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 16(t0)\n" ++
  "  la t1, hesr_length\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 24(t0)\n" ++
  "  la t1, sdai_transfer_status\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 32(t0)\n" ++
  "  la t1, sdai_transfer_origin_len\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 40(t0)\n" ++
  "  la t1, sdai_transfer_beneficiary_len\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 48(t0)\n" ++
  "  la t1, evm_selfdestruct_log_status\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 56(t0)\n" ++
  "  la t1, sdai_transfer_output\n" ++
  "  ld t2, 0(t1)\n" ++
  "  addi t1, t1, 16\n" ++
  "  bnez t2, .L_rsda_use_transfer_origin\n" ++
  "  la t1, sdai_origin_rlp\n" ++
  ".L_rsda_use_transfer_origin:\n" ++
  "  addi t0, t0, 64\n" ++
  "  li t2, 96\n" ++
  ".L_rsda_copy_origin_rlp:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .L_rsda_copy_origin_rlp\n" ++
  "  la t1, sdai_transfer_output\n" ++
  "  ld t2, 8(t1)\n" ++
  "  addi t1, t1, 128\n" ++
  "  bnez t2, .L_rsda_use_transfer_beneficiary\n" ++
  "  la t1, sdai_beneficiary_rlp\n" ++
  ".L_rsda_use_transfer_beneficiary:\n" ++
  "  li t2, 96\n" ++
  ".L_rsda_copy_beneficiary_rlp:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .L_rsda_copy_beneficiary_rlp\n" ++
  "  j .L_rsda_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  accountAddBalanceFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  selfdestructBalanceTransferFunction ++ "\n" ++
  eip7708SyntheticLogFunctions ++ "\n" ++
  runtimeAccessAccountSeedFunction ++ "\n" ++
  runtimeAccessSeedInitialAccountsFunction ++ "\n" ++
  ".exit_outofgas:\n" ++
  "  j .L_rsda_done\n" ++
  ".L_rsda_done:"

/-- Minimal `.data` section for the SELFDESTRUCT account-input probe. -/
def runtimeSelfdestructAccountInputsDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "evm_stack_low:\n" ++
  "  .zero 256\n" ++
  "evm_stack_top:\n" ++
  ".balign 32\n" ++
  "evm_memory:\n" ++
  "  .zero 0x8000\n" ++
  ".balign 8\n" ++
  "evm_env:\n" ++
  "  .zero 624\n" ++
  ".balign 8\n" ++
  "evm_blob_hashes:\n" ++
  "  .zero 512\n" ++
  ".balign 8\n" ++
  "evm_block_hashes:\n" ++
  "  .zero 8192\n" ++
  ".balign 8\n" ++
  "evm_event_logs:\n" ++
  "  .zero 262144\n" ++   -- 6c7v9: 1024 × 256-byte LOG event descriptors (was 4096 = 16×256)
  eip7708SyntheticLogTopicData ++
  emitPrecompileFrameData ++
  emitSha256Data ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  emitRuntimeAccountWitnessData ++
  ".balign 8\n" ++
  runtimeAccessAccountCountLabel ++ ":\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  runtimeAccessAccountTableLabel ++ ":\n" ++
  "  .zero " ++ toString (runtimeAccessAccountCapacity * runtimeAccessAccountRecordSize) ++ "\n" ++
  runtimeAccessSeedScratchLabel ++ ":\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "evm_selfdestruct_beneficiary:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "evm_selfdestruct_balance_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sd_eip7708_from_sw:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sd_eip7708_to_sw:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "evm_selfdestruct_created_in_tx:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "evm_selfdestruct_log_status:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "evm_selfdestruct_staged:\n" ++
  "  .zero 8\n" ++
  ".balign 16\n" ++
  "lp64_stack:\n" ++
  "  .zero 262144\n" ++
  "lp64_sp_top:\n"

def runtimeSelfdestructAccountInputsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := runtimeSelfdestructAccountInputsPrologue
  dataAsm     := runtimeSelfdestructAccountInputsDataSection
}

/-- Runtime-layout probe for SELFDESTRUCT EIP-7708 log bridging.

Input matches `runtime_selfdestruct_account_inputs`; output is the first
256-byte captured log descriptor, or all zeros when no log is emitted. -/
def runtimeSelfdestructEip7708LogsPrologue : String :=
  emitRuntimeDispatcherSetup ++ "\n" ++
  "  la t0, evm_selfdestruct_created_in_tx\n" ++
  "  sd x0, 0(t0)\n" ++
  "  la t0, evm_event_logs\n" ++
  "  li t1, 512\n" ++
  ".L_rsdl_zero_logs:\n" ++
  "  sd x0, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .L_rsdl_zero_logs\n" ++
  "  sd x0, 472(x20)\n" ++
  "  la t0, evm_selfdestruct_beneficiary\n" ++
  "  li t1, 20\n" ++
  "  mv t2, x21\n" ++
  ".L_rsdl_copy_beneficiary:\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .L_rsdl_copy_beneficiary\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  la t0, evm_selfdestruct_created_in_tx\n" ++
  "  sd t3, 0(t0)\n" ++
  selfdestructLoadAccountInputsAsm ++
  selfdestructBalanceTransferRuntimeAsm ++
  selfdestructEip7708LogRuntimeAsm ++
  "  li t0, 0xa0010000\n" ++
  "  la t1, evm_event_logs\n" ++
  "  li t2, 32\n" ++
  ".L_rsdl_copy_desc:\n" ++
  "  ld t3, 0(t1)\n" ++
  "  sd t3, 0(t0)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .L_rsdl_copy_desc\n" ++
  "  j .L_rsdl_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  accountAddBalanceFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  selfdestructBalanceTransferFunction ++ "\n" ++
  eip7708SyntheticLogFunctions ++ "\n" ++
  runtimeAccessAccountSeedFunction ++ "\n" ++
  runtimeAccessSeedInitialAccountsFunction ++ "\n" ++
  ".exit_outofgas:\n" ++
  "  j .L_rsdl_done\n" ++
  ".L_rsdl_done:"

def runtimeSelfdestructEip7708LogsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := runtimeSelfdestructEip7708LogsPrologue
  dataAsm     := runtimeSelfdestructAccountInputsDataSection
}

end EvmAsm.Codegen
