/-
  EvmAsm.Codegen.Programs.Selfdestruct

  SELFDESTRUCT runtime assembly helpers split out of `Programs.Noop` to keep
  the halt-handler module under the file-size guardrail.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.AccountBalance

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
  "  ld t0, 568(x20)\n" ++
  "  li t1, 25000\n" ++
  "  bltu t0, t1, .exit_outofgas\n" ++
  "  sub t0, t0, t1\n" ++
  "  sd t0, 568(x20)\n" ++
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
  "  bnez t1, .L_selfdestruct_transfer_done\n" ++
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
  "  .zero 4096\n" ++
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
  ".balign 8\n" ++
  "evm_selfdestruct_created_in_tx:\n" ++
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

end EvmAsm.Codegen
