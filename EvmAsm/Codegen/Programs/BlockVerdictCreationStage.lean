/-
  EvmAsm.Codegen.Programs.BlockVerdictCreationStage

  Top-level contract-creation payload staging for block_verdict.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## stage_creation_runtime_payload

    Stage the first conservative top-level creation runtime payload shape.
    The transaction initcode is executable bytecode, not calldata, so this is
    intentionally separate from `stage_runtime_payload_code`, which copies the
    context data section into the calldata segment for normal message calls.

    This slice supports only one-byte STOP initcode. That is the narrow shape
    whose execution does not observe ADDRESS/CALLER/ORIGIN/CALLVALUE, so the
    later integration can run it before the created-address/creator-env
    substrate exists. Broader constructors must stay gated until those fields
    are staged soundly.

    Calling convention:
      a0 = context record ptr (192-byte simple_transfer/multi_tx_nth_context
           output; reads status@0, gas@40, is_creation@48, data ptr@56,
           data len@64, value@96)
      a1 = output payload buffer ptr (>= 592 bytes, 8-byte aligned)
      a2 = exec payload ptr (block env source; bv_exec_p value)

    Returns:
      a0 = status
             0 ok: one-byte STOP creation initcode staged
             1 unsupported: context status is nonzero
             2 unsupported: context is not a creation transaction
             3 unsupported: initcode pointer/length is outside this slice
             4 unsupported: initcode is not exactly STOP

    Payload layout for the supported shape:
      +0    u64 bytecode length            (= 1)
      +8    bytecode bytes                 (= 0x00 STOP, padded)
      +16   u64 calldata length            (= 1; tx.data IS the initcode)
      +24   calldata bytes                 (= 0x00 STOP, padded)
      +32   u64 slot_count                 (= 0)
      +40   blob_base_fee word             (= 0 in this staging-only slice)
      +72   u64 blob_hash_count            (= 0)
      +80   u64 current_block_number       (= 0)
      +88   u64 blockhash_count            (= 0)
      +96   13 simple-env words
      +512  SLOTNUM word                   (EIP-7843 slot_number, exec@532)
      +544  u64 gas_limit                  (= context tx gas limit)
      +552  u64 validate_tx_gas flag       (= 1; see note below)
      +560  u64 is_creation flag           (= 1)
      +568  u64 account-witness header len (= 0)
      +576  u64 witness.state len          (= 0)
      +584  u64 witness.codes len          (= 0)

    `validate_tx_gas` is 1: the dispatcher computes the v0.6.0 creation
    intrinsic (TX_BASE + CREATE_ACCESS + data tokens + initcode words +
    access-list), the calldata floor, the EIP-8037 reservoir split, and the
    prepare_dispatch NEW_ACCOUNT state charge exactly like execution-specs.
    For a creation transaction tx.data is the initcode, so it is staged as the
    dispatcher's calldata for the intrinsic data/initcode-word costs; the
    supported one-byte STOP shape never reads CALLDATA, so execution is
    unaffected.
-/
def stageCreationRuntimePayloadFunction : String :=
  "stage_creation_runtime_payload:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a1                    # output payload ptr\n" ++
  "  mv s1, a0                    # context record\n" ++
  "  mv s2, a2                    # exec payload\n" ++
  "  ld t0, 0(s1)                 # context status\n" ++
  "  beqz t0, .Lscrp_ctx_ok\n" ++
  "  li a0, 1\n" ++
  "  j .Lscrp_ret\n" ++
  ".Lscrp_ctx_ok:\n" ++
  "  ld t0, 48(s1)                # is_creation\n" ++
  "  bnez t0, .Lscrp_creation_ok\n" ++
  "  li a0, 2\n" ++
  "  j .Lscrp_ret\n" ++
  ".Lscrp_creation_ok:\n" ++
  "  ld s3, 64(s1)                # initcode length\n" ++
  "  li t0, 1\n" ++
  "  beq s3, t0, .Lscrp_len_ok\n" ++
  "  li a0, 3\n" ++
  "  j .Lscrp_ret\n" ++
  ".Lscrp_len_ok:\n" ++
  "  ld t0, 56(s1)                # initcode ptr\n" ++
  "  bnez t0, .Lscrp_ptr_ok\n" ++
  "  li a0, 3\n" ++
  "  j .Lscrp_ret\n" ++
  ".Lscrp_ptr_ok:\n" ++
  "  lbu t1, 0(t0)\n" ++
  "  beqz t1, .Lscrp_supported\n" ++
  "  li a0, 4\n" ++
  "  j .Lscrp_ret\n" ++
  ".Lscrp_supported:\n" ++
  -- Zero the fixed 592-byte STOP-shaped payload (74 dwords).
  "  mv t1, s0\n" ++
  "  li t2, 74\n" ++
  ".Lscrp_zero:\n" ++
  "  sd zero, 0(t1)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lscrp_zero\n" ++
  -- bytecode length = 1; bytecode byte is STOP and already zeroed.
  "  li t0, 1; sd t0, 0(s0)\n" ++
  -- calldata length = 1 (tx.data = the initcode); the calldata byte is STOP
  -- and already zeroed. Staged so the dispatcher's validated intrinsic path
  -- prices the creation data tokens and initcode words from tx.data.
  "  li t0, 1; sd t0, 16(s0)\n" ++
  -- Env trailer starts at +96 for one padded bytecode dword and one padded
  -- calldata dword, no storage.
  "  addi t6, s0, 96              # env base\n" ++
  -- COINBASE (word 6 -> +192): exec 20-byte canonical address at payload byte 32,
  -- reversed into the low 160 bits of the EVM stack word layout.
  "  addi t1, s2, 32; addi t2, t6, 192; li t3, 0\n" ++
  ".Lscrp_coinbase:\n" ++
  "  li t4, 20; beq t3, t4, .Lscrp_coinbase_done\n" ++
  "  add t5, t1, t3; lbu t4, 0(t5); li t5, 19; sub t5, t5, t3; add t5, t2, t5; sb t4, 0(t5)\n" ++
  "  addi t3, t3, 1; j .Lscrp_coinbase\n" ++
  ".Lscrp_coinbase_done:\n" ++
  -- NUMBER (word 8), TIMESTAMP (word 7), GASLIMIT (word 10).
  "  ld t1, 404(s2); sd t1, 256(t6)\n" ++
  "  ld t1, 428(s2); sd t1, 224(t6)\n" ++
  "  ld t1, 412(s2); sd t1, 320(t6)\n" ++
  -- BASEFEE (word 11): 32-byte copy from exec+440.
  "  addi t1, s2, 440\n" ++
  "  ld t2, 0(t1); sd t2, 352(t6); ld t2, 8(t1); sd t2, 360(t6)\n" ++
  "  ld t2, 16(t1); sd t2, 368(t6); ld t2, 24(t1); sd t2, 376(t6)\n" ++
  -- CALLVALUE (word 3): context value. STOP does not observe it, but staging
  -- it now keeps the trailer shape aligned with the later broader helper.
  "  addi t1, s1, 96\n" ++
  "  ld t2, 0(t1); sd t2, 96(t6); ld t2, 8(t1); sd t2, 104(t6)\n" ++
  "  ld t2, 16(t1); sd t2, 112(t6); ld t2, 24(t1); sd t2, 120(t6)\n" ++
  -- EIP-7843 SLOTNUM (trailer word @env_base+416, low limb): block-header
  -- slot_number (SSZ field 23, u64 LE @exec_payload+532) is authenticated as part
  -- of the reconstructed header hash. The dispatcher copies this word to
  -- evm_env+624, which h_SLOTNUM pushes. Read byte-wise (LBU): exec_payload =
  -- SSZ_BASE+60 is mod-8 = 6, so a direct 8-byte ld at +532 (mod 8 = 2) would be
  -- misaligned (traps in the verified RV64 subset). slot is u64 -> only limb0
  -- (+416) is set; upper 3 limbs stay 0 (payload pre-zeroed). LE -> LE limb0.
  "  li t1, 0; li t2, 0\n" ++
  ".Lscrp_slot:\n" ++
  "  li t3, 8; beq t2, t3, .Lscrp_slot_done\n" ++
  "  add t3, s2, t2; addi t3, t3, 532; lbu t4, 0(t3); slli t5, t2, 3; sll t4, t4, t5; or t1, t1, t4\n" ++
  "  addi t2, t2, 1; j .Lscrp_slot\n" ++
  ".Lscrp_slot_done:\n" ++
  "  sd t1, 416(t6)               # SLOTNUM limb0 = slot_number (u64 LE)\n" ++
  -- Trailer: gas@+448, validate@+456 = 1, is_creation@+464 = 1.
  "  ld t1, 40(s1); sd t1, 448(t6)\n" ++
  "  li t1, 1; sd t1, 456(t6); sd t1, 464(t6)\n" ++
  "  li a0, 0\n" ++
  ".Lscrp_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- `zisk_stage_creation_runtime_payload`: layout probe for the supported
    one-byte STOP creation shape.

    OUTPUT:
      +0  stage status                         (expect 0)
      +8  bytecode length                      (expect 1)
      +16 first bytecode byte                  (expect 0)
      +24 calldata length                      (expect 1; tx.data is the initcode)
      +32 is_creation at env_base+464          (expect 1)
      +40 validate_tx_gas at env_base+456      (expect 1)
      +48 gas at env_base+448                  (expect 53000)
      +56 callvalue low limb at env_base+96    (expect 0x42)
      +64 non-creation status                  (expect 2)
      +72 non-STOP status                      (expect 4) -/
def ziskStageCreationRuntimePayloadPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  -- Supported creation context.
  "  la t0, scrp_ctx\n" ++
  "  sd zero, 0(t0)\n" ++
  "  li t1, 53000; sd t1, 40(t0)\n" ++
  "  li t1, 1; sd t1, 48(t0)\n" ++
  "  la t1, scrp_initcode; sd t1, 56(t0)\n" ++
  "  li t1, 1; sd t1, 64(t0)\n" ++
  "  li t1, 0x42; sd t1, 96(t0)\n" ++
  -- Synthetic exec payload: coinbase@32 first byte 0xC0, number/timestamp/gaslimit/basefee.
  "  la t2, scrp_exec\n" ++
  "  li t1, 0xC0; sb t1, 32(t2)\n" ++
  "  li t1, 99; sd t1, 404(t2)\n" ++
  "  li t1, 12345; sd t1, 428(t2)\n" ++
  "  li t1, 30000000; sd t1, 412(t2)\n" ++
  "  li t1, 7; sd t1, 440(t2)\n" ++
  "  la a0, scrp_ctx; la a1, scrp_payload; la a2, scrp_exec\n" ++
  "  jal ra, stage_creation_runtime_payload\n" ++
  "  li s0, 0xa0010000\n" ++
  "  sd a0, 0(s0)\n" ++
  "  la t0, scrp_payload\n" ++
  "  ld t1, 0(t0); sd t1, 8(s0)\n" ++
  "  lbu t1, 8(t0); sd t1, 16(s0)\n" ++
  "  ld t1, 16(t0); sd t1, 24(s0)\n" ++
  "  li t2, 96; add t2, t0, t2\n" ++
  "  ld t1, 464(t2); sd t1, 32(s0)\n" ++
  "  ld t1, 456(t2); sd t1, 40(s0)\n" ++
  "  ld t1, 448(t2); sd t1, 48(s0)\n" ++
  "  ld t1, 96(t2); sd t1, 56(s0)\n" ++
  -- Negative: same STOP payload, but not a creation transaction.
  "  la t0, scrp_bad_ctx\n" ++
  "  sd zero, 0(t0)\n" ++
  "  li t1, 53000; sd t1, 40(t0)\n" ++
  "  sd zero, 48(t0)\n" ++
  "  la t1, scrp_initcode; sd t1, 56(t0)\n" ++
  "  li t1, 1; sd t1, 64(t0)\n" ++
  "  la a0, scrp_bad_ctx; la a1, scrp_bad_payload; la a2, scrp_exec\n" ++
  "  jal ra, stage_creation_runtime_payload\n" ++
  "  sd a0, 64(s0)\n" ++
  -- Negative: creation transaction, but initcode byte is not STOP.
  "  la t0, scrp_bad_ctx\n" ++
  "  li t1, 1; sd t1, 48(t0)\n" ++
  "  la t1, scrp_bad_initcode; sd t1, 56(t0)\n" ++
  "  la a0, scrp_bad_ctx; la a1, scrp_bad_payload; la a2, scrp_exec\n" ++
  "  jal ra, stage_creation_runtime_payload\n" ++
  "  sd a0, 72(s0)\n" ++
  "  j .Lscrpp_done\n" ++
  stageCreationRuntimePayloadFunction ++ "\n" ++
  ".Lscrpp_done:"

def ziskStageCreationRuntimePayloadDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "scrp_ctx:\n  .zero 192\n" ++
  "scrp_bad_ctx:\n  .zero 192\n" ++
  "scrp_exec:\n  .zero 512\n" ++
  "scrp_initcode:\n  .byte 0\n" ++
  ".balign 8\n" ++
  "scrp_bad_initcode:\n  .byte 0x01\n" ++
  ".balign 8\n" ++
  "scrp_payload:\n  .zero 1024\n" ++
  "scrp_bad_payload:\n  .zero 1024\n"

def ziskStageCreationRuntimePayloadProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStageCreationRuntimePayloadPrologue
  dataAsm     := ziskStageCreationRuntimePayloadDataSection
}

/-! ## block_verdict_single_tx_creation_runtime

    Narrow integration helper for top-level creation receipts. It supports
    exactly the staging shape above, runs the staged initcode through the
    callable runtime dispatcher, and stores the same one-transaction runtime
    windows as the existing EOA/contract paths. It deliberately leaves receipt
    enforcement disabled; later slices reconcile created-account effects before
    enforcing creation receipts.

    ABI:
      a0 = simple_transfer_tx_context output
      a1 = execution payload ptr

    Returns:
      a0 = 0 when runtime windows were filled; nonzero staging status otherwise.
-/
def blockVerdictSingleTxCreationRuntimeFunction : String :=
  "block_verdict_single_tx_creation_runtime:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0\n" ++
  "  la t0, bv_creation_ctx_ptr; sd s0, 0(t0)  # stable across runtime dispatcher\n" ++
  "  mv s1, a1\n" ++
  "  la a1, bv_runtime_payload\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, stage_creation_runtime_payload\n" ++
  "  bnez a0, .Lbvcr_ret\n" ++
  "  ld s2, 48(s0)               # save is_creation before dispatcher clobbers caller state\n" ++
  "  la t4, runtime_dispatcher_input_ptr; la t5, bv_runtime_payload; addi t5, t5, 8; sd t5, 0(t4)\n" ++
  "  jal ra, runtime_dispatcher_call\n" ++
  "  la t4, runtime_dispatcher_caller_sp; ld sp, 0(t4)\n" ++
  "  la t4, runtime_dispatcher_input_ptr; sd zero, 0(t4)\n" ++
  "  jal ra, dispatcher_tx_gas_settle\n" ++
  "  la t4, bv_creation_ctx_ptr; ld s0, 0(t4)  # dispatcher clobbers caller s-registers\n" ++
  "  ld s2, 48(s0)               # reload is_creation (the pre-dispatch save in s2 was clobbered too)\n" ++
  "  mv s3, a2\n" ++
  -- The staged payload runs with validate_tx_gas = 1, so the dispatcher
  -- computed the creation intrinsic / floor / reservoir split / NEW_ACCOUNT
  -- prepare charge itself and dispatcher_tx_gas_settle's a0 is already the
  -- published combined gas+state left (no post-settle constant adjustment).
  "  la t4, bv_runtime_gas_left; sd a0, 0(t4)\n" ++
  "  la t4, bv_runtime_refund_counter; sd a1, 0(t4)\n" ++
  "  snez t0, s3; la t4, bv_tx_status_arr; sd t0, 0(t4)\n" ++
  "  la t4, bv_tx_is_creation_arr; sd s2, 0(t4)\n" ++
  -- Amsterdam EIP-7708: process_create_message transfers value into the child
  -- frame before initcode runs, emitting Transfer(sender, created, value). The
  -- staged top-level creation path has only STOP initcode, so adding the log
  -- before the receipt-window snapshot preserves execution-specs ordering.
  "  beqz s3, .Lbvcr_tl7708_done\n" ++
  "  addi t0, s0, 96; ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2; ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
  "  beqz t1, .Lbvcr_tl7708_done\n" ++
  "  ld a0, 24(s0); la a1, bmvmx_sender_addr; jal ra, address_from_pubkey\n" ++
  "  la a0, bmvmx_sender_addr; la t0, sttc_nonce; ld a1, 0(t0); la a2, bv_create_addr; jal ra, address_compute_create\n" ++
  "  addi sp, sp, -16\n  sd x20, 0(sp)\n" ++
  "  la t0, eip7708_tl_from32\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, bmvmx_sender_addr; addi t1, t1, 19; mv t2, t0; li t3, 20\n" ++
  ".Lbvcr_tl_from:\n  beqz t3, .Lbvcr_tl_from_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbvcr_tl_from\n" ++
  ".Lbvcr_tl_from_d:\n" ++
  "  la t0, eip7708_tl_to32\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, bv_create_addr; addi t1, t1, 19; mv t2, t0; li t3, 20\n" ++
  ".Lbvcr_tl_to:\n  beqz t3, .Lbvcr_tl_to_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbvcr_tl_to\n" ++
  ".Lbvcr_tl_to_d:\n" ++
  "  la t0, eip7708_tl_val32\n  addi t1, s0, 127; mv t2, t0; li t3, 32\n" ++
  ".Lbvcr_tl_val:\n  beqz t3, .Lbvcr_tl_val_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbvcr_tl_val\n" ++
  ".Lbvcr_tl_val_d:\n" ++
  "  la x20, evm_env\n  la a0, eip7708_tl_from32\n  la a1, eip7708_tl_to32\n  la a2, eip7708_tl_val32\n" ++
  "  jal ra, eip7708_append_transfer_log\n" ++
  "  ld x20, 0(sp)\n  addi sp, sp, 16\n" ++
  ".Lbvcr_tl7708_done:\n" ++
  "  jal ra, block_log_window_snapshot\n" ++

  -- Successful top-level STOP creation makes the created account alive with
  -- the transaction value as balance and nonce 1. Record that execution-derived
  -- effect before BAL all-account non-storage comparisons run.
  "  beqz s3, .Lbvcr_created_effect_done\n" ++
  "  la a0, bv_create_addr\n" ++
  "  la a1, nse_zero_bal\n" ++
  "  la a2, bv_creation_ctx_ptr; ld a2, 0(a2); addi a2, a2, 96\n" ++
  "  li a3, 0\n" ++
  "  li a4, 1\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  ".Lbvcr_created_effect_done:\n" ++
  "  la t4, bv_last_log_start; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 0(t4)\n" ++
  "  la t4, bv_last_log_count; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 8(t4)\n" ++
  "  la t4, runtime_tx_calldata_floor; ld t5, 0(t4)\n" ++
  "  la t4, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  li a0, 0; jal ra, dispatcher_capture_exec_state_gas\n" ++
  "  la t4, bvgr_runtime_gas_left_ptr; la t5, bv_runtime_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_refund_counter_ptr; la t5, bv_runtime_refund_counter; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_calldata_floor_ptr; la t5, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  li t5, 1; la t4, bvgr_runtime_count; sd t5, 0(t4)\n" ++
  "  li t5, 6; la t4, bv_receipts_completeness_shape; sd t5, 0(t4)\n" ++
  "  li t5, 1; la t4, bv_receipts_enforce_enabled; sd t5, 0(t4)\n" ++
  "  li a0, 0\n" ++
  ".Lbvcr_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

end EvmAsm.Codegen
