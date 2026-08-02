/-
  EvmAsm.Codegen.Programs.BlockVerdictCreationStage

  Top-level contract-creation payload staging for block_verdict.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockVerdictContractStage
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.ArenaCapacities
import EvmAsm.Codegen.GasConstants
import EvmAsm.Codegen.Programs.EIP7708Logs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## stage_creation_runtime_payload

    Legacy one-byte-STOP creation staging.  The live arbitrary-initcode route
    below uses `stage_runtime_payload_code`; it must explicitly split the
    creation frame's empty calldata from the transaction's initcode, which is
    charged as transaction data but executed as frame code.

    This slice supports only one-byte STOP initcode. That is the narrow shape
    whose execution does not observe ADDRESS/CALLER/ORIGIN/CALLVALUE. These
    constraints apply only to this legacy probe: they do not gate production
    creation. `blockVerdictCreationRuntimeFunction` below stages the created
    address and creator environment before dispatching arbitrary initcode.

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
  -- CALLVALUE (word 3): context value is BE, while the payload's EVM words
  -- are LE limbs. This legacy emitted stager is currently non-live, but keep
  -- its ABI correct instead of preserving an emitted raw-BE env seed.
  "  addi t1, s1, 127; addi t2, t6, 96; li t3, 32\n" ++
  ".Lscrpp_callvalue_rev:\n" ++
  "  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; bnez t3, .Lscrpp_callvalue_rev\n" ++
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

/-! ## block_verdict_creation_runtime

    Formerly known as `block_verdict_single_tx_creation_runtime`.

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

    The former `single_tx` name was misleading — the MULTI-tx path calls it too.
    There are eight call sites (GH #10663):

    | site | |
    |---|---|
    | `BlockVerdictCreateCollision.lean:114`  | single-tx creation dispatch |
    | `BlockVerdictMtxRuntime.lean:521`       | **multi-tx mirror** (`:507` carries the parallel
                                                `.Lbv_mtx_creation_access_field` structure) |
    | `EvmDispatchUnits.lean:118,138,145,152,159,165` | six |

    So **"this routine ran" is NOT evidence that the single-tx path ran.** Measured for
    `create_oog_from_eoa_refunds`: dispatch comes from `MtxRuntime:521` (24/24), never from
    `CreateCollision:114` (0/24). During GH #10614 this name made a false premise plausible
    enough to file as an issue (#10662, since closed), and then made two *true* results —
    "these blocks are on the multi-tx path" and "the creation runtime is entered" — look
    mutually contradictory. Hours went into reconciling a conflict only the name created.

    Sibling trap: `dispatch_tx_runtime_code` (`BlockVerdictFunction:847`) is a **different**
    routine, and creation transactions never reach it — they divert at `BlockVerdictFunction:299`
    into `BlockVerdictCreateCollision:23`, which is also why the single-tx check region at
    `:1122` is never entered for them. One diversion explains both non-arrivals.
-/
def blockVerdictCreationRuntimeFunction : String :=
  "block_verdict_creation_runtime:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0\n" ++
  "  la t0, bv_creation_ctx_ptr; sd s0, 0(t0)  # stable across runtime dispatcher\n" ++
  "  mv s1, a1\n" ++
  -- A top-level CREATE runs transaction data as initcode, but its EVM frame
  -- has empty calldata.  The common stager models normal message calls, where
  -- ctx.data is both transaction data and frame calldata, so temporarily hide
  -- the context length while it builds the frame and restore it immediately.
  -- The dispatcher receives the restored ptr/len separately for transaction
  -- intrinsic gas; this keeps CALLDATALOAD/CALLDATACOPY empty while CODECOPY
  -- still sees initcode (execution-specs: vm/instructions/system.py:134-143).
  -- The callable runtime may resolve code for nested CALL/STATICCALL targets.
  -- Reserve room for its authenticated M31 context before the common stager
  -- writes the code/calldata prefix: one padded initcode copy plus the
  -- pre-header, state witness, codes witness, and fixed trailer must fit the
  -- same bounded payload buffer as the normal contract path.
  "  ld t1, 64(s0); addi t1, t1, 7; andi t1, t1, -8\n" ++
  "  la t0, sv_pre_rlp_len; ld t2, 0(t0); add t1, t1, t2\n" ++
  "  la t0, bv_witness_state_len; ld t2, 0(t0); add t1, t1, t2\n" ++
  "  la t0, svf_codes_len; ld t2, 0(t0); add t1, t1, t2\n" ++
  "  addi t1, t1, 584; li t2, " ++ toString (bsrAccountSlotCap * 64 + 65536) ++ "; bgtu t1, t2, .Lbvcr_payload_unsupported\n" ++
  "  ld t0, 64(s0); sd t0, 40(sp); sd zero, 64(s0)\n" ++
  "  la a1, bv_runtime_payload\n" ++
  "  mv a2, s1\n" ++
  "  ld a3, 56(s0); ld a4, 40(sp)\n" ++
  "  li a5, 0; li a6, 0\n" ++
  "  jal ra, stage_runtime_payload_code\n" ++
  "  ld t0, 40(sp); sd t0, 64(s0)\n" ++
  "  la t1, runtime_tx_intrinsic_data_ptr; ld t2, 56(s0); sd t2, 0(t1)\n" ++
  "  la t1, runtime_tx_intrinsic_data_len; ld t2, 64(s0); sd t2, 0(t1)\n" ++
  "  bnez a0, .Lbvcr_ret\n" ++
  -- Match the normal contract-dispatch witness trailer.  The common stager
  -- constructs code, calldata, and env words; nested account/code lookups
  -- additionally require authenticated pre-transaction header/state/code.
  "  la a0, bv_runtime_payload; la a1, sv_pre_rlp_ptr; ld a1, 0(a1); la a2, sv_pre_rlp_len; ld a2, 0(a2); la a3, bv_witness_state_ptr; ld a3, 0(a3); la a4, bv_witness_state_len; ld a4, 0(a4); la a5, svf_codes_ptr; ld a5, 0(a5); la a6, svf_codes_len; ld a6, 0(a6); jal ra, stage_runtime_payload_witness_context\n" ++
  -- `stage_runtime_payload_code` normally takes ADDRESS from ctx+72 (the
  -- transaction recipient).  A top-level CREATE has no recipient: its frame
  -- address is the CREATE(sender, nonce) address already derived by the
  -- verdict path.  Replace just that word before dispatch; this is required
  -- for initcode such as ADDRESS; SELFDESTRUCT to execute in the created
  -- account's context, as `process_create_message` does.
  "  la t0, srpc_env_base; ld t0, 0(t0); la t1, bv_runtime_payload; add t1, t1, t0\n" ++
  "  sd zero, 0(t1); sd zero, 8(t1); sd zero, 16(t1); sd zero, 24(t1)\n" ++
  "  la t2, bv_create_addr; li t3, 0\n" ++
  ".Lbvcr_stage_address:\n" ++
  "  li t4, 20; beq t3, t4, .Lbvcr_stage_address_done\n" ++
  "  li t4, 19; sub t4, t4, t3; add t4, t2, t4; lbu t5, 0(t4); add t4, t1, t3; sb t5, 0(t4); addi t3, t3, 1; j .Lbvcr_stage_address\n" ++
  ".Lbvcr_stage_address_done:\n" ++
  -- A top-level CREATE runs initcode with CALLER == ORIGIN == the
  -- authenticated transaction sender.  The common stager leaves those words
  -- zero for its self-contained recipient slice, so complete the two sender
  -- identity words here before dispatching initcode.
  "  ld a0, 24(s0); beqz a0, .Lbvcr_stage_caller_done\n" ++
  "  la a1, srpc_sender_addr; jal ra, address_from_pubkey\n" ++
  "  la t0, srpc_env_base; ld t0, 0(t0); la t1, bv_runtime_payload; add t1, t1, t0; addi t1, t1, 64\n" ++
  "  la t2, srpc_sender_addr; li t3, 0\n" ++
  ".Lbvcr_stage_caller:\n" ++
  "  li t4, 20; beq t3, t4, .Lbvcr_stage_caller_done\n" ++
  "  li t4, 19; sub t4, t4, t3; add t4, t2, t4; lbu t5, 0(t4); add t4, t1, t3; sb t5, 0(t4); addi t3, t3, 1; j .Lbvcr_stage_caller\n" ++
  ".Lbvcr_stage_caller_done:\n" ++
  "  la t0, srpc_env_base; ld t0, 0(t0); la t1, bv_runtime_payload; add t1, t1, t0; addi t1, t1, 128\n" ++
  "  la t2, srpc_sender_addr; li t3, 0\n" ++
  ".Lbvcr_stage_origin:\n" ++
  "  li t4, 20; beq t3, t4, .Lbvcr_stage_origin_done\n" ++
  "  li t4, 19; sub t4, t4, t3; add t4, t2, t4; lbu t5, 0(t4); add t4, t1, t3; sb t5, 0(t4); addi t3, t3, 1; j .Lbvcr_stage_origin\n" ++
  ".Lbvcr_stage_origin_done:\n" ++
  -- Restore the env base for the adjacent SELFBALANCE staging below.
  "  la t0, srpc_env_base; ld t0, 0(t0); la t1, bv_runtime_payload; add t1, t1, t0\n" ++
  -- `process_create_message` credits the newly-created account with tx.value
  -- before initcode executes.  The context stores that value in canonical BE
  -- order, while h_SELFBALANCE copies env+32 directly onto the LE EVM stack.
  -- Seed this fresh CREATE frame by reversing BE tx.value into the LE env word,
  -- so SELFDESTRUCT and SELFBALANCE observe the spec's live account balance.
  "  addi t1, t1, 32; addi t2, s0, 127; li t3, 32\n" ++
  ".Lbvcr_stage_selfbalance_rev:\n" ++
  "  lbu t4, 0(t2); sb t4, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t3, t3, -1; bnez t3, .Lbvcr_stage_selfbalance_rev\n" ++
  -- A transaction-level CREATE enters initcode in the freshly-created account,
  -- just like `process_create_message`: mark depth zero as a CREATE frame and
  -- publish its address/nonce before the dispatcher starts.  The runtime uses
  -- this marker for EIP-6780 SELFDESTRUCT-to-self accounting; without it an
  -- initcode SELFDESTRUCT treats its own just-created account as pre-existing.
  -- Keep the depth-zero metadata in the same form as `create_frame_descend`.
  -- The nonce-table seed itself must happen after runtime_dispatcher_call's
  -- per-transaction reset; the callable dispatcher performs that guarded seed.
  "  la t0, create_frame_flag; li t1, 1; sd t1, 0(t0)\n" ++
  "  la t0, create_address_be; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t1, bv_create_addr; li t2, 0\n" ++
  ".Lbvcr_create_address_copy:\n" ++
  "  li t3, 20; beq t2, t3, .Lbvcr_create_address_copy_done\n" ++
  "  add t3, t1, t2; lbu t4, 0(t3); add t3, t0, t2; sb t4, 0(t3); addi t2, t2, 1; j .Lbvcr_create_address_copy\n" ++
  ".Lbvcr_create_address_copy_done:\n" ++
  "  la t1, create_address_by_depth; ld t2, 0(t0); sd t2, 0(t1); ld t2, 8(t0); sd t2, 8(t1); ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)\n" ++
  -- `utils/message.py:56-71` derives a top-level creation target and adds it
  -- to `accessed_addresses` before any execution.  Record the same derived
  -- CREATE(sender, nonce) target after it exists and before the dispatcher
  -- begins the corresponding create frame; it remains a read even when
  -- initcode later halts or reverts.
  "  la a0, bv_create_addr; jal ra, account_read_record\n" ++
  "  ld s2, 48(s0)               # save is_creation before dispatcher clobbers caller state\n" ++
  -- Retain only the depth-zero RETURN in a distinct EIP-170-sized fixed
  -- buffer.  Its status distinguishes STOP (0), captured RETURN (1), and an
  -- oversized RETURN (2), so the later deposit step can reject rather than
  -- silently treating an unsupported output as empty code.
  "  la t0, top_level_creation_returndata_status; sd zero, 0(t0)\n" ++
  "  la t0, create_deposit_failed_flag; sd zero, 0(t0)\n" ++
  "  la t0, create_prebalance_lookup_status; sd zero, 0(t0)\n" ++
  "  la t0, system_call_mode; li t1, 2; sd t1, 0(t0)\n" ++
  -- `process_create_message` moves the endowment and emits its EIP-7708
  -- Transfer before initcode executes.  Stage the descriptor now; the
  -- dispatcher's post-reset hook materializes it as log 0 before initcode.
  "  addi t0, s0, 96; ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2; ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
  "  beqz t1, .Lbvcr_tl7708_staged\n" ++
  "  ld a0, 24(s0); la a1, bmvmx_sender_addr; jal ra, address_from_pubkey\n" ++
  "  la a0, bmvmx_sender_addr; la t0, sttc_nonce; ld a1, 0(t0); la a2, bv_create_addr; jal ra, address_compute_create\n" ++
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
  "  li t1, 1; la t0, eip7708_tl_typed_avail; sd t1, 0(t0); la t0, bv_pending_tl_flag; sd t1, 0(t0)\n" ++
  ".Lbvcr_tl7708_staged:\n" ++
  -- The creation path enters the callable dispatcher directly, rather than
  -- through the ordinary post-preparation seam.  Preserve that seam's order:
  -- materialize gas/blob first, capture the body state, then publish the
  -- value-transfer record from the shared post-capture hook.  The CREATE
  -- producer is intentionally not called here: the gas seed below must first
  -- materialise `bv_pending_upfront_sender_post` (execution-specs
  -- `fork.py:1105-1108`) before `move_ether` consumes it.
  -- This capture is
  -- paired with the failure restore below in this routine; the ordinary route
  -- pairs its capture in `Dispatch.lean` with the caller-side restore in
  -- `BlockVerdictDispatchTx.lean`.
  -- Save `ra`: the dispatcher uses its caller return address to resume after
  -- initcode, while both helpers and the mark are calls.
  -- GH #10784 cut 2: `mark_account_created` is a PRE-BODY event.  execution-specs
  -- `process_create_message` marks the target at `vm/interpreter.py:208` — after
  -- `destroy_storage` (:202), before `increment_nonce` (:210) and before
  -- `process_message` (:212) runs the initcode.  The nested CREATE route already
  -- honours that: `create_frame_descend` inserts at descent.  The top-level creation
  -- route enters the callable dispatcher directly (see the seam comment above), so it
  -- had no descent to mark at and was left marking only inside
  -- `create_record_code_effect`, i.e. AFTER the initcode and only on a successful
  -- deposit.  `bv_create_addr` is fully staged by this point (the copy above, and the
  -- `account_read_record` call already consumes it).
  --
  -- Placed AFTER `dispatcher_capture_body_state` while the spec marks BEFORE its
  -- snapshot, and the two are equivalent here for a checkable reason rather than by
  -- assumption: `account_state_created_count` is NOT one of the thirteen fields of
  -- `body_state_snapshot_by_depth` (`BlockVerdictDispatchTx.lean:492-505`, offsets
  -- 0..96), so the restore cannot roll the mark back.  GH #10979 is what made that
  -- true — it removed `account_state_created_checkpoint` — and it matches the spec,
  -- where `copy_tx_state` leaves `created_accounts` shared and `restore_tx_state`
  -- (`state_tracker.py:823-826`) restores only four other fields.
  --
  -- a0-a3 are dead across the two lines below (they set up t4/t5 and the dispatcher
  -- takes its input through `runtime_dispatcher_input_ptr`), and
  -- `code_state_address_set_insert` preserves every s-register, so s0 survives.
  -- Overflow is fail-closed exactly as at the descent site: set
  -- `account_state_overflow`, which both consumers turn into `bv_fail_code = 58`.
  -- The callable dispatcher performs the root sender-debit seed after its
  -- per-transaction setup reset.  Calling that one-shot producer here would
  -- consume the tuple before the live AccountState overlay can survive setup.
  "  addi sp, sp, -16; sd ra, 0(sp); jal ra, dispatcher_capture_body_state\n" ++
  -- GH #10645: destroy_storage before mark (interpreter.py:202 then :208).
  -- LE stack-word key into create_address_word (same form as storage_write_record).
  "  la t0, create_address_word; sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, bv_create_addr; addi t1, t1, 19; mv t2, t0; li t3, 20\n" ++
  ".Lbvcr_ds_rev:\n  beqz t3, .Lbvcr_ds_rev_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbvcr_ds_rev\n" ++
  ".Lbvcr_ds_rev_d:\n  la a0, create_address_word; jal ra, destroy_storage\n" ++
  "  la a0, bv_create_addr; la a1, account_state_created; la a2, account_state_created_count; li a3, " ++ toString accountStateCreatedCapacity ++ "; jal ra, code_state_address_set_insert; beqz a0, .Lbvcr_created_marked\n" ++
  "  la t0, account_state_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lbvcr_created_marked:\n" ++
  -- GH #10944: stage the top-level CREATE endowment for the SHARED recorder.
  --
  -- execution-specs has ONE `move_ether` for calls and creations alike, because
  -- `process_create_message` DELEGATES to `process_message` (`vm/interpreter.py:212`) and the
  -- transfer lives at `:384-390` inside that shared body.  So this route must REACH the
  -- existing recorder, not acquire a second call site.
  --
  -- ⚠️ THE PRE-BALANCE IS AUTHENTICATED, NOT ASSUMED.  `nse_zero_bal` is wrong as an
  -- unconditional default and right only as a lookup RESULT: a deployable pre-existing account
  -- may hold ether.  `account_at_header_state_root_tracked` returns three outcomes and each is
  -- honoured exactly as the nested sites honour them (`CreateFrameDescend`):
  --   * 0 FOUND     -> use the looked-up balance, 32B BE at `create_prebalance_acct+8`;
  --   * 1 ABSENT    -> not in the header state, so the pre-balance IS zero.  An ESTABLISHED
  --                    zero, which the buffer already holds because the lookup zeroes it;
  --   * >=2 MALFORMED -> set `create_prebalance_lookup_status`.  This route ALREADY CONSUMES
  --                    that status (`.Lbvcr_payload_unsupported` below) with nothing on it
  --                    setting the flag; supplying the setter is part of the fix.
  --
  -- Gated on the endowment being nonzero, reusing the test the route already computed for the
  -- EIP-7708 staging above -- the spec gates `move_ether` and `emit_transfer_log` in ONE
  -- conditional structure, so one guard is correct rather than two.
  --
  -- Placed after `dispatcher_capture_body_state`, matching `process_message`'s
  -- snapshot-then-transfer order (`:380` then `:384`), so a failing body discards the record.
  -- GH #11164: the lookup runs for EVERY top-level creation, not only a nonzero-endowment
  -- one, because its result also feeds the post-body final-state record below.  A NONZERO
  -- endowment makes `post != pre`, so the recorded pre value cannot change whether a
  -- `balance_changes` row is emitted; the spurious-row case needs `pre == post`, i.e. a
  -- ZERO endowment -- exactly the case the old gate skipped.  So the endowment test now
  -- guards only the transfer staging, and has moved below the lookup.
  "  la t0, create_prebalance_acct; li t1, 128\n" ++
  ".Lbvcr_endow_zero:\n" ++
  "  sb x0, 0(t0); addi t0, t0, 1; addi t1, t1, -1; bnez t1, .Lbvcr_endow_zero\n" ++
  -- The top-level route has no populated header/witness tuple in `evm_env`:
  -- its header length is zero there.  Query the authenticated parent header and
  -- witnessed state directly, as the sibling top-level BALANCE staging does.
  "  la t5, svf_parent_rlp; ld a0, 0(t5); la t5, svf_parent_rlp_len; ld a1, 0(t5); la a2, bv_create_addr; li a3, 20; la t5, bv_witness_state_ptr; ld a4, 0(t5); la t5, bv_witness_state_len; ld a5, 0(t5); la a6, create_prebalance_acct\n" ++
  "  jal ra, account_at_header_state_root_tracked; mv t6, a0\n" ++
  "  beqz t6, .Lbvcr_endow_pre_ready\n" ++
  "  li t0, 1; beq t6, t0, .Lbvcr_endow_pre_ready\n" ++
  "  li t0, 1; la t1, create_prebalance_lookup_status; sd t0, 0(t1); j .Lbvcr_endow_done\n" ++
  ".Lbvcr_endow_pre_ready:\n" ++
  -- GH #11164: capture the AUTHENTICATED pre-balance (32B BE at `create_prebalance_acct+8`)
  -- into a dedicated buffer NOW, before the dispatcher runs.  `create_prebalance_acct` is
  -- also written by `call_frame_descend` and `create_frame_descend`, both reachable from
  -- `runtime_dispatcher_call` below, so any CALL/CREATE the constructor performs clobbers it
  -- before the post-body final-state record can read it -- a writer between the store and
  -- the read.  `bvcr_created_pre_bal` has no writer inside the dispatcher.
  "  la t0, create_prebalance_acct; addi t0, t0, 8; la t1, bvcr_created_pre_bal; li t2, 32\n" ++
  ".Lbvcr_pre_bal_cp:\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Lbvcr_pre_bal_cp\n" ++
  -- The endowment staging stays gated: a zero endowment means there is no transfer to
  -- record, and the spec gates `move_ether`/`emit_transfer_log` together.
  "  addi t0, s0, 96; ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2; ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
  "  beqz t1, .Lbvcr_endow_done\n" ++
  -- The context record holds the endowment as 32B BE at +96 (the EIP-7708 staging above
  -- reverses it DOWNWARD from +127 into the log's LE stack word, which fixes the direction).
  -- The recorder takes pointers to BE buffers, so copy it forward, unreversed.
  "  addi t0, s0, 96; la t1, bvcr_endow_val_be; li t2, 32\n" ++
  ".Lbvcr_endow_val_cp:\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Lbvcr_endow_val_cp\n" ++
  -- The descriptor is consumed by `dispatcher_seed_pending_value_transfer`
  -- after the sender gas seed and body snapshot.  Calling the producer here
  -- would observe the still-zero sender-post scratch and underflow exactly as
  -- seen on 00078 (execution-specs `interpreter.py:380-390`).
  ".Lbvcr_endow_done:\n" ++
  "  ld ra, 0(sp); addi sp, sp, 16\n" ++
  "  la t4, runtime_dispatcher_input_ptr; la t5, bv_runtime_payload; addi t5, t5, 8; sd t5, 0(t4)\n" ++
  "  jal ra, runtime_dispatcher_call\n" ++
  -- `return`/`revert` clear child-depth markers, while a top-level frame has
  -- no parent return path.  Clear this transaction-local depth-zero marker
  -- here so the next transaction cannot inherit created-in-tx status.
  "  la t0, create_frame_flag; sd zero, 0(t0)\n" ++
  "  la t0, system_call_mode; sd zero, 0(t0)\n" ++
  "  la t4, runtime_dispatcher_caller_sp; ld sp, 0(t4)\n" ++
  "  la t4, runtime_dispatcher_input_ptr; sd zero, 0(t4)\n" ++
  -- Propagate an unauthenticated nested-CREATE pre-balance lookup as this
  -- helper's existing nonzero unsupported result.  The caller's normal
  -- creation-unsupported route reaches the final fail-closed verdict gate.
  "  la t4, create_prebalance_lookup_status; ld t4, 0(t4); bnez t4, .Lbvcr_payload_unsupported\n" ++
  -- `process_create_message` consumes a successful constructor RETURN as the
  -- deployed code before transaction gas settlement.  STOP has empty code and
  -- needs no record; a returned payload is captured in the fixed EIP-170
  -- buffer above.  Any unavailable/invalid/OOG deposit takes this helper's
  -- existing conservative failure edge rather than using an unverified code
  -- hash or silently omitting the state-gas charge.
  "  li t0, 0xa0010000; ld t1, 32(t0); li t2, 1; bne t1, t2, .Lbvcr_deposit_done\n" ++
  -- GH #10938: the SURVIVOR now deposits at depth 0 (`NoopHalt.returnRevertTail`), so this
  -- stage no longer validates, charges or records — it only SETTLES.  Status 1 means the
  -- survivor saw a depth-0 creation RETURN, so fall through to `.Lbvcr_deposit_done`.  Every
  -- other status keeps the pre-existing conservative `.Lbvcr_ret`.
  -- ⛔ THE FAILURE FLAG IS CHECKED FIRST, BEFORE the status cell, because `.Lrr_createcap_*`
  -- writes that status AFTER the survivor published its failure.  Reading the status first would
  -- therefore mask a failed deposit as `status == 1` and settle it as a success.
  --
  -- GH #10938 piece 4: THE STATUS-2 EDGE IS GONE.  Piece 3 had left status 2 meaning "oversized
  -- capture" for a capture it had already deleted, gated on
  -- `topLevelCreationReturndataMaxBytes` (deleted with this change) — a threshold with no buffer behind it, equal to
  -- `maxDeployedCodeSize` only BY COINCIDENCE.  The survivor no longer computes it, so nothing
  -- writes 2 and this edge became unreachable.  The oversized-code case it existed for reaches
  -- this same exception arm by the authoritative route instead: the deposit validator rejects
  -- `len(code) > MAX_CODE_SIZE`, diverts through `.Lrr_crinv_*`, and sets
  -- `create_deposit_failed_flag`, which the line above reads FIRST.  One limit, one enforcer,
  -- and the two constants are now free to diverge.
  "  la t0, create_deposit_failed_flag; ld t1, 0(t0); bnez t1, .Lbvcr_deposit_exception\n" ++
  "  la t0, top_level_creation_returndata_status; ld t1, 0(t0); li t2, 1; beq t1, t2, .Lbvcr_deposit_done\n" ++
  "  j .Lbvcr_ret\n" ++
  -- GH #10938: the stage's deposit PROCESSING is gone — validator, hash gas, code-deposit
  -- state gas, `create_record_code_effect` and the created-account publication all now run
  -- once, in the survivor, at every depth (`vm/interpreter.py:215-241` is one depth-agnostic
  -- block reached through the `process_message` delegation at `:212`).  Keeping them here as
  -- well double-charged code-deposit state gas on every row that reached this point, which
  -- is an OVER-charge and rejects a valid block.  What remains below is settlement and the
  -- exception edge, for which the survivor has no counterpart.
  -- `process_create_message` treats an invalid returned code (or a deposit
  -- charge OOG) as an ExceptionalHalt of the top-level CREATE, not as an
  -- unsupported execution shape: it restores the creation snapshot, burns
  -- remaining regular gas, refills frame state gas, and emits a failed receipt.
  -- The callable dispatcher has already completed the initcode successfully,
  -- so reproduce that post-deposit exception before the common settlement
  -- trailer.  This mirrors the depth-zero abort cleanup in block_verdict:
  -- execution effects/logs are rolled back to the pre-dispatch snapshots while
  -- the access rows are TRUNCATED to the pre-dispatch snapshot (GH #10654).
  ".Lbvcr_deposit_exception:\n" ++
  "  la t0, evm_env; sd zero, 568(t0); sd zero, 472(t0)\n" ++
  "  la t0, evm_log_data_used; sd zero, 0(t0); la t0, evm_log_data_overflow; sd zero, 0(t0)\n" ++
  -- Roll back every body-written arena to the shared pre-dispatch mark.  In
  -- particular this deliberately leaves the read sets intact: the spec's
  -- `restore_tx_state` restores writes but preserves reads.
  "  jal ra, dispatcher_restore_body_state\n" ++
  ".Lbvcr_deposit_exception_settle:\n" ++
  "  li t0, 0xa0010000; li t1, 6; sd t1, 32(t0)\n" ++
  ".Lbvcr_deposit_done:\n" ++
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
  -- `process_message` restores the transaction snapshot after an initcode
  -- REVERT/exception (`vm/interpreter.py:429`), not only after a code-deposit
  -- failure.  The top-level CREATE wrapper receives that status from the
  -- shared settlement fold, so restore the captured body state here before
  -- publishing any receipt/effect data.  In particular this replays the
  -- storage-writes undo journal captured by `dispatcher_capture_body_state`;
  -- without it, a reverted constructor's SSTORE rows survive into the BAL.
  "  bnez a2, .Lbvcr_body_state_kept\n" ++
  "  jal ra, dispatcher_restore_body_state\n" ++
  -- Keep the transaction-level discard explicit at the top-level boundary as
  -- well.  The wrapper can be entered by both single- and multi-transaction
  -- callers, and neither caller may promote a failed constructor's leftover
  -- tx map on its next incorporation (`fork.py:832,879-881`).
  "  jal ra, write_sets_discard_tx\n" ++
  ".Lbvcr_body_state_kept:\n" ++
  "  snez t0, s3; la t4, bv_tx_status_arr; sd t0, 0(t4)\n" ++
  "  la t4, bv_tx_is_creation_arr; sd s2, 0(t4)\n" ++
  -- A failed top-level creation rolls back all logs, including the staged
  -- endowment Transfer re-emitted before initcode.  Match the normal
  -- top-level dispatch path before taking this transaction's log snapshot.
  "  bnez s3, .Lbvcr_tl7708_snapshot\n" ++
  "  la t0, evm_env; sd x0, 472(t0)\n" ++
  ".Lbvcr_tl7708_snapshot:\n" ++
  "  jal ra, block_log_window_snapshot\n" ++

  -- A successful top-level creation normally leaves the new account alive with
  -- the transaction value and its running creator nonce. EIP-6780 is the
  -- exception: a constructor can SELFDESTRUCT its own just-created account,
  -- and the dispatcher records that deferred deletion in `account_state_delete`
  -- before returning here. execution-specs clears that account before
  -- `incorporate_tx_into_block` derives the BAL, so publishing the nonce after
  -- the dispatcher would resurrect an account whose final fields are all zero.
  --
  -- Do not use `evm_selfdestruct_created_in_tx` here: it is reset only at the
  -- next SELFDESTRUCT and is not a transaction-final membership query. The
  -- active +24 flag in the address-keyed delete set is the durable deferred-
  -- delete fact. A malformed count deliberately falls through to the
  -- established publication path rather than suppressing an effect.
  "  beqz s3, .Lbvcr_created_effect_done\n" ++
  "  la t0, account_state_delete_count; ld t1, 0(t0); li t2, " ++ toString accountStateDeleteCapacity ++ "; bgtu t1, t2, .Lbvcr_created_effect_live; li t2, 0; la t3, account_state_delete\n" ++
  ".Lbvcr_created_effect_delete_scan:\n" ++
  "  bgeu t2, t1, .Lbvcr_created_effect_live; ld t4, 24(t3); beqz t4, .Lbvcr_created_effect_delete_next; li t4, 0\n" ++
  ".Lbvcr_created_effect_delete_cmp:\n" ++
  "  li t5, 20; beq t4, t5, .Lbvcr_created_effect_done; la t5, bv_create_addr; add t5, t5, t4; lbu t6, 0(t5); add t5, t3, t4; lbu t5, 0(t5); bne t6, t5, .Lbvcr_created_effect_delete_next; addi t4, t4, 1; j .Lbvcr_created_effect_delete_cmp\n" ++
  ".Lbvcr_created_effect_delete_next:\n" ++
  "  addi t3, t3, 32; addi t2, t2, 1; j .Lbvcr_created_effect_delete_scan\n" ++
  ".Lbvcr_created_effect_live:\n" ++
  -- `update_builder_from_tx` compares the final transaction account state,
  -- not the original endowment.  The dispatcher has returned to the live
  -- depth-zero environment, whose LE balance word at +32 was updated by every
  -- constructor value movement.  Reverse it into the BE nonstorage ABI here;
  -- do not read either post-dispatch overlay, because both have been reset by
  -- this boundary.
  "  la t0, evm_env; addi t0, t0, 63; la t1, nse_create_post_bal; li t2, 32\n" ++
  ".Lbvcr_created_final_balance:\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Lbvcr_created_final_balance\n" ++
  -- The initcode may have performed CREATE/CREATE2 attempts.  Its creator
  -- nonce is therefore the running table value, not always EIP-161's initial
  -- nonce 1; use the same lookup as the ordinary top-level creation deposit.
  "  la a0, bv_create_addr\n  jal ra, create_creator_nonce_current\n  mv a4, a0\n" ++
  "  la a0, bv_create_addr\n" ++
  -- GH #11164: the AUTHENTICATED pre-balance, captured before the dispatcher ran.  A
  -- hardcoded `nse_zero_bal` is wrong here for the reason this file already states above
  -- (":485"): a deployable pre-existing account may hold ether, and `balance_changes`
  -- stores only the POST value, so `pre` is used solely for the net-equal filter -- a
  -- hardcoded zero can therefore only emit a row the spec does not (never suppress one).
  "  la a1, bvcr_created_pre_bal\n" ++
  "  la a2, nse_create_post_bal\n" ++
  "  li a3, 0\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  ".Lbvcr_created_effect_done:\n" ++
  "  la t4, bv_last_log_start; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 0(t4)\n" ++
  "  la t4, bv_last_log_count; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 8(t4)\n" ++
  "  la t4, runtime_tx_calldata_floor; ld t5, 0(t4)\n" ++
  "  la t4, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  -- The creation execution/deposit path above is shared by single- and
  -- multi-transaction callers.  Only publication is mode-specific: retain
  -- the existing scalar path for single tx, while the multi-tx adapter asks
  -- us to scatter the identical settled result at its current index.
  "  la t4, bv_creation_output_mode; ld t5, 0(t4); bnez t5, .Lbvcr_mtx_publish\n" ++
  "  li a0, 0; jal ra, dispatcher_capture_exec_state_gas\n" ++
  -- Every terminal transaction route finalizes its one combined EIP-8037
  -- state-gas cell after execution capture and authoritative status are known.
  -- A successful creation keeps its captured execution component; a reverted
  -- creation retains only its intrinsic/auth component.
  "  li a0, 0; snez a1, s3; jal ra, block_verdict_tx_state_gas_inline_finalize\n" ++
  "  la t4, bvgr_runtime_gas_left_ptr; la t5, bv_runtime_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_refund_counter_ptr; la t5, bv_runtime_refund_counter; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_calldata_floor_ptr; la t5, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  li t5, 1; la t4, bvgr_runtime_count; sd t5, 0(t4)\n" ++
  "  li t5, 6; la t4, bv_receipts_completeness_shape; sd t5, 0(t4)\n" ++
  "  li t5, 1; la t4, bv_receipts_enforce_enabled; sd t5, 0(t4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvcr_ret\n" ++
  ".Lbvcr_mtx_publish:\n" ++
  "  la t4, bv_creation_output_index; ld t1, 0(t4); mv a0, t1; jal ra, dispatcher_capture_exec_state_gas\n" ++
  "  la t4, bv_creation_output_index; ld t1, 0(t4)\n" ++
  "  slli t0, t1, 3\n" ++
  "  la t3, bv_mtx_gas_left; add t3, t3, t0; la t4, bv_runtime_gas_left; ld t5, 0(t4); sd t5, 0(t3)\n" ++
  "  la t3, bv_mtx_refund; add t3, t3, t0; la t4, bv_runtime_refund_counter; ld t5, 0(t4); sd t5, 0(t3)\n" ++
  "  la t3, bv_mtx_calldata; add t3, t3, t0; la t4, bv_runtime_calldata_floor; ld t5, 0(t4); sd t5, 0(t3)\n" ++
  "  la t3, bv_tx_status_arr; add t3, t3, t0; snez t5, s3; sd t5, 0(t3)\n" ++
  "  la t3, bv_tx_is_creation_arr; add t3, t3, t0; sd s2, 0(t3)\n" ++
  "  slli t0, t1, 4; la t3, bv_tx_log_window; add t3, t3, t0\n" ++
  "  la t4, bv_last_log_start; ld t5, 0(t4); sd t5, 0(t3); la t4, bv_last_log_count; ld t5, 0(t4); sd t5, 8(t3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvcr_ret\n" ++
  ".Lbvcr_payload_unsupported:\n" ++
  "  li a0, 5\n" ++
  ".Lbvcr_ret:\n" ++
  -- The intrinsic-data override is creation-local.  Clear it on every return
  -- path, including an unsupported staging result before dispatch.
  "  la t0, runtime_tx_intrinsic_data_ptr; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_intrinsic_data_len; sd zero, 0(t0)\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

end EvmAsm.Codegen
