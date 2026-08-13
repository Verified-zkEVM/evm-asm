/-
  EvmAsm.Codegen.Programs.BlockVerdictRuntimePayload

  Bridge between `simple_transfer_tx_context` extraction and the runtime
  dispatcher input ABI (`scripts/pack-bytecode.py` layout). Stages one
  supported transaction's runtime payload into a static scratch buffer so the
  next child bead can call the callable runtime dispatcher over it.

  This bead only *stages and verifies* the payload fields; it does not call the
  dispatcher or consume its output arrays.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.U256

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## stage_runtime_payload

    Stage a `pack-bytecode.py`-compatible runtime payload for one supported
    transaction. The supported class is the simple value transfer to an EOA
    recipient that `simple_transfer_tx_context` already accepts (status 0):
    non-creation, empty calldata/initcode. The recipient EOA has no code, so
    the runtime bytecode is a single `STOP` (`0x00`), the canonical empty-code
    body — safe to dispatch and equivalent to executing empty code.

    The staged payload mirrors the byte format read by
    `emitRuntimeDispatcherSetup` (see `pack-bytecode.py` docstring):

      +0    u64 bytecode length            (= 1, single STOP)
      +8    bytecode bytes (padded to 8)   (0x00)
      +16   u64 calldata length            (= context data len, 0 here)
      +24   calldata bytes                 (none)
      +24   u64 slot_count                 (= 0)
      +32   blob_base_fee, 32-byte word    (from exec payload @440)
      +64   u64 blob_hash_count            (= 0)
      +72   u64 current_block_number       (= 0, BLOCKHASH table empty)
      +80   u64 blockhash_count            (= 0)
      +88   13 simple-env words (416 B)    (COINBASE/TIMESTAMP/NUMBER/
                                            GASLIMIT/BASEFEE staged from exec)
      +504  SLOTNUM word (32 B)            (EIP-7843 slot_number, exec@532)
      +536  u64 gas_limit                  (= context tx gas limit)
      +544  u64 validate_tx_gas flag       (= 1)
      +552  u64 is_creation flag           (= context is_creation, 0 here)
      +560  u64 account-witness header len (= 0, no witness for STOP)
      +568  u64 witness.state len          (= 0)
      +576  u64 witness.codes len          (= 0)
      +584  end of payload

    Env-word slot order (each 32 B, four LE u64 limbs), matching
    `emitRuntimeDispatcherSetup`:
      0 ADDRESS  1 SELFBALANCE  2 CALLER   3 CALLVALUE  4 ORIGIN
      5 GASPRICE 6 COINBASE     7 TIMESTAMP 8 NUMBER     9 PREVRANDAO
      10 GASLIMIT 11 BASEFEE    12 CHAINID

    Calling convention:
      a0 = context record ptr (192-byte `simple_transfer_tx_context` output)
      a1 = output payload buffer ptr (>= 584 bytes, 8-byte aligned)
      a2 = exec payload ptr (block env source; `bv_exec_p` value)

    Returns:
      a0 = status
             0  ok: supported simple transfer staged
             1  unsupported: context status is nonzero (extraction skip/fail)
-/
def stageRuntimePayloadFunction : String :=
  "stage_runtime_payload:\n" ++
  "  addi sp, sp, -32\n" ++   -- 6121j.1: +16 extra slot to save a0(ctx) across the BLOBBASEFEE price call
  "  sd ra, 0(sp); sd s0, 8(sp)\n" ++
  "  mv s0, a1                    # output payload ptr\n" ++
  -- Reject any context the extractor did not fully accept.
  "  ld t0, 0(a0)                 # context status\n" ++
  "  beqz t0, .Lsrp_supported\n" ++
  "  li a0, 1\n" ++
  "  j .Lsrp_ret\n" ++
  ".Lsrp_supported:\n" ++
  -- Zero the whole 584-byte payload (73 dwords) up front; only the nonzero
  -- fields are written below.
  "  mv t1, s0\n" ++
  "  li t2, 73\n" ++
  ".Lsrp_zero_loop:\n" ++
  "  sd zero, 0(t1)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lsrp_zero_loop\n" ++
  -- Bytecode: single STOP (0x00), length 1. The 8-byte zero slot already
  -- holds the 0x00 STOP byte plus padding, so only the length needs writing.
  "  li t0, 1; sd t0, 0(s0)       # bytecode length = 1\n" ++
  -- Calldata: copy the context's data length (0 for a simple transfer; the
  -- extractor rejects non-empty calldata with status 61, so this is 0 here).
  "  ld t0, 64(a0)                # context data len\n" ++
  "  sd t0, 16(s0)                # calldata length\n" ++
  -- Block env words available from the exec payload.
  -- BASEFEE (word 11 -> +88 + 11*32 = +440): 32-byte direct copy from
  -- exec+440 (SSZ LE bytes == stack-word LE limbs).
  "  # #12057 BASEFEE 32B byte-copy (exec+440 may be unaligned)\n" ++
  "  addi t1, a2, 440; addi t3, s0, 440; li t4, 0\n" ++
  ".Lsrp_basefee_loop:\n" ++
  "  li t5, 32; beq t4, t5, .Lsrp_basefee_done\n" ++
  "  add t6, t1, t4; lbu t5, 0(t6)\n" ++
  "  add t6, t3, t4; sb t5, 0(t6)\n" ++
  "  addi t4, t4, 1; j .Lsrp_basefee_loop\n" ++
  ".Lsrp_basefee_done:\n" ++
  -- NUMBER (word 8 -> +344): exec u64 @404.
  "  # #12057 aligned: u64 LE from a2+404 via LBU pack\n  lbu t2, 404(a2)\n  lbu t3, 405(a2); slli t3, t3, 8; or t2, t2, t3\n  lbu t3, 406(a2); slli t3, t3, 16; or t2, t2, t3\n  lbu t3, 407(a2); slli t3, t3, 24; or t2, t2, t3\n  lbu t3, 408(a2); slli t3, t3, 32; or t2, t2, t3\n  lbu t3, 409(a2); slli t3, t3, 40; or t2, t2, t3\n  lbu t3, 410(a2); slli t3, t3, 48; or t2, t2, t3\n  lbu t3, 411(a2); slli t3, t3, 56; or t2, t2, t3\n  sd t2, 344(s0)\n" ++
  -- TIMESTAMP (word 7 -> +312): exec u64 @428.
  "  # #12057 aligned: u64 LE from a2+428 via LBU pack\n  lbu t2, 428(a2)\n  lbu t3, 429(a2); slli t3, t3, 8; or t2, t2, t3\n  lbu t3, 430(a2); slli t3, t3, 16; or t2, t2, t3\n  lbu t3, 431(a2); slli t3, t3, 24; or t2, t2, t3\n  lbu t3, 432(a2); slli t3, t3, 32; or t2, t2, t3\n  lbu t3, 433(a2); slli t3, t3, 40; or t2, t2, t3\n  lbu t3, 434(a2); slli t3, t3, 48; or t2, t2, t3\n  lbu t3, 435(a2); slli t3, t3, 56; or t2, t2, t3\n  sd t2, 312(s0)\n" ++
  -- PREVRANDAO (word 9 -> +376): exec+372 is a canonical Bytes32 (big-endian
  -- integer), while EVM stack words use low limbs first. Reverse all 32 bytes;
  -- a direct copy makes PREVRANDAO byte-swapped for arithmetic consumers.
  "  addi t1, a2, 372; addi t3, s0, 376; li t4, 0\n" ++
  ".Lsrp_prevrandao_loop:\n" ++
  "  li t5, 32; beq t4, t5, .Lsrp_prevrandao_done\n" ++
  "  add t6, t1, t4; lbu t5, 0(t6)\n" ++
  "  li t6, 31; sub t6, t6, t4; add t6, t3, t6; sb t5, 0(t6)\n" ++
  "  addi t4, t4, 1; j .Lsrp_prevrandao_loop\n" ++
  ".Lsrp_prevrandao_done:\n" ++
  -- GASLIMIT (word 10 -> +408): exec u64 @412.
  "  # #12057 aligned: u64 LE from a2+412 via LBU pack\n  lbu t2, 412(a2)\n  lbu t3, 413(a2); slli t3, t3, 8; or t2, t2, t3\n  lbu t3, 414(a2); slli t3, t3, 16; or t2, t2, t3\n  lbu t3, 415(a2); slli t3, t3, 24; or t2, t2, t3\n  lbu t3, 416(a2); slli t3, t3, 32; or t2, t2, t3\n  lbu t3, 417(a2); slli t3, t3, 40; or t2, t2, t3\n  lbu t3, 418(a2); slli t3, t3, 48; or t2, t2, t3\n  lbu t3, 419(a2); slli t3, t3, 56; or t2, t2, t3\n  sd t2, 408(s0)\n" ++
  -- 6121j.1: CHAINID (word 12 -> +472): bv_chain_id (u64, set by chain_config_valid during the
  -- verdict's config validation, BEFORE dispatch). Direct u64 copy like NUMBER/TIMESTAMP/GASLIMIT
  -- above (the handler evm_env_load .chainId reads env+384 the same way). Activates CHAINID for
  -- dispatched self-contained contracts -- previously conservatively rejected (#8782) because the
  -- env word was unstaged so a dispatched contract read CHAINID=0 (false-accept). Now staged with
  -- the real chain id, so the reject is lifted (see BlockVerdictSelfContained .Lbsc_check).
  "  la t1, bv_chain_id; ld t2, 0(t1); sd t2, 472(s0)\n" ++
  -- COINBASE (word 6 -> +280): exec 20-byte canonical address at payload byte 32,
  -- reversed into the low 160 bits of the EVM stack word layout.
  "  addi t1, a2, 32              # exec coinbase ptr\n" ++
  "  addi t3, s0, 280             # dst env word\n" ++
  "  li t4, 0\n" ++
  ".Lsrp_coinbase_loop:\n" ++
  "  li t5, 20; beq t4, t5, .Lsrp_coinbase_done\n" ++
  "  add t6, t1, t4; lbu t5, 0(t6)\n" ++
  "  li t6, 19; sub t6, t6, t4; add t6, t3, t6; sb t5, 0(t6)\n" ++
  "  addi t4, t4, 1; j .Lsrp_coinbase_loop\n" ++
  ".Lsrp_coinbase_done:\n" ++
  -- 6121j.1: BLOBBASEFEE — stage the block blob gas price into the payload blob_base_fee slot @+32
  -- (the dispatcher copies +32 -> evm_env+512, which the BLOBBASEFEE handler reads). Reuse the
  -- verdict's amsterdam_blob_gas_price_u256 (= calculate_blob_gas_price = taylor_exponential(1,
  -- excess_blob_gas, 11684671); co-linked in BlockVerdictV2); excess_blob_gas = SSZ exec field
  -- @exec+520 (bgv_u64le). Save a0 (ctx, read by the trailer below) across the calls; s0 is
  -- callee-saved (preserved by the helper). Previously the slot stayed 0 so a dispatched
  -- BLOBBASEFEE contract read 0 (#8782 rejected it conservatively); now staged with the real price.
  "  sd a0, 16(sp)\n" ++
  "  addi a0, a2, 520; jal ra, bgv_u64le\n" ++                       -- a0 = excess_blob_gas (u64)
  "  addi a1, s0, 32; jal ra, amsterdam_blob_gas_price_u256\n" ++    -- price (u256 BE) -> payload+32 (overflow unreachable for valid blocks)
  "  ld a0, 16(sp)\n" ++                                             -- restore ctx ptr for the trailer
  -- EIP-7843 SLOTNUM (payload word @+504, low limb): block-header slot_number
  -- (SSZ field 23, u64 LE @exec_payload+532) is authenticated as part of the
  -- reconstructed header hash. The dispatcher copies payload+504 -> evm_env+624,
  -- which h_SLOTNUM pushes. Read byte-wise (LBU): exec_payload = SSZ_BASE+60 is
  -- mod-8 = 6, so a direct 8-byte ld at +532 (mod 8 = 2) would be misaligned
  -- (traps in the verified RV64 subset). slot is u64 -> only limb0 (+504) is set;
  -- upper 3 limbs stay 0 (payload pre-zeroed). LE source -> LE limb0 directly.
  "  li t0, 0; li t1, 0\n" ++
  ".Lsrp_slot:\n" ++
  "  li t2, 8; beq t1, t2, .Lsrp_slot_done\n" ++
  "  add t2, a2, t1; addi t2, t2, 532; lbu t3, 0(t2); slli t4, t1, 3; sll t3, t3, t4; or t0, t0, t3\n" ++
  "  addi t1, t1, 1; j .Lsrp_slot\n" ++
  ".Lsrp_slot_done:\n" ++
  "  sd t0, 504(s0)               # SLOTNUM limb0 = slot_number (u64 LE)\n" ++
  -- Transaction gas / control trailer.
  "  ld t0, 40(a0)                # context tx gas limit\n" ++
  "  sd t0, 536(s0)               # gas_limit\n" ++
  "  li t0, 1; sd t0, 544(s0)     # validate_tx_gas = 1\n" ++
  "  ld t0, 48(a0)                # context is_creation\n" ++
  "  sd t0, 552(s0)               # is_creation\n" ++
  -- No account-witness context is needed for the STOP body: header/state/codes
  -- lengths stay zero (already zeroed above), signalling \"no witness\".
  "  li a0, 0\n" ++
  ".Lsrp_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++   -- 6121j.1: matches the -32 frame
  "  ret"

/- Probe input layout (file byte 0 maps to guest INPUT+8, so the probe stores
   the block-verdict globals directly and lays out the exec payload + tx list
   in guest memory).

      +8    tx_list_len
      +16   tx_item_start
      +24   tx_count
      +32   public_keys_len
      +40   tx gas limit override (echoed into context via the extractor)
      +64   fake exec payload (base_fee @ +440 within payload)
      +320  public keys blob
      +640  transaction-list bytes

   Output (written to OUTPUT = 0xa0010000):
      +0    stage status
      +8    staged bytecode length
      +16   staged calldata length
      +24   staged gas flag (validate_tx_gas)
      +32   staged is_creation flag
      +40   staged header len (witness pointer field)
      +48   staged witness.state len
      +56   staged witness.codes len
      +64   staged gas_limit
      +72   context status (for diagnostics)
      +80   PREVRANDAO low byte (env word 9 @ payload+376)
-/
def ziskStageRuntimePayloadPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  addi t0, s0, 64; la t1, bv_exec_p; sd t0, 0(t1)\n" ++
  "  addi t0, s0, 320; la t1, bv_public_keys_ptr; sd t0, 0(t1)\n" ++
  "  ld t0, 32(s0); la t1, bv_public_keys_len; sd t0, 0(t1)\n" ++
  "  addi t0, s0, 640; la t1, bv_tx_list_ptr; sd t0, 0(t1)\n" ++
  "  ld t0, 8(s0); la t1, bv_tx_list_len; sd t0, 0(t1)\n" ++
  "  ld t0, 16(s0); la t1, bv_tx_item_start; sd t0, 0(t1)\n" ++
  "  ld t0, 24(s0); la t1, bv_tx_count; sd t0, 0(t1)\n" ++
  -- Build the per-transaction context record.
  "  li a0, 0xa0020000\n" ++
  "  jal ra, simple_transfer_tx_context\n" ++
  -- Stage the runtime payload from that context + exec payload.
  "  li a0, 0xa0020000\n" ++
  "  li a1, 0xa0030000\n" ++
  "  la t0, bv_exec_p; ld a2, 0(t0)\n" ++
  "  jal ra, stage_runtime_payload\n" ++
  -- Surface verification fields.
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                 # stage status\n" ++
  "  li t1, 0xa0030000            # staged payload\n" ++
  "  ld t2, 0(t1);   sd t2, 8(t0)   # bytecode length\n" ++
  "  ld t2, 16(t1);  sd t2, 16(t0)  # calldata length\n" ++
  "  ld t2, 544(t1); sd t2, 24(t0)  # gas flag\n" ++
  "  ld t2, 552(t1); sd t2, 32(t0)  # is_creation\n" ++
  "  ld t2, 560(t1); sd t2, 40(t0)  # header len\n" ++
  "  ld t2, 568(t1); sd t2, 48(t0)  # witness.state len\n" ++
  "  ld t2, 576(t1); sd t2, 56(t0)  # witness.codes len\n" ++
  "  ld t2, 536(t1); sd t2, 64(t0)  # gas_limit\n" ++
  "  li t3, 0xa0020000; ld t2, 0(t3); sd t2, 72(t0)  # context status\n" ++
  "  lbu t2, 376(t1); sd t2, 80(t0)  # PREVRANDAO low byte\n" ++
  "  j .Lsrpp_done\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  txExtractToAddressFunction ++ "\n" ++
  txExtractValueFunction ++ "\n" ++
  txExtractDataSectionFunction ++ "\n" ++
  simpleTransferTxContextFunction ++ "\n" ++
  bgvU64leFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  amsterdamBlobGasPriceU256Function ++ "\n" ++
  stageRuntimePayloadFunction ++ "\n" ++
  ".Lsrpp_done:"

def ziskStageRuntimePayloadDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bv_exec_p:\n  .zero 8\n" ++
  "bv_tx_list_ptr:\n  .zero 8\n" ++
  "bv_tx_list_len:\n  .zero 8\n" ++
  "bv_tx_count:\n  .zero 8\n" ++
  "bv_tx_item_start:\n  .zero 8\n" ++
  "bv_public_keys_ptr:\n  .zero 8\n" ++
  "bv_public_keys_len:\n  .zero 8\n" ++
  "bv_chain_id:\n  .zero 8\n" ++
  "u256m_acc:\n  .zero 40\n" ++
  "teng_type:\n  .zero 8\n" ++
  "teng_inner_off:\n  .zero 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  blockVerdictSimpleTransferDataSection


end EvmAsm.Codegen
