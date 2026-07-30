/-
  EvmAsm.Codegen.Programs.BlockVerdictContractStage

  Contract-recipient runtime payload staging for the multi-transaction dispatch
  spine (evm-asm-fhsxz.2.4.2.57.11.6.4.1). `stage_runtime_payload`
  (BlockVerdictRuntimePayload.lean) only stages a hardcoded 1-byte `STOP` body
  for EOA recipients. `stage_runtime_payload_code` generalizes it to stage an
  arbitrary recipient bytecode of length L: the runtime-dispatcher input is the
  tightly-packed pack-bytecode layout (scripts/pack-bytecode.py), so every field
  after the bytecode segment shifts by `round8(L) - 8` relative to the STOP case.
  The env-trailer base is `env_base = round8(L) + 80` (for the empty
  calldata/storage/blob/blockhash case); the env words sit at `env_base + word*32`
  in `EvmEnv` order (0 ADDRESS, 1 SELFBALANCE, 2 CALLER, 3 CALLVALUE, 4 ORIGIN,
  5 GASPRICE, 6 COINBASE, 7 TIMESTAMP, 8 NUMBER, 9 PREVRANDAO, 10 GASLIMIT,
  11 BASEFEE, 12 CHAINID), then a 32-byte SLOTNUM word, then the gas/validate/
  is_creation trailer, then the (zero-length here) M31 witness-context lengths.
  For L=1 this reproduces stage_runtime_payload's STOP layout byte-for-byte
  (env_base=88 -> COINBASE@+280, BASEFEE@+440, gas@+536).

  Scope (slice [1/3]): code + env + gas trailer for the empty
  calldata/storage/witness case (storage-less contracts execute correctly).
  Account/storage witness (M31) + CALLER/sender env + calldata are slice [2/3].
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## stage_runtime_payload_code

    Stage a contract recipient's runtime payload with an arbitrary bytecode.

    Calling convention:
      a0 = context record ptr (192-byte simple_transfer/multi_tx_nth_context output;
           reads status@0, gas@40, is_creation@48, value@96, recipient@72)
      a1 = output payload buffer ptr (>= round8(code_len) + storage_count*64 + 584
           bytes, 8-aligned)
      a2 = exec payload ptr (block env source; bv_exec_p value)
      a3 = recipient code ptr
      a4 = recipient code length (bytes)
      a5 = storage preload ptr (storage_count x 64-byte (key:32, value:32) pairs,
           each carrying a slot's ORIGINAL pre-tx value; the dispatcher expands
           these into the STATE_TRACKER persistent log so SLOAD/SSTORE see the
           correct original value for EIP-2200/3529 gas). May be null if count 0.
      a6 = storage preload count

    Returns:
      a0 = 0 ok / 1 unsupported (context status nonzero)

    Leaves CALLER/ORIGIN/GASPRICE/calldata zero — those (plus the M31
    account-witness segment for code lookups of OTHER accounts) are still TODO;
    this covers code + recipient storage + the read env words + gas trailer. -/
def stageRuntimePayloadCodeFunction : String :=
  "stage_runtime_payload_code:\n" ++
  "  addi sp, sp, -72\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a1                    # output payload ptr\n" ++
  "  mv s1, a0                    # context record\n" ++
  "  mv s2, a2                    # exec payload\n" ++
  "  mv s3, a3                    # code ptr\n" ++
  "  mv s4, a4                    # code length\n" ++
  "  mv s6, a5                    # storage preload ptr (count x 64B (key,value))\n" ++
  "  mv s7, a6                    # storage preload count\n" ++
  "  ld t0, 0(s1)                 # context status\n" ++
  "  beqz t0, .Lsrpc_supported\n" ++
  "  li a0, 1\n" ++
  "  j .Lsrpc_ret\n" ++
  ".Lsrpc_supported:\n" ++
  -- cb = round8(code_len); cd_pad = round8(ctx calldata len); co = cb + cd_pad;
  -- env_base = 80 + co + storage_count*64; total = env_base + 504.
  "  addi t0, s4, 7; andi t0, t0, -8     # t0 = cb (padded code length)\n" ++
  "  ld a7, 64(s1)                       # a7 = calldata length (ctx data len)\n" ++
  "  addi t6, a7, 7; andi t6, t6, -8     # t6 = cd_pad (padded calldata length)\n" ++
  "  slli a6, s7, 6                      # a6 = storage bytes = count*64\n" ++
  "  add t1, t0, t6                      # t1 = co = cb + cd_pad\n" ++
  "  add t1, t1, a6; addi t1, t1, 80     # t1 = env_base = 80 + co + count*64\n" ++
  -- 3vc2p.3b: the input-driven dispatcher setup reads the M29 block (blob-base-fee 32 +
  -- blob_hash_count 8 + cur 8 + count 8 + count*32 hashes) BETWEEN the storage preload and
  -- the env trailer. The fixed 56-byte slot (blob-base-fee+blob_hash_count+cur+count) already
  -- sits in env_base; the count*32 HASHES push the env trailer further back, so shift env_base
  -- by m29_stage_count*32. m29_stage_count defaults 0 -> no shift (byte-identical) until the
  -- dispatch site (3vc2p.3b sub-step B) populates the M29 staging globals.
  "  la t5, m28_blob_stage_count; ld t5, 0(t5); slli t5, t5, 5; add t1, t1, t5\n" ++
  "  la t5, m29_stage_count; ld t5, 0(t5); slli t5, t5, 5; add t1, t1, t5\n" ++
  -- 3vc2p.5: publish the env_base OFFSET so dispatch_tx_runtime_code's CALLER/ORIGIN/
  -- GASPRICE/SELFBALANCE staging uses the SAME base instead of the round8(codelen)+80
  -- approximation (which is only correct for empty calldata+storage). Single source of truth.
  "  la t5, srpc_env_base; sd t1, 0(t5)\n" ++
  "  addi t2, t1, 504                    # t2 = total payload bytes\n" ++
  "  addi t2, t2, 7; andi t2, t2, -8\n" ++
  -- Zero [s0, s0+total).
  "  mv t3, s0\n" ++
  ".Lsrpc_zero:\n" ++
  "  beqz t2, .Lsrpc_zero_done\n" ++
  "  sd zero, 0(t3); addi t3, t3, 8; addi t2, t2, -8; j .Lsrpc_zero\n" ++
  ".Lsrpc_zero_done:\n" ++
  -- bytecode length @ +0, code bytes @ +8.
  "  sd s4, 0(s0)\n" ++
  "  addi t3, s0, 8; mv t4, s3; mv t5, s4\n" ++
  ".Lsrpc_copy:\n" ++
  "  beqz t5, .Lsrpc_copy_done\n" ++
  "  lbu t6, 0(t4); sb t6, 0(t3); addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lsrpc_copy\n" ++
  ".Lsrpc_copy_done:\n" ++
  -- calldata-len @ +8+cb = ctx data len; calldata bytes @ +16+cb (from ctx data ptr@56).
  "  add t3, s0, t0               # t3 = s0 + cb\n" ++
  "  ld a7, 64(s1); sd a7, 8(t3)  # calldata-len @ +8+cb\n" ++
  "  addi t3, t3, 16              # t3 = dst = s0 + cb + 16 (calldata bytes)\n" ++
  "  ld t4, 56(s1); mv t5, a7     # src = ctx data ptr, bytes = calldata len\n" ++
  ".Lsrpc_cdcopy:\n" ++
  "  beqz t5, .Lsrpc_cdcopy_done\n" ++
  "  lbu t6, 0(t4); sb t6, 0(t3); addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lsrpc_cdcopy\n" ++
  ".Lsrpc_cdcopy_done:\n" ++
  -- slot_count @ +16+co; storage pairs @ +24+co. (co = cb + cd_pad; recompute.)
  "  add t3, s0, t0               # s0 + cb\n" ++
  "  ld a7, 64(s1); addi t6, a7, 7; andi t6, t6, -8   # cd_pad\n" ++
  "  add t3, t3, t6               # t3 = s0 + co\n" ++
  "  sd s7, 16(t3)                # slot_count @ +16+co\n" ++
  "  addi t3, t3, 24              # t3 = dst = s0 + co + 24 (storage pairs)\n" ++
  "  mv t4, s6; slli t5, s7, 6    # src, bytes = count*64\n" ++
  ".Lsrpc_scopy:\n" ++
  "  beqz t5, .Lsrpc_scopy_done\n" ++
  "  lbu t6, 0(t4); sb t6, 0(t3); addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lsrpc_scopy\n" ++
  ".Lsrpc_scopy_done:\n" ++
  -- 3vc2p.3b: M28+M29 block at storage-end (t3 = s0 + co + 24 + storage*64 after the copy loop).
  -- BLOBBASEFEE occupies the first 32-byte word; then blob_hash_count@+32,
  -- blob_hashes@+40 (count*32), cur@+40+bhc*32, count@+48+bhc*32, hashes@+56+bhc*32.
  "  mv s5, t3\n" ++
  "  addi a0, s2, 520; jal ra, bgv_u64le\n" ++
  "  mv a1, s5; jal ra, amsterdam_blob_gas_price_u256\n" ++
  "  mv t3, s5\n" ++
  -- blob_hash_count @ +32 + blob hashes @ +40.
  "  la t4, m28_blob_stage_count; ld t0, 0(t4); sd t0, 32(t3)\n" ++
  "  addi t4, t3, 40; la t5, m28_blob_stage_table; slli t6, t0, 5\n" ++
  ".Lsrpc_blob:\n" ++
  "  beqz t6, .Lsrpc_blob_done\n" ++
  "  lbu a5, 0(t5); sb a5, 0(t4); addi t5, t5, 1; addi t4, t4, 1; addi t6, t6, -1; j .Lsrpc_blob\n" ++
  ".Lsrpc_blob_done:\n" ++
  -- BLOCKHASH fields shifted by blob_count*32 (t0 = blob_count).
  "  slli t0, t0, 5\n" ++
  "  la t4, m29_stage_cur;   ld t5, 0(t4); add t4, t3, t0; sd t5, 40(t4)\n" ++
  "  la t4, m29_stage_count; ld t6, 0(t4); add t4, t3, t0; sd t6, 48(t4)\n" ++
  "  add t4, t3, t0; addi t4, t4, 56; la t5, m29_stage_table; slli t6, t6, 5\n" ++
  ".Lsrpc_m29:\n" ++
  "  beqz t6, .Lsrpc_m29_done\n" ++
  "  lbu a5, 0(t5); sb a5, 0(t4); addi t5, t5, 1; addi t4, t4, 1; addi t6, t6, -1; j .Lsrpc_m29\n" ++
  ".Lsrpc_m29_done:\n" ++
  -- env words base (now after the M29 block).
  "  la t1, srpc_env_base; ld t1, 0(t1)     # reload env_base after helper calls\n" ++
  "  add s5, s0, t1               # s5 = &env_words (env_base)\n" ++
  -- COINBASE (word 6 -> +192): exec 20-byte canonical address at payload byte 32,
  -- reversed into the low 160 bits of the EVM stack word layout.
  "  addi t3, s2, 32; addi t4, s5, 192; li t5, 0\n" ++
  ".Lsrpc_cb:\n" ++
  "  li t6, 20; beq t5, t6, .Lsrpc_cb_done\n" ++
  "  add a5, t3, t5; lbu a6, 0(a5); li a5, 19; sub a5, a5, t5; add a5, t4, a5; sb a6, 0(a5); addi t5, t5, 1; j .Lsrpc_cb\n" ++
  ".Lsrpc_cb_done:\n" ++
  -- NUMBER (word 8 -> +256) = exec u64 @404; TIMESTAMP (word 7 -> +224) = @428;
  -- PREVRANDAO (word 9 -> +288) = exec Bytes32 @372, reversed from its
  -- canonical big-endian byte order into the low-limb-first EVM stack layout;
  -- GASLIMIT (word 10 -> +320) = @412.
  "  ld t3, 404(s2); sd t3, 256(s5)\n" ++
  "  ld t3, 428(s2); sd t3, 224(s5)\n" ++
  "  addi t3, s2, 372; addi t4, s5, 288; li t5, 0\n" ++
  ".Lsrpc_prevrandao_loop:\n" ++
  "  li t6, 32; beq t5, t6, .Lsrpc_prevrandao_done\n" ++
  "  add a5, t3, t5; lbu a6, 0(a5)\n" ++
  "  li a5, 31; sub a5, a5, t5; add a5, t4, a5; sb a6, 0(a5)\n" ++
  "  addi t5, t5, 1; j .Lsrpc_prevrandao_loop\n" ++
  ".Lsrpc_prevrandao_done:\n" ++
  "  ld t3, 412(s2); sd t3, 320(s5)\n" ++
  -- BASEFEE (word 11 -> +352): 32-byte copy from exec+440.
  "  addi t3, s2, 440\n" ++
  "  ld t4, 0(t3); sd t4, 352(s5); ld t4, 8(t3); sd t4, 360(s5)\n" ++
  "  ld t4, 16(t3); sd t4, 368(s5); ld t4, 24(t3); sd t4, 376(s5)\n" ++
  -- CHAINID (word 12 -> +384): chain_config_valid captured the execution
  -- chain id before contract dispatch. Store it as the low limb of the EVM
  -- stack-word layout, matching the simple-transfer staging path.
  "  la t3, bv_chain_id; ld t4, 0(t3); sd t4, 384(s5)\n" ++
  -- ADDRESS (word 0 -> +0): recipient (ctx+72, 20-byte BE address), converted
  -- to the EVM stack-word layout (low limb first) used by env loads and storage logs.
  "  addi t3, s1, 72; mv t4, s5; li t5, 0\n" ++
  ".Lsrpc_ad:\n" ++
  "  li t6, 20; beq t5, t6, .Lsrpc_ad_done\n" ++
  "  li a5, 19; sub a5, a5, t5; add a5, t3, a5; lbu a6, 0(a5); add a5, t4, t5; sb a6, 0(a5); addi t5, t5, 1; j .Lsrpc_ad\n" ++
  ".Lsrpc_ad_done:\n" ++
  -- CALLVALUE (word 3 -> +96): context value is stored BE in the tx context;
  -- reverse it into the low-limb-first EVM stack-word layout that env loads push.
  "  addi t3, s1, 96; addi t4, s5, 96; li t5, 0\n" ++
  ".Lsrpc_cv:\n" ++
  "  li t6, 32; beq t5, t6, .Lsrpc_cv_done\n" ++
  "  add a5, t3, t5; lbu a6, 0(a5); li a5, 31; sub a5, a5, t5; add a5, t4, a5; sb a6, 0(a5); addi t5, t5, 1; j .Lsrpc_cv\n" ++
  ".Lsrpc_cv_done:\n" ++
  -- EIP-7843 SLOTNUM (trailer word @env_base+416, low limb): the block-header
  -- slot_number (SSZ field 23, u64 LE @exec_payload+532) is authenticated as part
  -- of the reconstructed header hash (BlockHeaderSszToRlp field 23). The
  -- dispatcher copies this word to evm_env+624, which h_SLOTNUM pushes. Read the
  -- u64 byte-wise (LBU): exec_payload = SSZ_BASE+60 is mod-8 = 6, so a direct
  -- 8-byte ld at +532 (mod 8 = 2) would be a misaligned access (traps in the
  -- verified RV64 subset). slot is u64 -> only limb0 (the +416 dword) is nonzero;
  -- the upper 3 limbs stay 0 (payload pre-zeroed). LE source -> LE limb0 directly.
  "  li t3, 0; li t4, 0\n" ++
  ".Lsrpc_slot:\n" ++
  "  li t5, 8; beq t4, t5, .Lsrpc_slot_done\n" ++
  "  add t5, s2, t4; addi t5, t5, 532; lbu t6, 0(t5); slli a5, t4, 3; sll t6, t6, a5; or t3, t3, t6\n" ++
  "  addi t4, t4, 1; j .Lsrpc_slot\n" ++
  ".Lsrpc_slot_done:\n" ++
  "  sd t3, 416(s5)                       # SLOTNUM limb0 = slot_number (u64 LE)\n" ++
  -- Trailer (relative to env_base s5): gas@+448, validate@+456, is_creation@+464,
  -- witness lens@+472/+480/+488 (zero).
  "  ld t3, 40(s1); sd t3, 448(s5)        # gas limit (ctx tx gas)\n" ++
  "  li t3, 1; sd t3, 456(s5)             # validate_tx_gas = 1\n" ++
  "  ld t3, 48(s1); sd t3, 464(s5)        # is_creation\n" ++
  "  li a0, 0\n" ++
  ".Lsrpc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 72\n" ++
  "  ret"

/-- Stage the authenticated account-witness trailer shared by the top-level
    creation and ordinary contract-dispatch routes.  Both routes already use
    `stage_runtime_payload_code` for the common code/calldata/environment
    prefix; this leaf owns only the three witness lengths and their contiguous
    byte ranges at `env_base + 472` onward.

    Calling convention:
      a0 = payload, a1/a2 = header ptr/len, a3/a4 = state ptr/len,
      a5/a6 = codes ptr/len.
    Clobbers t0-t6 conservatively (the current body writes t0-t3); it has no
    result. -/
def stageRuntimePayloadWitnessContextFunction : String :=
  "stage_runtime_payload_witness_context:\n" ++
  "  la t0, srpc_env_base; ld t1, 0(t0); add t0, a0, t1\n" ++
  "  sd a2, 472(t0); sd a4, 480(t0); sd a6, 488(t0)\n" ++
  "  addi t2, t0, 496\n" ++
  "  mv t0, a1; mv t1, a2\n" ++
  ".Lsrpwc_header:\n" ++
  "  beqz t1, .Lsrpwc_state_start\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t2); addi t0, t0, 1; addi t2, t2, 1; addi t1, t1, -1; j .Lsrpwc_header\n" ++
  ".Lsrpwc_state_start:\n" ++
  "  mv t0, a3; mv t1, a4\n" ++
  ".Lsrpwc_state:\n" ++
  "  beqz t1, .Lsrpwc_codes_start\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t2); addi t0, t0, 1; addi t2, t2, 1; addi t1, t1, -1; j .Lsrpwc_state\n" ++
  ".Lsrpwc_codes_start:\n" ++
  "  mv t0, a5; mv t1, a6\n" ++
  ".Lsrpwc_codes:\n" ++
  "  beqz t1, .Lsrpwc_done\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t2); addi t0, t0, 1; addi t2, t2, 1; addi t1, t1, -1; j .Lsrpwc_codes\n" ++
  ".Lsrpwc_done:\n" ++
  "  ret"

/-- `zisk_stage_runtime_payload_code`: layout-validation probe. Builds a
    synthetic context + exec payload + a 5-byte code blob (all in writable
    `.data` scratch), stages the payload, and writes diagnostics to OUTPUT:
      +0  code length read back from payload+0       (expect 5)
      +8  env_base = round8(5)+80 = 88
      +16 first code byte at payload+8               (expect 0x60)
      +24 gas at payload[env_base+448]               (expect 21000 = 0x5208)
      +32 COINBASE low byte at payload[env_base+192] (expect 0xC0)
      +40 ADDRESS low byte at payload[env_base+0]    (expect 0xBB)
      +48 PREVRANDAO low byte at payload[env_base+288] (expect 0x55) -/
def ziskStageRuntimePayloadCodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  -- Synthetic context: status@0=0, gas@40=21000, is_creation@48=0, data_len@64=0,
  -- recipient@72 = 0xAA.., value@96 = 0.
  "  la t0, srpc_ctx\n" ++
  "  sd zero, 0(t0)\n" ++
  "  li t1, 21000; sd t1, 40(t0)\n" ++
  "  sd zero, 48(t0); sd zero, 64(t0); sd zero, 96(t0)\n" ++
  "  li t1, 0xAA; sb t1, 72(t0); li t1, 0xBB; sb t1, 91(t0)\n" ++
  -- Synthetic exec payload: coinbase@32 first byte 0xC0; prev_randao has
  -- canonical high byte 0x44 and low byte 0x55; number@404 = 99.
  "  la t2, srpc_exec\n" ++
  "  li t1, 0xC0; sb t1, 32(t2)\n" ++
  "  li t1, 0x44; sb t1, 372(t2)\n" ++
  "  li t1, 0x55; sb t1, 403(t2)\n" ++
  "  li t1, 99; sd t1, 404(t2)\n" ++
  -- Code blob: PUSH1 0x01 PUSH1 0x02 STOP = 0x60 0x01 0x60 0x02 0x00 (5 bytes).
  "  la t3, srpc_code\n" ++
  "  li t1, 0x60; sb t1, 0(t3); li t1, 0x01; sb t1, 1(t3)\n" ++
  "  li t1, 0x60; sb t1, 2(t3); li t1, 0x02; sb t1, 3(t3); sb zero, 4(t3)\n" ++
  -- Stage into srpc_payload (no storage preload: a5=0, a6=0).
  "  la a0, srpc_ctx; la a1, srpc_payload; la a2, srpc_exec; la a3, srpc_code; li a4, 5\n" ++
  "  li a5, 0; li a6, 0\n" ++
  "  jal ra, stage_runtime_payload_code\n" ++
  -- Diagnostics to OUTPUT 0xa0010000.
  "  li s0, 0xa0010000\n" ++
  "  la t0, srpc_payload\n" ++
  "  ld t1, 0(t0); sd t1, 0(s0)\n" ++
  "  li t1, 88; sd t1, 8(s0)\n" ++
  "  lbu t1, 8(t0); sd t1, 16(s0)\n" ++
  "  li t2, 88; add t2, t0, t2\n" ++
  "  ld t1, 448(t2); sd t1, 24(s0)\n" ++
  "  lbu t1, 192(t2); sd t1, 32(s0)\n" ++
  "  lbu t1, 0(t2); sd t1, 40(s0)\n" ++
  "  lbu t1, 288(t2); sd t1, 48(s0)\n" ++
  "  j .Lsrpcp_done\n" ++
  stageRuntimePayloadCodeFunction ++ "\n" ++
  stageRuntimePayloadWitnessContextFunction ++ "\n" ++
  ".Lsrpcp_done:"

/-- `zisk_stage_runtime_payload_code_m29`: 3vc2p.3b — same synthetic staging as the
    code probe but with m29_stage_count=2 + a 2-hash M29 table, verifying the M29 block
    write + the env_base shift by count*32. codelen=5, no calldata/storage -> co=8,
    storage_end=co+24=32; M29 cur@payload[72], count@[80], hashes@[88]; env_base = 88+64 = 152.
    OUTPUT: +0 srpc_env_base (expect 152); +8 M29 count payload[80] (expect 2);
      +16 M29 cur payload[72] (expect 0x5A); +24 M29 hash0 payload[88] (expect 0x11);
      +32 ADDRESS low byte payload[152] (expect 0xBB); +40 gas payload[152+448] (expect 21000);
      +48 PREVRANDAO low byte payload[152+288] (expect 0x55). -/
def ziskStageRuntimePayloadCodeM29Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, srpc_ctx\n" ++
  "  sd zero, 0(t0)\n" ++
  "  li t1, 21000; sd t1, 40(t0)\n" ++
  "  sd zero, 48(t0); sd zero, 64(t0); sd zero, 96(t0)\n" ++
  "  li t1, 0xAA; sb t1, 72(t0); li t1, 0xBB; sb t1, 91(t0)\n" ++
  "  la t2, srpc_exec\n" ++
  "  li t1, 0xC0; sb t1, 32(t2)\n" ++
  "  li t1, 0x44; sb t1, 372(t2)\n" ++
  "  li t1, 0x55; sb t1, 403(t2)\n" ++
  "  li t1, 99; sd t1, 404(t2)\n" ++
  "  la t3, srpc_code\n" ++
  "  li t1, 0x60; sb t1, 0(t3); li t1, 0x01; sb t1, 1(t3)\n" ++
  "  li t1, 0x60; sb t1, 2(t3); li t1, 0x02; sb t1, 3(t3); sb zero, 4(t3)\n" ++
  -- M29 staging: count=2, cur=0x5A, hash[0] first byte = 0x11.
  "  la t0, m29_stage_count; li t1, 2; sd t1, 0(t0)\n" ++
  "  la t0, m29_stage_cur;   li t1, 0x5A; sd t1, 0(t0)\n" ++
  "  la t0, m29_stage_table; li t1, 0x11; sb t1, 0(t0); li t1, 0x22; sb t1, 32(t0)\n" ++
  "  la a0, srpc_ctx; la a1, srpc_payload; la a2, srpc_exec; la a3, srpc_code; li a4, 5\n" ++
  "  li a5, 0; li a6, 0\n" ++
  "  jal ra, stage_runtime_payload_code\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t1, srpc_env_base; ld t2, 0(t1); sd t2, 0(s0)\n" ++       -- env_base (expect 152)
  "  la t0, srpc_payload\n" ++
  "  ld t1, 80(t0); sd t1, 8(s0)\n" ++                            -- M29 count (expect 2)
  "  lbu t1, 72(t0); sd t1, 16(s0)\n" ++                          -- M29 cur low byte (expect 0x5A)
  "  lbu t1, 88(t0); sd t1, 24(s0)\n" ++                          -- M29 hash0 (expect 0x11)
  "  li t2, 152; add t2, t0, t2\n" ++
  "  lbu t1, 0(t2); sd t1, 32(s0)\n" ++                           -- ADDRESS low byte at env_base (expect 0xBB)
  "  ld t1, 448(t2); sd t1, 40(s0)\n" ++                          -- gas at env_base+448 (expect 21000)
  "  lbu t1, 288(t2); sd t1, 48(s0)\n" ++                          -- PREVRANDAO low byte (expect 0x55)
  "  j .Lsrpcm29_done\n" ++
  stageRuntimePayloadCodeFunction ++ "\n" ++
  stageRuntimePayloadWitnessContextFunction ++ "\n" ++
  ".Lsrpcm29_done:"

def ziskStageRuntimePayloadCodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "srpc_ctx:\n  .zero 192\n" ++
  "srpc_exec:\n  .zero 512\n" ++
  "srpc_code:\n  .zero 64\n" ++
  "srpc_env_base:\n  .zero 8\n" ++
  "m29_stage_cur:\n  .zero 8\n" ++
  "m29_stage_count:\n  .zero 8\n" ++
  "m29_stage_table:\n  .zero 8192\n" ++   -- 3vc2p.3b: M29 recent-blockhash table (256x32; default 0 -> inert)   -- 3vc2p.5: published env_base offset (single source of truth)
  "srpc_payload:\n  .zero 1024\n"

def ziskStageRuntimePayloadCodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStageRuntimePayloadCodePrologue
  dataAsm     := ziskStageRuntimePayloadCodeDataSection
}

def ziskStageRuntimePayloadCodeM29ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStageRuntimePayloadCodeM29Prologue
  dataAsm     := ziskStageRuntimePayloadCodeDataSection
}

/-- `zisk_stage_runtime_payload_code_storage`: storage-segment layout probe.
    Same as above but with one storage preload pair (key byte 0x07, value byte
    0x63), so env_base = round8(5) + 80 + 1*64 = 152. Diagnostics to OUTPUT:
      +0  slot_count read at payload[+16+cb] = payload[+24]   (expect 1)
      +8  storage pair key byte at payload[+24+cb] = payload[+32] (expect 0x07)
      +16 storage pair value byte at payload[+24+cb+32] = payload[+64] (expect 0x63)
      +24 env_base (expect 152)
      +32 gas at payload[env_base+448]                         (expect 21000)
      +40 ADDRESS low byte at payload[env_base+0]              (expect 0xBB) -/
def ziskStageRuntimePayloadCodeStoragePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, srpcs_ctx\n" ++
  "  sd zero, 0(t0)\n" ++
  "  li t1, 21000; sd t1, 40(t0)\n" ++
  "  sd zero, 48(t0); sd zero, 64(t0); sd zero, 96(t0)\n" ++
  "  li t1, 0xAA; sb t1, 72(t0); li t1, 0xBB; sb t1, 91(t0)\n" ++
  "  la t2, srpcs_exec\n" ++
  "  li t1, 0xC0; sb t1, 32(t2)\n" ++
  "  la t3, srpcs_code\n" ++
  "  li t1, 0x60; sb t1, 0(t3); li t1, 0x07; sb t1, 1(t3)\n" ++
  "  li t1, 0x54; sb t1, 2(t3); sb zero, 3(t3)\n" ++   -- PUSH1 0x07 SLOAD STOP
  -- One storage preload pair: key byte0=0x07, value byte0=0x63.
  "  la t4, srpcs_store\n" ++
  "  li t1, 0x07; sb t1, 0(t4)\n" ++
  "  li t1, 0x63; sb t1, 32(t4)\n" ++
  "  la a0, srpcs_ctx; la a1, srpcs_payload; la a2, srpcs_exec; la a3, srpcs_code; li a4, 4\n" ++
  "  la a5, srpcs_store; li a6, 1\n" ++
  "  jal ra, stage_runtime_payload_code\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, srpcs_payload\n" ++
  -- cb = round8(4) = 8. slot_count @ +16+cb = +24; pair @ +24+cb = +32.
  "  ld t1, 24(t0); sd t1, 0(s0)\n" ++
  "  lbu t1, 32(t0); sd t1, 8(s0)\n" ++
  "  lbu t1, 64(t0); sd t1, 16(s0)\n" ++
  "  li t1, 152; sd t1, 24(s0)\n" ++
  "  li t2, 152; add t2, t0, t2\n" ++
  "  ld t1, 448(t2); sd t1, 32(s0)\n" ++
  "  lbu t1, 0(t2); sd t1, 40(s0)\n" ++
  "  j .Lsrpcsp_done\n" ++
  stageRuntimePayloadCodeFunction ++ "\n" ++
  stageRuntimePayloadWitnessContextFunction ++ "\n" ++
  ".Lsrpcsp_done:"

def ziskStageRuntimePayloadCodeStorageDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "srpcs_ctx:\n  .zero 192\n" ++
  "srpcs_exec:\n  .zero 512\n" ++
  "srpcs_code:\n  .zero 64\n" ++
  "srpcs_store:\n  .zero 64\n" ++
  "srpc_env_base:\n  .zero 8\n" ++
  "m29_stage_cur:\n  .zero 8\n" ++
  "m29_stage_count:\n  .zero 8\n" ++
  "m29_stage_table:\n  .zero 8192\n" ++   -- 3vc2p.3b: M29 recent-blockhash table (256x32; default 0 -> inert)   -- 3vc2p.5: published env_base offset
  "srpcs_payload:\n  .zero 1024\n"

def ziskStageRuntimePayloadCodeStorageProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStageRuntimePayloadCodeStoragePrologue
  dataAsm     := ziskStageRuntimePayloadCodeStorageDataSection
}

/-- `zisk_stage_runtime_payload_code_calldata`: calldata-segment layout probe.
    Code len 5, calldata len 4 (0xDE 0xAD 0xBE 0xEF), no storage. cb=8,
    cd_pad=round8(4)=8, co=16, env_base = 80 + 16 + 0 = 96. Diagnostics:
      +0  calldata-len at payload[+8+cb] = payload[+16]   (expect 4)
      +8  calldata byte0 at payload[+16+cb] = payload[+24] (expect 0xDE)
      +16 slot_count at payload[+16+co] = payload[+32]     (expect 0)
      +24 env_base (expect 96)
      +32 gas at payload[env_base+448]                     (expect 21000)
      +40 ADDRESS low byte at payload[env_base+0]          (expect 0xBB) -/
def ziskStageRuntimePayloadCodeCalldataPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, srpcc_ctx\n" ++
  "  sd zero, 0(t0)\n" ++
  "  li t1, 21000; sd t1, 40(t0)\n" ++
  "  sd zero, 48(t0); sd zero, 96(t0)\n" ++
  "  li t1, 0xAA; sb t1, 72(t0); li t1, 0xBB; sb t1, 91(t0)\n" ++
  "  li t1, 4; sd t1, 64(t0)\n" ++          -- ctx data len = 4
  "  la t4, srpcc_cd\n" ++
  "  sd t4, 56(t0)\n" ++                    -- ctx data ptr
  "  li t1, 0xDE; sb t1, 0(t4); li t1, 0xAD; sb t1, 1(t4)\n" ++
  "  li t1, 0xBE; sb t1, 2(t4); li t1, 0xEF; sb t1, 3(t4)\n" ++
  "  la t2, srpcc_exec\n" ++
  "  li t1, 0xC0; sb t1, 32(t2)\n" ++
  "  la t3, srpcc_code\n" ++
  "  li t1, 0x60; sb t1, 0(t3); li t1, 0x01; sb t1, 1(t3)\n" ++
  "  li t1, 0x60; sb t1, 2(t3); li t1, 0x02; sb t1, 3(t3); sb zero, 4(t3)\n" ++
  "  la a0, srpcc_ctx; la a1, srpcc_payload; la a2, srpcc_exec; la a3, srpcc_code; li a4, 5\n" ++
  "  li a5, 0; li a6, 0\n" ++
  "  jal ra, stage_runtime_payload_code\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, srpcc_payload\n" ++
  "  ld t1, 16(t0); sd t1, 0(s0)\n" ++       -- calldata-len @ +8+cb = +16
  "  lbu t1, 24(t0); sd t1, 8(s0)\n" ++      -- calldata byte0 @ +16+cb = +24
  "  ld t1, 32(t0); sd t1, 16(s0)\n" ++      -- slot_count @ +16+co = +32
  "  li t1, 96; sd t1, 24(s0)\n" ++
  "  li t2, 96; add t2, t0, t2\n" ++
  "  ld t1, 448(t2); sd t1, 32(s0)\n" ++
  "  lbu t1, 0(t2); sd t1, 40(s0)\n" ++
  "  j .Lsrpccp_done\n" ++
  stageRuntimePayloadCodeFunction ++ "\n" ++
  stageRuntimePayloadWitnessContextFunction ++ "\n" ++
  ".Lsrpccp_done:"

def ziskStageRuntimePayloadCodeCalldataDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "srpcc_ctx:\n  .zero 192\n" ++
  "srpcc_exec:\n  .zero 512\n" ++
  "srpcc_code:\n  .zero 64\n" ++
  "srpcc_cd:\n  .zero 64\n" ++
  "srpc_env_base:\n  .zero 8\n" ++
  "m29_stage_cur:\n  .zero 8\n" ++
  "m29_stage_count:\n  .zero 8\n" ++
  "m29_stage_table:\n  .zero 8192\n" ++   -- 3vc2p.3b: M29 recent-blockhash table (256x32; default 0 -> inert)   -- 3vc2p.5: published env_base offset
  "srpcc_payload:\n  .zero 1024\n"

def ziskStageRuntimePayloadCodeCalldataProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStageRuntimePayloadCodeCalldataPrologue
  dataAsm     := ziskStageRuntimePayloadCodeCalldataDataSection
}

end EvmAsm.Codegen
