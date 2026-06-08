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
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer

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
  -- blob/blockhash length fields stay 0 (already zeroed). env words base.
  "  add s5, s0, t1               # s5 = &env_words (env_base)\n" ++
  -- COINBASE (word 6 -> +192): exec 20-byte address @32, low-aligned.
  "  addi t3, s2, 32; addi t4, s5, 192; li t5, 0\n" ++
  ".Lsrpc_cb:\n" ++
  "  li t6, 20; beq t5, t6, .Lsrpc_cb_done\n" ++
  "  add a5, t3, t5; lbu a6, 0(a5); add a5, t4, t5; sb a6, 0(a5); addi t5, t5, 1; j .Lsrpc_cb\n" ++
  ".Lsrpc_cb_done:\n" ++
  -- NUMBER (word 8 -> +256) = exec u64 @404; TIMESTAMP (word 7 -> +224) = @428;
  -- GASLIMIT (word 10 -> +320) = @412.
  "  ld t3, 404(s2); sd t3, 256(s5)\n" ++
  "  ld t3, 428(s2); sd t3, 224(s5)\n" ++
  "  ld t3, 412(s2); sd t3, 320(s5)\n" ++
  -- BASEFEE (word 11 -> +352): 32-byte copy from exec+440.
  "  addi t3, s2, 440\n" ++
  "  ld t4, 0(t3); sd t4, 352(s5); ld t4, 8(t3); sd t4, 360(s5)\n" ++
  "  ld t4, 16(t3); sd t4, 368(s5); ld t4, 24(t3); sd t4, 376(s5)\n" ++
  -- ADDRESS (word 0 -> +0): recipient (ctx+72, 20 bytes), low-aligned.
  "  addi t3, s1, 72; mv t4, s5; li t5, 0\n" ++
  ".Lsrpc_ad:\n" ++
  "  li t6, 20; beq t5, t6, .Lsrpc_ad_done\n" ++
  "  add a5, t3, t5; lbu a6, 0(a5); add a5, t4, t5; sb a6, 0(a5); addi t5, t5, 1; j .Lsrpc_ad\n" ++
  ".Lsrpc_ad_done:\n" ++
  -- CALLVALUE (word 3 -> +96): 32-byte copy of ctx value (ctx+96).
  "  addi t3, s1, 96\n" ++
  "  ld a5, 0(t3); sd a5, 96(s5); ld a5, 8(t3); sd a5, 104(s5)\n" ++
  "  ld a5, 16(t3); sd a5, 112(s5); ld a5, 24(t3); sd a5, 120(s5)\n" ++
  -- Trailer (relative to env_base s5): SLOTNUM@+416 (zero), gas@+448,
  -- validate@+456, is_creation@+464, witness lens@+472/+480/+488 (zero).
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

/-- `zisk_stage_runtime_payload_code`: layout-validation probe. Builds a
    synthetic context + exec payload + a 5-byte code blob (all in writable
    `.data` scratch), stages the payload, and writes diagnostics to OUTPUT:
      +0  code length read back from payload+0       (expect 5)
      +8  env_base = round8(5)+80 = 88
      +16 first code byte at payload+8               (expect 0x60)
      +24 gas at payload[env_base+448]               (expect 21000 = 0x5208)
      +32 COINBASE low byte at payload[env_base+192] (expect 0xC0)
      +40 ADDRESS low byte at payload[env_base+0]    (expect 0xAA) -/
def ziskStageRuntimePayloadCodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  -- Synthetic context: status@0=0, gas@40=21000, is_creation@48=0, data_len@64=0,
  -- recipient@72 = 0xAA.., value@96 = 0.
  "  la t0, srpc_ctx\n" ++
  "  sd zero, 0(t0)\n" ++
  "  li t1, 21000; sd t1, 40(t0)\n" ++
  "  sd zero, 48(t0); sd zero, 64(t0); sd zero, 96(t0)\n" ++
  "  li t1, 0xAA; sb t1, 72(t0)\n" ++
  -- Synthetic exec payload: coinbase@32 first byte 0xC0, number@404 = 99.
  "  la t2, srpc_exec\n" ++
  "  li t1, 0xC0; sb t1, 32(t2)\n" ++
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
  "  j .Lsrpcp_done\n" ++
  stageRuntimePayloadCodeFunction ++ "\n" ++
  ".Lsrpcp_done:"

def ziskStageRuntimePayloadCodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "srpc_ctx:\n  .zero 192\n" ++
  "srpc_exec:\n  .zero 512\n" ++
  "srpc_code:\n  .zero 64\n" ++
  "srpc_payload:\n  .zero 1024\n"

def ziskStageRuntimePayloadCodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStageRuntimePayloadCodePrologue
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
      +40 ADDRESS low byte at payload[env_base+0]              (expect 0xAA) -/
def ziskStageRuntimePayloadCodeStoragePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, srpcs_ctx\n" ++
  "  sd zero, 0(t0)\n" ++
  "  li t1, 21000; sd t1, 40(t0)\n" ++
  "  sd zero, 48(t0); sd zero, 64(t0); sd zero, 96(t0)\n" ++
  "  li t1, 0xAA; sb t1, 72(t0)\n" ++
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
  ".Lsrpcsp_done:"

def ziskStageRuntimePayloadCodeStorageDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "srpcs_ctx:\n  .zero 192\n" ++
  "srpcs_exec:\n  .zero 512\n" ++
  "srpcs_code:\n  .zero 64\n" ++
  "srpcs_store:\n  .zero 64\n" ++
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
      +40 ADDRESS low byte at payload[env_base+0]          (expect 0xAA) -/
def ziskStageRuntimePayloadCodeCalldataPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, srpcc_ctx\n" ++
  "  sd zero, 0(t0)\n" ++
  "  li t1, 21000; sd t1, 40(t0)\n" ++
  "  sd zero, 48(t0); sd zero, 96(t0)\n" ++
  "  li t1, 0xAA; sb t1, 72(t0)\n" ++
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
  ".Lsrpccp_done:"

def ziskStageRuntimePayloadCodeCalldataDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "srpcc_ctx:\n  .zero 192\n" ++
  "srpcc_exec:\n  .zero 512\n" ++
  "srpcc_code:\n  .zero 64\n" ++
  "srpcc_cd:\n  .zero 64\n" ++
  "srpcc_payload:\n  .zero 1024\n"

def ziskStageRuntimePayloadCodeCalldataProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStageRuntimePayloadCodeCalldataPrologue
  dataAsm     := ziskStageRuntimePayloadCodeCalldataDataSection
}

end EvmAsm.Codegen
