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
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

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
def stageRuntimePayloadCode_prog : Program :=
  [ .ADDI .x2 .x2 (-72 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x11,
    .MV .x9 .x10,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x22 .x15,
    .MV .x23 .x16,
    .LD .x5 .x9 (0 : BitVec 12),
    .BEQ .x5 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.stage_runtime_payload_code + 1184) (GuestAddrs.stage_runtime_payload_code + 80)),
    .ADDI .x5 .x20 (7 : BitVec 12),
    .ANDI .x5 .x5 (-8 : BitVec 12),
    .LD .x17 .x9 (64 : BitVec 12),
    .ADDI .x31 .x17 (7 : BitVec 12),
    .ANDI .x31 .x31 (-8 : BitVec 12),
    .SLLI .x16 .x23 (6 : BitVec 6),
    .ADD .x6 .x5 .x31,
    .ADD .x6 .x6 .x16,
    .ADDI .x6 .x6 (80 : BitVec 12),
    .AUIPC .x30 (laHi GuestAddrs.m28_blob_stage_count (GuestAddrs.stage_runtime_payload_code + 120)),
    .ADDI .x30 .x30 (laLo GuestAddrs.m28_blob_stage_count (GuestAddrs.stage_runtime_payload_code + 120)),
    .LD .x30 .x30 (0 : BitVec 12),
    .SLLI .x30 .x30 (5 : BitVec 6),
    .ADD .x6 .x6 .x30,
    .AUIPC .x30 (laHi GuestAddrs.m29_stage_count (GuestAddrs.stage_runtime_payload_code + 140)),
    .ADDI .x30 .x30 (laLo GuestAddrs.m29_stage_count (GuestAddrs.stage_runtime_payload_code + 140)),
    .LD .x30 .x30 (0 : BitVec 12),
    .SLLI .x30 .x30 (5 : BitVec 6),
    .ADD .x6 .x6 .x30,
    .AUIPC .x30 (laHi GuestAddrs.srpc_env_base (GuestAddrs.stage_runtime_payload_code + 160)),
    .ADDI .x30 .x30 (laLo GuestAddrs.srpc_env_base (GuestAddrs.stage_runtime_payload_code + 160)),
    .SD .x30 .x6 (0 : BitVec 12),
    .ADDI .x7 .x6 (504 : BitVec 12),
    .ADDI .x7 .x7 (7 : BitVec 12),
    .ANDI .x7 .x7 (-8 : BitVec 12),
    .MV .x28 .x8,
    .BEQ .x7 .x0 (20 : BitVec 13),
    .SD .x28 .x0 (0 : BitVec 12),
    .ADDI .x28 .x28 (8 : BitVec 12),
    .ADDI .x7 .x7 (-8 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .SD .x8 .x20 (0 : BitVec 12),
    .ADDI .x28 .x8 (8 : BitVec 12),
    .MV .x29 .x19,
    .MV .x30 .x20,
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x29 (0 : BitVec 12),
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x28 .x8 .x5,
    .LD .x17 .x9 (64 : BitVec 12),
    .SD .x28 .x17 (8 : BitVec 12),
    .ADDI .x28 .x28 (16 : BitVec 12),
    .LD .x29 .x9 (56 : BitVec 12),
    .MV .x30 .x17,
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x29 (0 : BitVec 12),
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x28 .x8 .x5,
    .LD .x17 .x9 (64 : BitVec 12),
    .ADDI .x31 .x17 (7 : BitVec 12),
    .ANDI .x31 .x31 (-8 : BitVec 12),
    .ADD .x28 .x28 .x31,
    .SD .x28 .x23 (16 : BitVec 12),
    .ADDI .x28 .x28 (24 : BitVec 12),
    .MV .x29 .x22,
    .SLLI .x30 .x23 (6 : BitVec 6),
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x29 (0 : BitVec 12),
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .MV .x21 .x28,
    .ADDI .x10 .x18 (520 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u64le (GuestAddrs.stage_runtime_payload_code + 376)),
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.amsterdam_blob_gas_price_u256 (GuestAddrs.stage_runtime_payload_code + 384)),
    .MV .x28 .x21,
    .AUIPC .x29 (laHi GuestAddrs.m28_blob_stage_count (GuestAddrs.stage_runtime_payload_code + 392)),
    .ADDI .x29 .x29 (laLo GuestAddrs.m28_blob_stage_count (GuestAddrs.stage_runtime_payload_code + 392)),
    .LD .x5 .x29 (0 : BitVec 12),
    .SD .x28 .x5 (32 : BitVec 12),
    .ADDI .x29 .x28 (40 : BitVec 12),
    .AUIPC .x30 (laHi GuestAddrs.m28_blob_stage_table (GuestAddrs.stage_runtime_payload_code + 412)),
    .ADDI .x30 .x30 (laLo GuestAddrs.m28_blob_stage_table (GuestAddrs.stage_runtime_payload_code + 412)),
    .SLLI .x31 .x5 (5 : BitVec 6),
    .BEQ .x31 .x0 (28 : BitVec 13),
    .LBU .x15 .x30 (0 : BitVec 12),
    .SB .x29 .x15 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .SLLI .x5 .x5 (5 : BitVec 6),
    .AUIPC .x29 (laHi GuestAddrs.m29_stage_cur (GuestAddrs.stage_runtime_payload_code + 456)),
    .ADDI .x29 .x29 (laLo GuestAddrs.m29_stage_cur (GuestAddrs.stage_runtime_payload_code + 456)),
    .LD .x30 .x29 (0 : BitVec 12),
    .ADD .x29 .x28 .x5,
    .SD .x29 .x30 (40 : BitVec 12),
    .AUIPC .x29 (laHi GuestAddrs.m29_stage_count (GuestAddrs.stage_runtime_payload_code + 476)),
    .ADDI .x29 .x29 (laLo GuestAddrs.m29_stage_count (GuestAddrs.stage_runtime_payload_code + 476)),
    .LD .x31 .x29 (0 : BitVec 12),
    .ADD .x29 .x28 .x5,
    .SD .x29 .x31 (48 : BitVec 12),
    .ADD .x29 .x28 .x5,
    .ADDI .x29 .x29 (56 : BitVec 12),
    .AUIPC .x30 (laHi GuestAddrs.m29_stage_table (GuestAddrs.stage_runtime_payload_code + 504)),
    .ADDI .x30 .x30 (laLo GuestAddrs.m29_stage_table (GuestAddrs.stage_runtime_payload_code + 504)),
    .SLLI .x31 .x31 (5 : BitVec 6),
    .BEQ .x31 .x0 (28 : BitVec 13),
    .LBU .x15 .x30 (0 : BitVec 12),
    .SB .x29 .x15 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x6 (laHi GuestAddrs.srpc_env_base (GuestAddrs.stage_runtime_payload_code + 544)),
    .ADDI .x6 .x6 (laLo GuestAddrs.srpc_env_base (GuestAddrs.stage_runtime_payload_code + 544)),
    .LD .x6 .x6 (0 : BitVec 12),
    .ADD .x21 .x8 .x6,
    .ADDI .x28 .x18 (32 : BitVec 12),
    .ADDI .x29 .x21 (192 : BitVec 12),
    .LI .x30 (0 : Word),
    .LI .x31 (20 : Word),
    .BEQ .x30 .x31 (36 : BitVec 13),
    .ADD .x15 .x28 .x30,
    .LBU .x16 .x15 (0 : BitVec 12),
    .LI .x15 (19 : Word),
    .SUB .x15 .x15 .x30,
    .ADD .x15 .x29 .x15,
    .SB .x15 .x16 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .LBU .x28 .x18 (404 : BitVec 12),
    .LBU .x29 .x18 (405 : BitVec 12),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (406 : BitVec 12),
    .SLLI .x29 .x29 (16 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (407 : BitVec 12),
    .SLLI .x29 .x29 (24 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (408 : BitVec 12),
    .SLLI .x29 .x29 (32 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (409 : BitVec 12),
    .SLLI .x29 .x29 (40 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (410 : BitVec 12),
    .SLLI .x29 .x29 (48 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (411 : BitVec 12),
    .SLLI .x29 .x29 (56 : BitVec 6),
    .OR .x28 .x28 .x29,
    .SD .x21 .x28 (256 : BitVec 12),
    .LBU .x28 .x18 (428 : BitVec 12),
    .LBU .x29 .x18 (429 : BitVec 12),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (430 : BitVec 12),
    .SLLI .x29 .x29 (16 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (431 : BitVec 12),
    .SLLI .x29 .x29 (24 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (432 : BitVec 12),
    .SLLI .x29 .x29 (32 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (433 : BitVec 12),
    .SLLI .x29 .x29 (40 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (434 : BitVec 12),
    .SLLI .x29 .x29 (48 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (435 : BitVec 12),
    .SLLI .x29 .x29 (56 : BitVec 6),
    .OR .x28 .x28 .x29,
    .SD .x21 .x28 (224 : BitVec 12),
    .ADDI .x28 .x18 (372 : BitVec 12),
    .ADDI .x29 .x21 (288 : BitVec 12),
    .LI .x30 (0 : Word),
    .LI .x31 (32 : Word),
    .BEQ .x30 .x31 (36 : BitVec 13),
    .ADD .x15 .x28 .x30,
    .LBU .x16 .x15 (0 : BitVec 12),
    .LI .x15 (31 : Word),
    .SUB .x15 .x15 .x30,
    .ADD .x15 .x29 .x15,
    .SB .x15 .x16 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .LBU .x28 .x18 (412 : BitVec 12),
    .LBU .x29 .x18 (413 : BitVec 12),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (414 : BitVec 12),
    .SLLI .x29 .x29 (16 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (415 : BitVec 12),
    .SLLI .x29 .x29 (24 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (416 : BitVec 12),
    .SLLI .x29 .x29 (32 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (417 : BitVec 12),
    .SLLI .x29 .x29 (40 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (418 : BitVec 12),
    .SLLI .x29 .x29 (48 : BitVec 6),
    .OR .x28 .x28 .x29,
    .LBU .x29 .x18 (419 : BitVec 12),
    .SLLI .x29 .x29 (56 : BitVec 6),
    .OR .x28 .x28 .x29,
    .SD .x21 .x28 (320 : BitVec 12),
    .ADDI .x28 .x18 (440 : BitVec 12),
    .ADDI .x29 .x21 (352 : BitVec 12),
    .LI .x30 (0 : Word),
    .LI .x31 (32 : Word),
    .BEQ .x30 .x31 (28 : BitVec 13),
    .ADD .x15 .x28 .x30,
    .LBU .x16 .x15 (0 : BitVec 12),
    .ADD .x15 .x29 .x30,
    .SB .x15 .x16 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .AUIPC .x28 (laHi GuestAddrs.bv_chain_id (GuestAddrs.stage_runtime_payload_code + 984)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bv_chain_id (GuestAddrs.stage_runtime_payload_code + 984)),
    .LD .x29 .x28 (0 : BitVec 12),
    .SD .x21 .x29 (384 : BitVec 12),
    .ADDI .x28 .x9 (72 : BitVec 12),
    .MV .x29 .x21,
    .LI .x30 (0 : Word),
    .LI .x31 (20 : Word),
    .BEQ .x30 .x31 (36 : BitVec 13),
    .LI .x15 (19 : Word),
    .SUB .x15 .x15 .x30,
    .ADD .x15 .x28 .x15,
    .LBU .x16 .x15 (0 : BitVec 12),
    .ADD .x15 .x29 .x30,
    .SB .x15 .x16 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .ADDI .x28 .x9 (96 : BitVec 12),
    .ADDI .x29 .x21 (96 : BitVec 12),
    .LI .x30 (0 : Word),
    .LI .x31 (32 : Word),
    .BEQ .x30 .x31 (36 : BitVec 13),
    .ADD .x15 .x28 .x30,
    .LBU .x16 .x15 (0 : BitVec 12),
    .LI .x15 (31 : Word),
    .SUB .x15 .x15 .x30,
    .ADD .x15 .x29 .x15,
    .SB .x15 .x16 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .LI .x28 (0 : Word),
    .LI .x29 (0 : Word),
    .LI .x30 (8 : Word),
    .BEQ .x29 .x30 (36 : BitVec 13),
    .ADD .x30 .x18 .x29,
    .ADDI .x30 .x30 (532 : BitVec 12),
    .LBU .x31 .x30 (0 : BitVec 12),
    .SLLI .x15 .x29 (3 : BitVec 6),
    .SLL .x31 .x31 .x15,
    .OR .x28 .x28 .x31,
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .SD .x21 .x28 (416 : BitVec 12),
    .LD .x28 .x9 (40 : BitVec 12),
    .SD .x21 .x28 (448 : BitVec 12),
    .LI .x28 (1 : Word),
    .SD .x21 .x28 (456 : BitVec 12),
    .LD .x28 .x9 (48 : BitVec 12),
    .SD .x21 .x28 (464 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (72 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `stageRuntimePayloadCode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def stageRuntimePayloadCode_relocs : RelocTable :=
  [ (30, .la .x30 "m28_blob_stage_count"),
    (35, .la .x30 "m29_stage_count"),
    (40, .la .x30 "srpc_env_base"),
    (94, .jal .x1 "bgv_u64le"),
    (96, .jal .x1 "amsterdam_blob_gas_price_u256"),
    (98, .la .x29 "m28_blob_stage_count"),
    (103, .la .x30 "m28_blob_stage_table"),
    (114, .la .x29 "m29_stage_cur"),
    (119, .la .x29 "m29_stage_count"),
    (126, .la .x30 "m29_stage_table"),
    (136, .la .x6 "srpc_env_base"),
    (246, .la .x28 "bv_chain_id") ]

def stageRuntimePayloadCodeFunction : String :=
  "stage_runtime_payload_code:\n" ++ emitProgramR stageRuntimePayloadCode_prog stageRuntimePayloadCode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `stageRuntimePayloadCode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem stageRuntimePayloadCodeFunction_eq_prog :
    stageRuntimePayloadCodeFunction = "stage_runtime_payload_code:\n" ++ emitProgramR stageRuntimePayloadCode_prog stageRuntimePayloadCode_relocs := rfl

#guard stageRuntimePayloadCodeFunction.startsWith "stage_runtime_payload_code:\n"
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
def stageRuntimePayloadWitnessContext_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.srpc_env_base (GuestAddrs.stage_runtime_payload_witness_context + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.srpc_env_base (GuestAddrs.stage_runtime_payload_witness_context + 0)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x5 .x10 .x6,
    .SD .x5 .x12 (472 : BitVec 12),
    .SD .x5 .x14 (480 : BitVec 12),
    .SD .x5 .x16 (488 : BitVec 12),
    .ADDI .x7 .x5 (496 : BitVec 12),
    .MV .x5 .x11,
    .MV .x6 .x12,
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x7 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .MV .x5 .x13,
    .MV .x6 .x14,
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x7 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .MV .x5 .x15,
    .MV .x6 .x16,
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x7 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `stageRuntimePayloadWitnessContext_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def stageRuntimePayloadWitnessContext_relocs : RelocTable :=
  [ (0, .la .x5 "srpc_env_base") ]

def stageRuntimePayloadWitnessContextFunction : String :=
  "stage_runtime_payload_witness_context:\n" ++ emitProgramR stageRuntimePayloadWitnessContext_prog stageRuntimePayloadWitnessContext_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `stageRuntimePayloadWitnessContext_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem stageRuntimePayloadWitnessContextFunction_eq_prog :
    stageRuntimePayloadWitnessContextFunction = "stage_runtime_payload_witness_context:\n" ++ emitProgramR stageRuntimePayloadWitnessContext_prog stageRuntimePayloadWitnessContext_relocs := rfl

#guard stageRuntimePayloadWitnessContextFunction.startsWith "stage_runtime_payload_witness_context:\n"
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


end EvmAsm.Codegen
