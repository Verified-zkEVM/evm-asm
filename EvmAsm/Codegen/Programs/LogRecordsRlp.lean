/-
  EvmAsm.Codegen.Programs.LogRecordsRlp

  `log_records_encode_rlp` (.63.1.6.2.1 logs leaf) — encode a window of the
  dispatcher's captured LOG descriptors as the spec's RLP logs list
  `rlp([log_0, ..])` with `log_i = rlp([address(20B), [topic..], data])`,
  matching execution-specs `Log` encoding (blocks.py). This is the missing
  primitive between the 8uld3.1a log capture (256-byte native descriptors +
  the evm_log_data full-data buffer) and the receipt encoder's `logs_rlp`
  input (`receipt_encode` field 3 / `logs_desc_ptr@8`): the per-tx bloom can
  then be derived from the same encoding via `logs_list_bloom_add`.

  Descriptor layout (EvmLogHandlers):
    +0    topic_count (u64, 0..4)
    +32   four 32-byte topic slots (stack-word / LE order)
    +192  executing ADDRESS context bytes (canonical 20-byte BE, low-aligned)
  Full data: evm_log_data_meta[i] = {byte offset (u64), data length (u64)}
  into evm_log_data.

  NOT wired into the verdict (that is the .2.1 integration follow-up) —
  soundness-neutral, like the nxio8 gas leaves.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Per-log scratch cap: address item (21) + topics list (≤ 2 + 4×33) + data
    item header (≤ 9). Data bytes are streamed straight into the payload
    buffer, so the cap bounds only the per-log header material. -/
def logRecordsRlpScratchCap : Nat := 256

/-! ## log_records_encode_rlp

    Calling convention:
      a0 = descriptor base ptr (256-byte stride; entry 0 of the WINDOW —
           callers pass `evm_event_logs + first*256`)
      a1 = log count in the window
      a2 = evm_log_data base ptr
      a3 = evm_log_data_meta base ptr (entry 0 of the WINDOW — callers pass
           `evm_log_data_meta + first*16`)
      a4 = output buffer ptr (receives `rlp([log..])`)
      a5 = output buffer capacity in bytes
      a6 = u64 out-length ptr
      a0 (output) status:
        0 success
        1 malformed descriptor (topic_count > 4)
        2 output capacity exceeded
    Zero logs encode as the empty list `0xc0`. -/
def logRecordsEncodeRlp_prog : Program :=
  [ .ADDI .x2 .x2 (-112 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .SD .x2 .x25 (80 : BitVec 12),
    .SD .x2 .x26 (88 : BitVec 12),
    .SD .x2 .x27 (96 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .SD .x22 .x0 (0 : BitVec 12),
    .LI .x23 (0 : Word),
    .BEQ .x9 .x0 (brOff (GuestAddrs.log_records_encode_rlp + 864) (GuestAddrs.log_records_encode_rlp + 92)),
    .AUIPC .x5 (laHi GuestAddrs.lrr_addr_be (GuestAddrs.log_records_encode_rlp + 96)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lrr_addr_be (GuestAddrs.log_records_encode_rlp + 96)),
    .ADDI .x6 .x8 (8 : BitVec 12),
    .LI .x7 (0 : Word),
    .LI .x28 (20 : Word),
    .BEQ .x7 .x28 (28 : BitVec 13),
    .ADD .x28 .x6 .x7,
    .LBU .x29 .x28 (0 : BitVec 12),
    .ADD .x28 .x5 .x7,
    .SB .x28 .x29 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.lrr_addr_be (GuestAddrs.log_records_encode_rlp + 144)),
    .ADDI .x10 .x10 (laLo GuestAddrs.lrr_addr_be (GuestAddrs.log_records_encode_rlp + 144)),
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.lrr_inner (GuestAddrs.log_records_encode_rlp + 156)),
    .ADDI .x12 .x12 (laLo GuestAddrs.lrr_inner (GuestAddrs.log_records_encode_rlp + 156)),
    .AUIPC .x13 (laHi GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 164)),
    .ADDI .x13 .x13 (laLo GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 164)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.log_records_encode_rlp + 172)),
    .AUIPC .x5 (laHi GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 176)),
    .LD .x24 .x5 (0 : BitVec 12),
    .LD .x25 .x8 (0 : BitVec 12),
    .LI .x5 (4 : Word),
    .BLTU .x5 .x25 (brOff (GuestAddrs.log_records_encode_rlp + 968) (GuestAddrs.log_records_encode_rlp + 196)),
    .LI .x26 (0 : Word),
    .LI .x27 (0 : Word),
    .BEQ .x26 .x25 (brOff (GuestAddrs.log_records_encode_rlp + 336) (GuestAddrs.log_records_encode_rlp + 208)),
    .SLLI .x5 .x26 (5 : BitVec 6),
    .ADDI .x6 .x8 (32 : BitVec 12),
    .ADD .x6 .x6 .x5,
    .AUIPC .x5 (laHi GuestAddrs.lrr_topic_be (GuestAddrs.log_records_encode_rlp + 224)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lrr_topic_be (GuestAddrs.log_records_encode_rlp + 224)),
    .LI .x7 (0 : Word),
    .LI .x28 (32 : Word),
    .BEQ .x7 .x28 (36 : BitVec 13),
    .LI .x28 (31 : Word),
    .SUB .x28 .x28 .x7,
    .ADD .x28 .x6 .x28,
    .LBU .x29 .x28 (0 : BitVec 12),
    .ADD .x28 .x5 .x7,
    .SB .x28 .x29 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.lrr_topic_be (GuestAddrs.log_records_encode_rlp + 276)),
    .ADDI .x10 .x10 (laLo GuestAddrs.lrr_topic_be (GuestAddrs.log_records_encode_rlp + 276)),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.lrr_topics (GuestAddrs.log_records_encode_rlp + 288)),
    .ADDI .x12 .x12 (laLo GuestAddrs.lrr_topics (GuestAddrs.log_records_encode_rlp + 288)),
    .ADD .x12 .x12 .x27,
    .AUIPC .x13 (laHi GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 300)),
    .ADDI .x13 .x13 (laLo GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 300)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.log_records_encode_rlp + 308)),
    .AUIPC .x5 (laHi GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 312)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 312)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x27 .x27 .x6,
    .ADDI .x26 .x26 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.log_records_encode_rlp + 208) (GuestAddrs.log_records_encode_rlp + 332)),
    .MV .x10 .x27,
    .AUIPC .x11 (laHi GuestAddrs.lrr_inner (GuestAddrs.log_records_encode_rlp + 340)),
    .ADDI .x11 .x11 (laLo GuestAddrs.lrr_inner (GuestAddrs.log_records_encode_rlp + 340)),
    .ADD .x11 .x11 .x24,
    .AUIPC .x12 (laHi GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 352)),
    .ADDI .x12 .x12 (laLo GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 352)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.log_records_encode_rlp + 360)),
    .AUIPC .x5 (laHi GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 364)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 364)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x24 .x24 .x6,
    .AUIPC .x5 (laHi GuestAddrs.lrr_topics (GuestAddrs.log_records_encode_rlp + 380)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lrr_topics (GuestAddrs.log_records_encode_rlp + 380)),
    .AUIPC .x6 (laHi GuestAddrs.lrr_inner (GuestAddrs.log_records_encode_rlp + 388)),
    .ADDI .x6 .x6 (laLo GuestAddrs.lrr_inner (GuestAddrs.log_records_encode_rlp + 388)),
    .ADD .x6 .x6 .x24,
    .MV .x7 .x27,
    .BEQ .x7 .x0 (28 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x24 .x24 .x27,
    .LD .x26 .x19 (8 : BitVec 12),
    .LI .x5 (1 : Word),
    .BNE .x26 .x5 (32 : BitVec 13),
    .LD .x6 .x19 (0 : BitVec 12),
    .ADD .x6 .x18 .x6,
    .LBU .x7 .x6 (0 : BitVec 12),
    .LI .x28 (128 : Word),
    .BGEU .x7 .x28 (12 : BitVec 13),
    .LI .x27 (0 : Word),
    .JAL .x0 (jalOff (GuestAddrs.log_records_encode_rlp + 600) (GuestAddrs.log_records_encode_rlp + 472)),
    .LI .x5 (56 : Word),
    .BLTU .x26 .x5 (brOff (GuestAddrs.log_records_encode_rlp + 576) (GuestAddrs.log_records_encode_rlp + 480)),
    .AUIPC .x6 (laHi GuestAddrs.lrr_dhdr (GuestAddrs.log_records_encode_rlp + 484)),
    .ADDI .x6 .x6 (laLo GuestAddrs.lrr_dhdr (GuestAddrs.log_records_encode_rlp + 484)),
    .LI .x7 (0 : Word),
    .MV .x28 .x26,
    .BEQ .x28 .x0 (16 : BitVec 13),
    .SRLI .x28 .x28 (8 : BitVec 6),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-12 : BitVec 21),
    .LI .x29 (183 : Word),
    .ADD .x29 .x29 .x7,
    .SB .x6 .x29 (0 : BitVec 12),
    .MV .x28 .x7,
    .BEQ .x28 .x0 (36 : BitVec 13),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .SLLI .x29 .x28 (3 : BitVec 6),
    .SRL .x29 .x26 .x29,
    .ANDI .x29 .x29 (255 : BitVec 12),
    .SUB .x30 .x7 .x28,
    .ADD .x30 .x6 .x30,
    .SB .x30 .x29 (0 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .ADDI .x27 .x7 (1 : BitVec 12),
    .JAL .x0 (28 : BitVec 21),
    .AUIPC .x6 (laHi GuestAddrs.lrr_dhdr (GuestAddrs.log_records_encode_rlp + 576)),
    .ADDI .x6 .x6 (laLo GuestAddrs.lrr_dhdr (GuestAddrs.log_records_encode_rlp + 576)),
    .LI .x29 (128 : Word),
    .ADD .x29 .x29 .x26,
    .SB .x6 .x29 (0 : BitVec 12),
    .LI .x27 (1 : Word),
    .ADD .x5 .x24 .x27,
    .ADD .x5 .x5 .x26,
    .MV .x10 .x5,
    .AUIPC .x11 (laHi GuestAddrs.lrr_payload (GuestAddrs.log_records_encode_rlp + 612)),
    .ADDI .x11 .x11 (laLo GuestAddrs.lrr_payload (GuestAddrs.log_records_encode_rlp + 612)),
    .ADD .x11 .x11 .x23,
    .AUIPC .x12 (laHi GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 624)),
    .ADDI .x12 .x12 (laLo GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 624)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.log_records_encode_rlp + 632)),
    .AUIPC .x5 (laHi GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 636)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 636)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .AUIPC .x5 (laHi GuestAddrs.lrr_inner (GuestAddrs.log_records_encode_rlp + 652)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lrr_inner (GuestAddrs.log_records_encode_rlp + 652)),
    .AUIPC .x6 (laHi GuestAddrs.lrr_payload (GuestAddrs.log_records_encode_rlp + 660)),
    .ADDI .x6 .x6 (laLo GuestAddrs.lrr_payload (GuestAddrs.log_records_encode_rlp + 660)),
    .ADD .x6 .x6 .x23,
    .MV .x7 .x24,
    .BEQ .x7 .x0 (28 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x23 .x23 .x24,
    .AUIPC .x5 (laHi GuestAddrs.lrr_dhdr (GuestAddrs.log_records_encode_rlp + 708)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lrr_dhdr (GuestAddrs.log_records_encode_rlp + 708)),
    .AUIPC .x6 (laHi GuestAddrs.lrr_payload (GuestAddrs.log_records_encode_rlp + 716)),
    .ADDI .x6 .x6 (laLo GuestAddrs.lrr_payload (GuestAddrs.log_records_encode_rlp + 716)),
    .ADD .x6 .x6 .x23,
    .MV .x7 .x27,
    .BEQ .x7 .x0 (28 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x23 .x23 .x27,
    .LD .x5 .x19 (0 : BitVec 12),
    .ADD .x5 .x18 .x5,
    .AUIPC .x6 (laHi GuestAddrs.lrr_payload (GuestAddrs.log_records_encode_rlp + 772)),
    .ADDI .x6 .x6 (laLo GuestAddrs.lrr_payload (GuestAddrs.log_records_encode_rlp + 772)),
    .ADD .x6 .x6 .x23,
    .MV .x7 .x26,
    .ADD .x28 .x23 .x7,
    .LUI .x29 (512 : BitVec 20),
    .ADDIW .x29 .x29 (-1500 : BitVec 12),
    .BLTU .x29 .x28 (brOff (GuestAddrs.log_records_encode_rlp + 976) (GuestAddrs.log_records_encode_rlp + 800)),
    .BEQ .x7 .x0 (28 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x23 .x23 .x26,
    .LD .x5 .x8 (0 : BitVec 12),
    .SLLI .x5 .x5 (5 : BitVec 6),
    .ADDI .x5 .x5 (32 : BitVec 12),
    .ADD .x8 .x8 .x5,
    .ADDI .x19 .x19 (24 : BitVec 12),
    .ADDI .x9 .x9 (-1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.log_records_encode_rlp + 92) (GuestAddrs.log_records_encode_rlp + 860)),
    .LI .x5 (9 : Word),
    .BLTU .x21 .x5 (brOff (GuestAddrs.log_records_encode_rlp + 976) (GuestAddrs.log_records_encode_rlp + 868)),
    .MV .x10 .x23,
    .MV .x11 .x20,
    .AUIPC .x12 (laHi GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 880)),
    .ADDI .x12 .x12 (laLo GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 880)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.log_records_encode_rlp + 888)),
    .AUIPC .x5 (laHi GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 892)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lrr_len (GuestAddrs.log_records_encode_rlp + 892)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x6 .x23,
    .BLTU .x21 .x7 (brOff (GuestAddrs.log_records_encode_rlp + 976) (GuestAddrs.log_records_encode_rlp + 908)),
    .SD .x22 .x7 (0 : BitVec 12),
    .ADD .x28 .x20 .x6,
    .AUIPC .x29 (laHi GuestAddrs.lrr_payload (GuestAddrs.log_records_encode_rlp + 920)),
    .ADDI .x29 .x29 (laLo GuestAddrs.lrr_payload (GuestAddrs.log_records_encode_rlp + 920)),
    .MV .x30 .x23,
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x29 (0 : BitVec 12),
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .LD .x25 .x2 (80 : BitVec 12),
    .LD .x26 .x2 (88 : BitVec 12),
    .LD .x27 .x2 (96 : BitVec 12),
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `logRecordsEncodeRlp_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def logRecordsEncodeRlp_relocs : RelocTable :=
  [ (24, .la .x5 "lrr_addr_be"),
    (36, .la .x10 "lrr_addr_be"),
    (39, .la .x12 "lrr_inner"),
    (41, .la .x13 "lrr_len"),
    (43, .jal .x1 "rlp_encode_bytes"),
    (44, .la .x5 "lrr_len"),
    (56, .la .x5 "lrr_topic_be"),
    (69, .la .x10 "lrr_topic_be"),
    (72, .la .x12 "lrr_topics"),
    (75, .la .x13 "lrr_len"),
    (77, .jal .x1 "rlp_encode_bytes"),
    (78, .la .x5 "lrr_len"),
    (85, .la .x11 "lrr_inner"),
    (88, .la .x12 "lrr_len"),
    (90, .jal .x1 "rlp_encode_list_prefix"),
    (91, .la .x5 "lrr_len"),
    (95, .la .x5 "lrr_topics"),
    (97, .la .x6 "lrr_inner"),
    (121, .la .x6 "lrr_dhdr"),
    (144, .la .x6 "lrr_dhdr"),
    (153, .la .x11 "lrr_payload"),
    (156, .la .x12 "lrr_len"),
    (158, .jal .x1 "rlp_encode_list_prefix"),
    (159, .la .x5 "lrr_len"),
    (163, .la .x5 "lrr_inner"),
    (165, .la .x6 "lrr_payload"),
    (177, .la .x5 "lrr_dhdr"),
    (179, .la .x6 "lrr_payload"),
    (193, .la .x6 "lrr_payload"),
    (220, .la .x12 "lrr_len"),
    (222, .jal .x1 "rlp_encode_list_prefix"),
    (223, .la .x5 "lrr_len"),
    (230, .la .x29 "lrr_payload") ]

def logRecordsEncodeRlpFunction : String :=
  "log_records_encode_rlp:\n" ++ emitProgramR logRecordsEncodeRlp_prog logRecordsEncodeRlp_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `logRecordsEncodeRlp_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem logRecordsEncodeRlpFunction_eq_prog :
    logRecordsEncodeRlpFunction = "log_records_encode_rlp:\n" ++ emitProgramR logRecordsEncodeRlp_prog logRecordsEncodeRlp_relocs := rfl

#guard logRecordsEncodeRlpFunction.startsWith "log_records_encode_rlp:\n"
/-- Scratch labels for `log_records_encode_rlp`. The 128 KiB payload buffer
    matches `evm_log_data`'s half: headers are small, so a window whose data
    fits the capture buffer fits here for typical receipts; status 2 reports
    overflow rather than truncating. -/
def logRecordsRlpDataSection : String :=
  ".balign 8\n" ++
  "lrr_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "lrr_addr_be:\n  .zero 20\n" ++
  ".balign 8\n" ++
  "lrr_topic_be:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "lrr_dhdr:\n  .zero 9\n" ++
  ".balign 8\n" ++
  "lrr_topics:\n  .zero 136\n" ++
  ".balign 8\n" ++
  s!"lrr_inner:\n  .zero {logRecordsRlpScratchCap}\n" ++
  ".balign 8\n" ++
  "lrr_payload:\n  .zero 2095652\n"

/-- `zisk_log_records_encode_rlp`: focused probe.

    Input (after the ziskemu length wrapper at 0x40000000):
      +8    log count (u64)
      +16   count × 256-byte descriptors (native layout)
      then  count × 16-byte meta entries {offset, len} (offsets into the
            data blob that follows)
      then  the data blob.
    Output: +0 status, +8 encoded length, +16.. encoded bytes. -/
def ziskLogRecordsEncodeRlpPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1, 8(s0)                # count\n" ++
  "  addi a0, s0, 16             # descriptors\n" ++
  "  mv a1, s1\n" ++
  "  slli t0, s1, 8\n" ++
  "  addi a3, s0, 16\n" ++
  "  add a3, a3, t0              # meta = after descriptors\n" ++
  "  slli t1, s1, 4\n" ++
  "  add a2, a3, t1              # data blob = after meta\n" ++
  "  li a4, 0xa0010010\n" ++
  "  li a5, 8192\n" ++
  "  li a6, 0xa0010008\n" ++
  "  jal ra, log_records_encode_rlp\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Llrrp_done\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  logRecordsEncodeRlpFunction ++ "\n" ++
  ".Llrrp_done:"


end EvmAsm.Codegen
