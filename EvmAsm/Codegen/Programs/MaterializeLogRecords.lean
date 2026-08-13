/-
  EvmAsm.Codegen.Programs.MaterializeLogRecords

  `materialize_log_records` (bead evm-asm-8uld3.1.2, EIP-6110) — the bridge between
  the M26 `evm_event_logs` LOG-capture descriptors (+ the persistent full-data
  `evm_log_data` buffer from 8uld3.1a, #8674) and the CANONICAL big-endian
  log-record array that `parse_deposit_requests` (#8657) consumes.

  The M26 descriptor (logCapturePreBody, EvmLogHandlers.lean; 256-byte stride) stores
  256-bit words in NATIVE order:
    * the packed block-log ADDRESS at +8 is already canonical big-endian
      (block_log_window_snapshot copies the canonical BE descriptor address);
    * topic0 at +32 is a stack word — LITTLE-ENDIAN (the descent reverses +31..+0 to
      get cd_value_be BE);
    * the full log data lives in `evm_log_data` at `evm_log_data_meta[i] = (offset, len)`
      (parallel to the descriptors) — raw bytes, already in the right order.

  `parse_deposit_requests` expects each record canonicalized to Ethereum big-endian:
    +0   address (20-byte BE in the low bytes, padded to 32)
    +32  topic_count (u64)
    +40  topic0 (32-byte BE)
    +72  data_len (u64)
    +80  data bytes (data_len, padded to 8)
  record stride = 80 + roundup8(data_len).

  So materialize copies the already-canonical address (20 B), reverses topic0
  (32 B) to BE, and copies the full data verbatim. Synthetic eip7708/SELFDESTRUCT logs bump the descriptor count
  without writing `evm_log_data_meta` (their <=32-byte data lives in the descriptor
  prefix); their stale/zero meta yields a record whose address is the synthetic
  emitter (not the deposit contract), which `parse_deposit_requests` skips on the
  address filter. `len` is sanity-capped to the buffer size to bound the copy.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## materialize_log_records
    a0 = PACKED descriptor base (variable stride 32 + 32*topic_count; vv4hr.3.4.2)
    address @ +8 (20 B canonical BE), topic_count @ +0, topic0 @ +32.   a1 = log count
    a2 = evm_log_data base                                    a3 = meta base (24 B stride)
    a4 = out canonical-record array ptr
    a0 (output) = total bytes written (sum of 80 + roundup8(len) per record).
    Each input log -> one canonical BE record (address+topic0 byte-reversed). -/
def materializeLogRecordsFunction : String :=
  "materialize_log_records:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                    # descriptor cursor\n" ++
  "  mv s1, a1                    # remaining count\n" ++
  "  mv s2, a2                    # evm_log_data base\n" ++
  "  mv s3, a3                    # meta cursor\n" ++
  "  mv s4, a4                    # out cursor\n" ++
  "  mv s5, a4                    # out base\n" ++
  ".Lmlr_loop:\n" ++
  "  beqz s1, .Lmlr_done\n" ++
  -- zero record[0..32] (address slot, padded) then copy canonical BE address from desc+8..+27
  "  sd zero, 0(s4); sd zero, 8(s4); sd zero, 16(s4); sd zero, 24(s4)\n" ++
  "  addi t0, s0, 8               # src = packed desc + 8 (canonical BE address)\n" ++
  "  mv t1, s4                    # dst = record+0\n" ++
  "  li t2, 20\n" ++
  ".Lmlr_addr:\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  bnez t2, .Lmlr_addr\n" ++
  -- topic_count: record+32 = desc+0
  "  ld t0, 0(s0)\n  sd t0, 32(s4)\n" ++
  -- topic0: record+40..+72 = reverse(desc+32..+63)
  "  addi t0, s0, 63             # src = desc + 32 + 31 (MSByte of the LE topic0)\n" ++
  "  addi t1, s4, 40             # dst = record+40\n" ++
  "  li t2, 32\n" ++
  ".Lmlr_topic:\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1)\n" ++
  "  addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  bnez t2, .Lmlr_topic\n" ++
  -- data: meta[i] = (offset, len) at s3; cap len to 262144 (buffer size) to bound the copy
  "  ld t4, 0(s3)                # offset into evm_log_data\n" ++
  "  ld t5, 8(s3)                # data_len\n" ++
  "  li t0, " ++ toString bvBlockLogDataBytes ++ "\n" ++
  "  bleu t5, t0, .Lmlr_lenok\n" ++
  "  li t5, 0                    # stale/garbage len -> 0 (record skipped by parse's filters)\n" ++
  ".Lmlr_lenok:\n" ++
  "  sd t5, 72(s4)               # record+72 = data_len\n" ++
  "  add t0, s2, t4              # src = evm_log_data + offset\n" ++
  "  addi t1, s4, 80             # dst = record+80\n" ++
  "  mv t2, t5\n" ++
  ".Lmlr_data:\n" ++
  "  beqz t2, .Lmlr_data_done\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  j .Lmlr_data\n" ++
  ".Lmlr_data_done:\n" ++
  -- advance: out += 80 + roundup8(len); desc += reclen (packed); meta += 24; count -= 1
  "  addi t5, t5, 7; andi t5, t5, -8; addi t5, t5, 80\n" ++
  "  add s4, s4, t5\n" ++
  "  ld t0, 0(s0); slli t0, t0, 5; addi t0, t0, 32   # reclen = 32 + 32*topic_count\n" ++
  "  add s0, s0, t0\n" ++
  "  addi s3, s3, 24\n" ++
  "  addi s1, s1, -1\n" ++
  "  j .Lmlr_loop\n" ++
  ".Lmlr_done:\n" ++
  "  sub a0, s4, s5              # total bytes written\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_materialize_log_records`: focused probe. Synthesizes two M26 descriptors +
    an `evm_log_data` buffer + parallel meta, materializes, and dumps the canonical
    records so the byte-reversal (address + topic0 -> BE) and the data copy can be
    asserted.

    Descriptor 0: addr = BE bytes 0x01..0x14 -> record address 0x01..0x14;
      topic_count = 2; topic0 = LE 0x20..0x01 -> BE 0x01..0x20; data = "DEPO" (4 B) at off 0.
    Descriptor 1: addr = BE bytes 0x15..0x28 -> record address 0x15..0x28; topic_count = 1;
      topic0 = LE 0x40..0x21 -> BE 0x21..0x40; data = 0 bytes (meta len 0).

    Output (at 0xa0010000):
      +0  total bytes (expect (80+8) + (80+0) = 168)
      +8  record0 first 128 bytes (addr/topic_count/topic0/len/data)  -- truncated dump -/
def ziskMaterializeLogRecordsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  -- build descriptor 0 at mlr_descs+0
  "  la s0, mlr_descs\n" ++
  -- topic_count = 2
  "  li t0, 2\n  sd t0, 0(s0)\n" ++
  -- topic0 (desc+32..63) = LE bytes 0x20,0x1f,...,0x01  (so BE = 01..20)
  "  addi t1, s0, 32\n  li t2, 32\n  li t3, 32\n" ++   -- t3 = 0x20 counting down
  ".Lmlrp_t0:\n" ++
  "  sb t3, 0(t1)\n  addi t1, t1, 1\n  addi t3, t3, -1\n  addi t2, t2, -1\n  bnez t2, .Lmlrp_t0\n" ++
  -- PACK: address (packed desc+8..27) = BE bytes 0x01..0x14
  "  addi t1, s0, 8\n  li t2, 20\n  li t3, 1\n" ++
  ".Lmlrp_a0:\n" ++
  "  sb t3, 0(t1)\n  addi t1, t1, 1\n  addi t3, t3, 1\n  addi t2, t2, -1\n  bnez t2, .Lmlrp_a0\n" ++
  -- descriptor 1 at mlr_descs+96 (desc0 reclen = 32 + 2*32 = 96)
  "  addi s0, s0, 96\n" ++
  "  li t0, 1\n  sd t0, 0(s0)\n" ++
  -- topic0 = LE 0x40..0x21 (BE = 21..40)
  "  addi t1, s0, 32\n  li t2, 32\n  li t3, 64\n" ++
  ".Lmlrp_t1:\n" ++
  "  sb t3, 0(t1)\n  addi t1, t1, 1\n  addi t3, t3, -1\n  addi t2, t2, -1\n  bnez t2, .Lmlrp_t1\n" ++
  -- address = BE bytes 0x15..0x28
  "  addi t1, s0, 8\n  li t2, 20\n  li t3, 21\n" ++
  ".Lmlrp_a1:\n" ++
  "  sb t3, 0(t1)\n  addi t1, t1, 1\n  addi t3, t3, 1\n  addi t2, t2, -1\n  bnez t2, .Lmlrp_a1\n" ++
  -- evm_log_data: bytes "DEPO" = 0x44 0x45 0x50 0x4f at offset 0
  "  la t0, mlr_data\n  li t1, 0x44\n  sb t1, 0(t0)\n  li t1, 0x45\n  sb t1, 1(t0)\n  li t1, 0x50\n  sb t1, 2(t0)\n  li t1, 0x4f\n  sb t1, 3(t0)\n" ++
  -- meta (24 B stride): meta[0] = (off 0, len 4) @+0; meta[1] = (off 0, len 0) @+24
  "  la t0, mlr_meta\n  sd zero, 0(t0)\n  li t1, 4\n  sd t1, 8(t0)\n  sd zero, 24(t0)\n  sd zero, 32(t0)\n" ++
  -- materialize_log_records(descs, 2, data, meta, out)
  "  la a0, mlr_descs\n  li a1, 2\n  la a2, mlr_data\n  la a3, mlr_meta\n  la a4, mlr_out\n" ++
  "  jal ra, materialize_log_records\n" ++
  -- dump: +0 total, +8.. record0 (88 bytes) + record1 (80 bytes) = 168 -> clamp to 240
  "  li t0, 0xa0010000\n  sd a0, 0(t0)\n" ++
  "  la t1, mlr_out\n  addi t3, t0, 8\n  li t4, 176\n" ++
  ".Lmlrp_dump:\n" ++
  "  beqz t4, .Lmlrp_dd\n" ++
  "  lbu t5, 0(t1); sb t5, 0(t3); addi t1, t1, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lmlrp_dump\n" ++
  ".Lmlrp_dd:\n" ++
  "  j .Lmlrp_done\n" ++
  materializeLogRecordsFunction ++ "\n" ++
  ".Lmlrp_done:"

def ziskMaterializeLogRecordsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mlr_descs:\n  .zero 512\n" ++      -- packed descriptors (desc0 96 B + desc1 64 B)
  ".balign 8\n" ++
  "mlr_data:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "mlr_meta:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "mlr_out:\n  .zero 1024\n"


end EvmAsm.Codegen
