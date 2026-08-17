/-
  EvmAsm.Codegen.Programs.Bloom

  Bloom-filter cluster lifted out of `EvmAsm.Codegen.Programs`
  per the file-size hard cap. This module groups every atomic
  bloom helper plus the per-block accumulators and the
  end-to-end validation composite.

  Slab 1 (K148-K154): atomic primitives
    K148 bloom_add_value         - single value (address/topic)
    K149 log_bloom_add           - one log (address + topics)
    K150 logs_list_bloom_add     - one receipt's logs
    K151 bloom_or_into           - 256-byte in-place OR
    K152 receipt_extract_logs_bloom
    K153 header_extract_logs_bloom
    K154 bloom_eq                - 256-byte equality

  Block-level composites live in `BloomBlock.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.BloomAddValue
import EvmAsm.Codegen.Programs.CallFrameReturn

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## log_bloom_add -- PR-K149

    Add a full log's bloom contributions to a 256-byte bloom
    filter, in place. A log is `rlp([address, topics, data])`
    where:
      * address : 20-byte string
      * topics  : RLP list of 32-byte hashes (0..4 entries; the
                  EVM opcodes LOG0..LOG4 enforce the upper bound)
      * data    : opaque bytes (NOT part of the bloom; only the
                  address and topics enter the filter)

    For each `value` in `{address, topic[0], …, topic[k-1]}`:
      bloom_add_value(bloom, value, len(value))

    Composes:
      - PR-K20 `rlp_list_nth_item`        — locate address /
        topics-list fields and individual topics
      - PR-K47 `rlp_list_count_items`     — topic-list cardinality
      - PR-K148 `bloom_add_value`         — bit-set per value
      - `zkvm_keccak256` (via K148)        — hashing

    Calling convention:
      a0 (input)  : bloom ptr (256 bytes, mutable, in-place OR)
      a1 (input)  : log_rlp ptr
      a2 (input)  : log_rlp byte length
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / log shape invalid
        2 : address field length != 20 bytes
        3 : topic field length != 32 bytes

    The data field is *not* part of the bloom, per the yellow
    paper; it's read and discarded. Caller zero-initialises the
    bloom buffer before the first call of a logs sequence. -/
def logBloomAdd_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x9,
    .MV .x11 .x18,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.lba_offset (GuestAddrs.log_bloom_add + 56)),
    .ADDI .x13 .x13 (laLo GuestAddrs.lba_offset (GuestAddrs.log_bloom_add + 56)),
    .AUIPC .x14 (laHi GuestAddrs.lba_length (GuestAddrs.log_bloom_add + 64)),
    .ADDI .x14 .x14 (laLo GuestAddrs.lba_length (GuestAddrs.log_bloom_add + 64)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.log_bloom_add + 72)),
    .BNE .x10 .x0 (brOff (GuestAddrs.log_bloom_add + 372) (GuestAddrs.log_bloom_add + 76)),
    .AUIPC .x5 (laHi GuestAddrs.lba_length (GuestAddrs.log_bloom_add + 80)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lba_length (GuestAddrs.log_bloom_add + 80)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (20 : Word),
    .BNE .x6 .x7 (brOff (GuestAddrs.log_bloom_add + 380) (GuestAddrs.log_bloom_add + 96)),
    .AUIPC .x5 (laHi GuestAddrs.lba_offset (GuestAddrs.log_bloom_add + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lba_offset (GuestAddrs.log_bloom_add + 100)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x11 .x9 .x6,
    .MV .x10 .x8,
    .LI .x12 (20 : Word),
    .JAL .x1 (jalOff GuestAddrs.bloom_add_value (GuestAddrs.log_bloom_add + 124)),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.lba_topics_offset (GuestAddrs.log_bloom_add + 140)),
    .ADDI .x13 .x13 (laLo GuestAddrs.lba_topics_offset (GuestAddrs.log_bloom_add + 140)),
    .AUIPC .x14 (laHi GuestAddrs.lba_topics_length (GuestAddrs.log_bloom_add + 148)),
    .ADDI .x14 .x14 (laLo GuestAddrs.lba_topics_length (GuestAddrs.log_bloom_add + 148)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.log_bloom_add + 156)),
    .BNE .x10 .x0 (brOff (GuestAddrs.log_bloom_add + 372) (GuestAddrs.log_bloom_add + 160)),
    .AUIPC .x5 (laHi GuestAddrs.lba_topics_offset (GuestAddrs.log_bloom_add + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lba_topics_offset (GuestAddrs.log_bloom_add + 164)),
    .LD .x19 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.lba_topics_length (GuestAddrs.log_bloom_add + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lba_topics_length (GuestAddrs.log_bloom_add + 176)),
    .LD .x20 .x5 (0 : BitVec 12),
    .ADD .x5 .x9 .x19,
    .MV .x10 .x5,
    .MV .x11 .x20,
    .AUIPC .x12 (laHi GuestAddrs.lba_topic_count (GuestAddrs.log_bloom_add + 200)),
    .ADDI .x12 .x12 (laLo GuestAddrs.lba_topic_count (GuestAddrs.log_bloom_add + 200)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.log_bloom_add + 208)),
    .BNE .x10 .x0 (brOff (GuestAddrs.log_bloom_add + 372) (GuestAddrs.log_bloom_add + 212)),
    .AUIPC .x5 (laHi GuestAddrs.lba_topic_count (GuestAddrs.log_bloom_add + 216)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lba_topic_count (GuestAddrs.log_bloom_add + 216)),
    .LD .x21 .x5 (0 : BitVec 12),
    .LI .x31 (0 : Word),
    .BGE .x31 .x21 (brOff (GuestAddrs.log_bloom_add + 364) (GuestAddrs.log_bloom_add + 232)),
    .ADD .x10 .x9 .x19,
    .MV .x11 .x20,
    .MV .x12 .x31,
    .AUIPC .x13 (laHi GuestAddrs.lba_offset (GuestAddrs.log_bloom_add + 248)),
    .ADDI .x13 .x13 (laLo GuestAddrs.lba_offset (GuestAddrs.log_bloom_add + 248)),
    .AUIPC .x14 (laHi GuestAddrs.lba_length (GuestAddrs.log_bloom_add + 256)),
    .ADDI .x14 .x14 (laLo GuestAddrs.lba_length (GuestAddrs.log_bloom_add + 256)),
    .ADDI .x2 .x2 (-8 : BitVec 12),
    .SD .x2 .x31 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.log_bloom_add + 272)),
    .LD .x31 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (8 : BitVec 12),
    .BNE .x10 .x0 (brOff (GuestAddrs.log_bloom_add + 372) (GuestAddrs.log_bloom_add + 284)),
    .AUIPC .x5 (laHi GuestAddrs.lba_length (GuestAddrs.log_bloom_add + 288)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lba_length (GuestAddrs.log_bloom_add + 288)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BNE .x6 .x7 (brOff (GuestAddrs.log_bloom_add + 388) (GuestAddrs.log_bloom_add + 304)),
    .AUIPC .x5 (laHi GuestAddrs.lba_offset (GuestAddrs.log_bloom_add + 308)),
    .ADDI .x5 .x5 (laLo GuestAddrs.lba_offset (GuestAddrs.log_bloom_add + 308)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x6 .x6 .x19,
    .ADD .x11 .x9 .x6,
    .MV .x10 .x8,
    .LI .x12 (32 : Word),
    .ADDI .x2 .x2 (-8 : BitVec 12),
    .SD .x2 .x31 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bloom_add_value (GuestAddrs.log_bloom_add + 344)),
    .LD .x31 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (8 : BitVec 12),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.log_bloom_add + 232) (GuestAddrs.log_bloom_add + 360)),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (3 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `logBloomAdd_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def logBloomAdd_relocs : RelocTable :=
  [ (14, .la .x13 "lba_offset"),
    (16, .la .x14 "lba_length"),
    (18, .jal .x1 "rlp_list_nth_item"),
    (20, .la .x5 "lba_length"),
    (25, .la .x5 "lba_offset"),
    (31, .jal .x1 "bloom_add_value"),
    (35, .la .x13 "lba_topics_offset"),
    (37, .la .x14 "lba_topics_length"),
    (39, .jal .x1 "rlp_list_nth_item"),
    (41, .la .x5 "lba_topics_offset"),
    (44, .la .x5 "lba_topics_length"),
    (50, .la .x12 "lba_topic_count"),
    (52, .jal .x1 "rlp_list_count_items"),
    (54, .la .x5 "lba_topic_count"),
    (62, .la .x13 "lba_offset"),
    (64, .la .x14 "lba_length"),
    (68, .jal .x1 "rlp_list_nth_item"),
    (72, .la .x5 "lba_length"),
    (77, .la .x5 "lba_offset"),
    (86, .jal .x1 "bloom_add_value") ]

def logBloomAddFunction : String :=
  "log_bloom_add:\n" ++ emitProgramR logBloomAdd_prog logBloomAdd_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `logBloomAdd_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem logBloomAddFunction_eq_prog :
    logBloomAddFunction = "log_bloom_add:\n" ++ emitProgramR logBloomAdd_prog logBloomAdd_relocs := rfl

#guard logBloomAddFunction.startsWith "log_bloom_add:\n"
#guard logBloomAdd_prog.length = 107
/-! ## logs_list_bloom_add -- PR-K150

    OR every log's bloom contribution from an RLP-encoded `logs`
    list into a 256-byte bloom buffer. This is what
    `apply_body` calls on each receipt's logs to compute the
    receipt's `logs_bloom` field, and what
    `block_compute_logs_bloom` (future) calls to assemble the
    block-level bloom from receipts (via repeated OR).

    Input list shape:

      logs = rlp([log_0, log_1, ..., log_{n-1}])
      log_i = rlp([address, topics, data])

    For each log_i, `logs_list_bloom_add` invokes K149
    `log_bloom_add` (which itself loops K148 `bloom_add_value`).
    Empty `logs` list (`0xc0`) is a valid input → bloom unchanged.

    Composes:
      - PR-K20 `rlp_list_nth_item`    -- walk each log_i
      - PR-K47 `rlp_list_count_items` -- list cardinality
      - PR-K149 `log_bloom_add`       -- per-log accumulation
      - PR-K148 `bloom_add_value`     -- (via K149)
      - `zkvm_keccak256`              -- (via K148)

    Calling convention:
      a0 (input)  : bloom ptr (256 bytes, mutable, in-place OR;
                    caller zero-inits before first call)
      a1 (input)  : logs_rlp ptr (RLP list of log entries)
      a2 (input)  : logs_rlp byte length
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure (logs_rlp not a list)
        2 : a log address field length != 20 (per K149)
        3 : a log topic field length != 32 (per K149) -/
def logsListBloomAdd_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x9,
    .MV .x11 .x18,
    .AUIPC .x12 (laHi GuestAddrs.llba_count (GuestAddrs.logs_list_bloom_add + 48)),
    .ADDI .x12 .x12 (laLo GuestAddrs.llba_count (GuestAddrs.logs_list_bloom_add + 48)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.logs_list_bloom_add + 56)),
    .BNE .x10 .x0 (brOff (GuestAddrs.logs_list_bloom_add + 180) (GuestAddrs.logs_list_bloom_add + 60)),
    .AUIPC .x5 (laHi GuestAddrs.llba_count (GuestAddrs.logs_list_bloom_add + 64)),
    .ADDI .x5 .x5 (laLo GuestAddrs.llba_count (GuestAddrs.logs_list_bloom_add + 64)),
    .LD .x19 .x5 (0 : BitVec 12),
    .LI .x20 (0 : Word),
    .BGE .x20 .x19 (brOff (GuestAddrs.logs_list_bloom_add + 172) (GuestAddrs.logs_list_bloom_add + 80)),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .MV .x12 .x20,
    .AUIPC .x13 (laHi GuestAddrs.llba_offset (GuestAddrs.logs_list_bloom_add + 96)),
    .ADDI .x13 .x13 (laLo GuestAddrs.llba_offset (GuestAddrs.logs_list_bloom_add + 96)),
    .AUIPC .x14 (laHi GuestAddrs.llba_length (GuestAddrs.logs_list_bloom_add + 104)),
    .ADDI .x14 .x14 (laLo GuestAddrs.llba_length (GuestAddrs.logs_list_bloom_add + 104)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.logs_list_bloom_add + 112)),
    .BNE .x10 .x0 (brOff (GuestAddrs.logs_list_bloom_add + 180) (GuestAddrs.logs_list_bloom_add + 116)),
    .AUIPC .x5 (laHi GuestAddrs.llba_offset (GuestAddrs.logs_list_bloom_add + 120)),
    .ADDI .x5 .x5 (laLo GuestAddrs.llba_offset (GuestAddrs.logs_list_bloom_add + 120)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.llba_length (GuestAddrs.logs_list_bloom_add + 132)),
    .ADDI .x5 .x5 (laLo GuestAddrs.llba_length (GuestAddrs.logs_list_bloom_add + 132)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x11 .x9 .x6,
    .MV .x12 .x7,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.log_bloom_add (GuestAddrs.logs_list_bloom_add + 156)),
    .BNE .x10 .x0 (28 : BitVec 13),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.logs_list_bloom_add + 80) (GuestAddrs.logs_list_bloom_add + 168)),
    .LI .x10 (0 : Word),
    .JAL .x0 (12 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (4 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `logsListBloomAdd_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def logsListBloomAdd_relocs : RelocTable :=
  [ (12, .la .x12 "llba_count"),
    (14, .jal .x1 "rlp_list_count_items"),
    (16, .la .x5 "llba_count"),
    (24, .la .x13 "llba_offset"),
    (26, .la .x14 "llba_length"),
    (28, .jal .x1 "rlp_list_nth_item"),
    (30, .la .x5 "llba_offset"),
    (33, .la .x5 "llba_length"),
    (39, .jal .x1 "log_bloom_add") ]

def logsListBloomAddFunction : String :=
  "logs_list_bloom_add:\n" ++ emitProgramR logsListBloomAdd_prog logsListBloomAdd_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `logsListBloomAdd_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem logsListBloomAddFunction_eq_prog :
    logsListBloomAddFunction = "logs_list_bloom_add:\n" ++ emitProgramR logsListBloomAdd_prog logsListBloomAdd_relocs := rfl

#guard logsListBloomAddFunction.startsWith "logs_list_bloom_add:\n"
#guard logsListBloomAdd_prog.length = 55
def ziskLogsListBloomAddDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bav_hash:\n" ++
  "  .zero 32\n" ++
  "lba_offset:\n" ++
  "  .zero 8\n" ++
  "lba_length:\n" ++
  "  .zero 8\n" ++
  "lba_topics_offset:\n" ++
  "  .zero 8\n" ++
  "lba_topics_length:\n" ++
  "  .zero 8\n" ++
  "lba_topic_count:\n" ++
  "  .zero 8\n" ++
  "llba_offset:\n" ++
  "  .zero 8\n" ++
  "llba_length:\n" ++
  "  .zero 8\n" ++
  "llba_count:\n" ++
  "  .zero 8"

/-! ## captured_logs_bloom_add -- M26 receipt bridge

    Convert the dispatcher's bounded LOG event descriptors into a 256-byte
    receipt bloom. Each descriptor is 256 bytes:
      +0  topic count (u64, must be <= 4)
      +32..160 four 32-byte topic slots in EVM stack-word byte order
      +192..224 ADDRESS context word in EVM stack-word byte order

    Stack-word byte order is four little-endian u64 limbs, low limb first.
    Ethereum bloom hashing wants canonical byte order, so this helper reverses
    the low 20 address bytes and each 32-byte topic into scratch before calling
    `bloom_add_value`. Descriptor data bytes are intentionally ignored, as data
    is not part of the Ethereum logs_bloom.

    Calling convention:
      a0 (input)  : bloom ptr (256 bytes, mutable, in-place OR)
      a1 (input)  : descriptor base ptr
      a2 (input)  : descriptor count
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : descriptor count > 16
        2 : topic count > 4 -/
def capturedLogsBloomAddFunction : String :=
  "captured_logs_bloom_add:
" ++
  "  addi sp, sp, -64
" ++
  "  sd ra,  0(sp)
" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
" ++
  "  mv s0, a0                   # bloom ptr
" ++
  "  mv s1, a1                   # descriptor base
" ++
  "  mv s2, a2                   # descriptor count
" ++
  "  li t0, 1024
" ++
  "  bgtu s2, t0, .Lclba_count_fail
" ++
  "  li s3, 0                    # descriptor index
" ++
  ".Lclba_log_loop:
" ++
  "  bgeu s3, s2, .Lclba_done
" ++
  "  slli t0, s3, 8              # i * 256
" ++
  "  add s4, s1, t0              # descriptor ptr
" ++
  "  ld s5, 0(s4)                # topic count
" ++
  "  li t0, 4
" ++
  "  bgtu s5, t0, .Lclba_topic_count_fail
" ++
  "  # ADDRESS word at descriptor+192. Bloom hashes the low 160 bits in
" ++
  "  # canonical big-endian order, so reverse descriptor bytes 0..19.
" ++
  "  addi t0, s4, 192
" ++
  "  addi t0, t0, 19
" ++
  "  la t1, clba_value
" ++
  "  li t2, 20
" ++
  ".Lclba_addr_rev:
" ++
  "  beqz t2, .Lclba_addr_hash
" ++
  "  lbu t3, 0(t0)
" ++
  "  sb t3, 0(t1)
" ++
  "  addi t0, t0, -1
" ++
  "  addi t1, t1, 1
" ++
  "  addi t2, t2, -1
" ++
  "  j .Lclba_addr_rev
" ++
  ".Lclba_addr_hash:
" ++
  "  mv a0, s0; la a1, clba_value; li a2, 20
" ++
  "  jal ra, bloom_add_value
" ++
  "  li s6, 0                    # topic index
" ++
  ".Lclba_topic_loop:
" ++
  "  bgeu s6, s5, .Lclba_next_log
" ++
  "  slli t0, s6, 5              # topic offset = 32 + 32*j
" ++
  "  addi t0, t0, 32
" ++
  "  add t0, s4, t0
" ++
  "  addi t0, t0, 31
" ++
  "  la t1, clba_value
" ++
  "  li t2, 32
" ++
  ".Lclba_topic_rev:
" ++
  "  beqz t2, .Lclba_topic_hash
" ++
  "  lbu t3, 0(t0)
" ++
  "  sb t3, 0(t1)
" ++
  "  addi t0, t0, -1
" ++
  "  addi t1, t1, 1
" ++
  "  addi t2, t2, -1
" ++
  "  j .Lclba_topic_rev
" ++
  ".Lclba_topic_hash:
" ++
  "  mv a0, s0; la a1, clba_value; li a2, 32
" ++
  "  jal ra, bloom_add_value
" ++
  "  addi s6, s6, 1
" ++
  "  j .Lclba_topic_loop
" ++
  ".Lclba_next_log:
" ++
  "  addi s3, s3, 1
" ++
  "  j .Lclba_log_loop
" ++
  ".Lclba_done:
" ++
  "  li a0, 0
" ++
  "  j .Lclba_ret
" ++
  ".Lclba_count_fail:
" ++
  "  li a0, 1
" ++
  "  j .Lclba_ret
" ++
  ".Lclba_topic_count_fail:
" ++
  "  li a0, 2
" ++
  ".Lclba_ret:
" ++
  "  ld ra,  0(sp)
" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
" ++
  "  addi sp, sp, 64
" ++
  "  ret"

/-! ## bloom_or_into -- PR-K151

    In-place 256-byte bitwise OR: `dst[i] |= src[i]` for
    `i in 0..256`. Used to accumulate one bloom filter into
    another -- in particular, to fold each receipt's `logs_bloom`
    into the block-level `block.logs_bloom` field.

    A natural complement to:
      * PR-K148 `bloom_add_value`     -- single-value add
      * PR-K149 `log_bloom_add`       -- per-log accumulation
      * PR-K150 `logs_list_bloom_add` -- per-receipt accumulation
      * PR-K151 (this PR) `bloom_or_into` -- per-block accumulation

    Pure register arithmetic; processes 8 bytes per iteration
    (32 iterations total) using `ld` + `or` + `sd`. No external
    function calls.

    Calling convention:
      a0 (input)  : dst bloom ptr (256 bytes, mutable, in-place OR)
      a1 (input)  : src bloom ptr (256 bytes, read-only)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def bloomOrInto_prog : Program :=
  [ .LI .x5 (32 : Word),
    .MV .x6 .x10,
    .MV .x7 .x11,
    .BEQ .x5 .x0 (36 : BitVec 13),
    .LD .x28 .x6 (0 : BitVec 12),
    .LD .x29 .x7 (0 : BitVec 12),
    .OR .x28 .x28 .x29,
    .SD .x6 .x28 (0 : BitVec 12),
    .ADDI .x6 .x6 (8 : BitVec 12),
    .ADDI .x7 .x7 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bloomOrIntoFunction : String :=
  "bloom_or_into:\n" ++ emitProgram bloomOrInto_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bloomOrInto_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bloomOrIntoFunction_eq_prog :
    bloomOrIntoFunction = "bloom_or_into:\n" ++ emitProgram bloomOrInto_prog := rfl

#guard bloomOrIntoFunction.startsWith "bloom_or_into:\n"
#guard bloomOrInto_prog.length = 14
/-! ## receipt_extract_logs_bloom -- PR-K152

    Extract the 256-byte `logs_bloom` field (field 2) from a
    receipt RLP. The receipt's inner shape (post-Byzantium,
    typed or untyped) is:

      receipt = rlp([status_or_postroot,
                     cumulative_gas_used,
                     logs_bloom (256 B fixed),
                     logs])

    For typed (EIP-2718) receipts on the wire, the caller is
    expected to have stripped the leading `0x<type>` byte, so
    `a0` points at the inner list's RLP prefix.

    Direct building block for block-level bloom validation: the
    block bloom is the OR-accumulation of every receipt's
    `logs_bloom`. With PR-K151 `bloom_or_into`, the loop becomes:

      bzero(block_bloom)
      for receipt in receipts:
        receipt_extract_logs_bloom(receipt, scratch)
        bloom_or_into(block_bloom, scratch)
      assert block_bloom == header.logs_bloom

    Composes:
      - PR-K20 `rlp_list_nth_item` on field 2

    Calling convention:
      a0 (input)  : receipt_rlp ptr (inner list, no type byte)
      a1 (input)  : receipt_rlp byte length
      a2 (input)  : 256-byte output bloom ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fewer than 3 fields
        2 : logs_bloom field length != 256 -/
def receiptExtractLogsBloom_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (2 : Word),
    .AUIPC .x13 (laHi GuestAddrs.relb_offset (GuestAddrs.receipt_extract_logs_bloom + 44)),
    .ADDI .x13 .x13 (laLo GuestAddrs.relb_offset (GuestAddrs.receipt_extract_logs_bloom + 44)),
    .AUIPC .x14 (laHi GuestAddrs.relb_length (GuestAddrs.receipt_extract_logs_bloom + 52)),
    .ADDI .x14 .x14 (laLo GuestAddrs.relb_length (GuestAddrs.receipt_extract_logs_bloom + 52)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.receipt_extract_logs_bloom + 60)),
    .BNE .x10 .x0 (84 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.relb_length (GuestAddrs.receipt_extract_logs_bloom + 68)),
    .ADDI .x5 .x5 (laLo GuestAddrs.relb_length (GuestAddrs.receipt_extract_logs_bloom + 68)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (256 : Word),
    .BNE .x6 .x7 (72 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.relb_offset (GuestAddrs.receipt_extract_logs_bloom + 88)),
    .ADDI .x5 .x5 (laLo GuestAddrs.relb_offset (GuestAddrs.receipt_extract_logs_bloom + 88)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x28 .x8 .x6,
    .MV .x29 .x18,
    .LI .x30 (256 : Word),
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x28 (0 : BitVec 12),
    .SB .x29 .x31 (0 : BitVec 12),
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
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `receiptExtractLogsBloom_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def receiptExtractLogsBloom_relocs : RelocTable :=
  [ (11, .la .x13 "relb_offset"),
    (13, .la .x14 "relb_length"),
    (15, .jal .x1 "rlp_list_nth_item"),
    (17, .la .x5 "relb_length"),
    (22, .la .x5 "relb_offset") ]

def receiptExtractLogsBloomFunction : String :=
  "receipt_extract_logs_bloom:\n" ++ emitProgramR receiptExtractLogsBloom_prog receiptExtractLogsBloom_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `receiptExtractLogsBloom_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem receiptExtractLogsBloomFunction_eq_prog :
    receiptExtractLogsBloomFunction = "receipt_extract_logs_bloom:\n" ++ emitProgramR receiptExtractLogsBloom_prog receiptExtractLogsBloom_relocs := rfl

#guard receiptExtractLogsBloomFunction.startsWith "receipt_extract_logs_bloom:\n"
#guard receiptExtractLogsBloom_prog.length = 46
/-! ## header_extract_logs_bloom -- PR-K153

    Extract the 256-byte `logs_bloom` field (field 6, 0-indexed)
    from a block header RLP. Header field layout from genesis on:

      [parent_hash, ommers_hash, coinbase,
       state_root, transactions_root, receipts_root,
       logs_bloom,                                   <-- field 6
       difficulty, number, gas_limit, gas_used,
       timestamp, extra_data, prev_randao / mix_hash,
       nonce, base_fee_per_gas?, withdrawals_root?,
       blob_gas_used?, excess_blob_gas?,
       parent_beacon_block_root?, requests_hash?]

    The bloom's position at field 6 is invariant across every
    fork from Frontier through Amsterdam; later forks only
    append new fields after it.

    Direct counterpart to PR-K152 `receipt_extract_logs_bloom`.
    Together with PR-K151 `bloom_or_into`, the verifier's
    `block_validate_logs_bloom` check becomes:

      header_extract_logs_bloom(header_rlp, header_bloom)
      bzero(computed_bloom)
      for receipt in receipts:
        receipt_extract_logs_bloom(receipt, scratch)
        bloom_or_into(computed_bloom, scratch)
      assert memcmp(header_bloom, computed_bloom) == 0

    Composes:
      - PR-K20 `rlp_list_nth_item` on field 6

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 256-byte output bloom ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fewer than 7 fields
        2 : logs_bloom field length != 256 -/
def headerExtractLogsBloom_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (6 : Word),
    .AUIPC .x13 (laHi GuestAddrs.helb_offset (GuestAddrs.header_extract_logs_bloom + 44)),
    .ADDI .x13 .x13 (laLo GuestAddrs.helb_offset (GuestAddrs.header_extract_logs_bloom + 44)),
    .AUIPC .x14 (laHi GuestAddrs.helb_length (GuestAddrs.header_extract_logs_bloom + 52)),
    .ADDI .x14 .x14 (laLo GuestAddrs.helb_length (GuestAddrs.header_extract_logs_bloom + 52)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.header_extract_logs_bloom + 60)),
    .BNE .x10 .x0 (84 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.helb_length (GuestAddrs.header_extract_logs_bloom + 68)),
    .ADDI .x5 .x5 (laLo GuestAddrs.helb_length (GuestAddrs.header_extract_logs_bloom + 68)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (256 : Word),
    .BNE .x6 .x7 (72 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.helb_offset (GuestAddrs.header_extract_logs_bloom + 88)),
    .ADDI .x5 .x5 (laLo GuestAddrs.helb_offset (GuestAddrs.header_extract_logs_bloom + 88)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x28 .x8 .x6,
    .MV .x29 .x18,
    .LI .x30 (256 : Word),
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x28 (0 : BitVec 12),
    .SB .x29 .x31 (0 : BitVec 12),
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
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerExtractLogsBloom_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerExtractLogsBloom_relocs : RelocTable :=
  [ (11, .la .x13 "helb_offset"),
    (13, .la .x14 "helb_length"),
    (15, .jal .x1 "rlp_list_nth_item"),
    (17, .la .x5 "helb_length"),
    (22, .la .x5 "helb_offset") ]

def headerExtractLogsBloomFunction : String :=
  "header_extract_logs_bloom:\n" ++ emitProgramR headerExtractLogsBloom_prog headerExtractLogsBloom_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerExtractLogsBloom_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerExtractLogsBloomFunction_eq_prog :
    headerExtractLogsBloomFunction = "header_extract_logs_bloom:\n" ++ emitProgramR headerExtractLogsBloom_prog headerExtractLogsBloom_relocs := rfl

#guard headerExtractLogsBloomFunction.startsWith "header_extract_logs_bloom:\n"
#guard headerExtractLogsBloom_prog.length = 46
/-! ## bloom_eq -- PR-K154

    Byte-equal check between two 256-byte bloom filters. The
    final compare step in block-level bloom validation:

      assert bloom_eq(header.logs_bloom, computed_block_bloom)

    Returns the verdict as a u64 (1 if equal, 0 if not). The
    return code in `a0` is always 0 (the predicate result lives
    in the out pointer, not the status), so the caller can
    distinguish "predicate is false" from "the call itself
    failed" -- though here the call can never fail since there
    are no parse / boundary conditions to honour.

    Together with PR-K151 `bloom_or_into`, PR-K152
    `receipt_extract_logs_bloom`, and PR-K153
    `header_extract_logs_bloom`, this closes the
    block-level bloom-validation pipeline:

      header_extract_logs_bloom(header_rlp, header_bloom)
      bzero(computed_bloom)
      for receipt in receipts:
        receipt_extract_logs_bloom(receipt, scratch)
        bloom_or_into(computed_bloom, scratch)
      bloom_eq(header_bloom, computed_bloom, is_equal_out)
      assert is_equal_out == 1

    Pure register arithmetic; processes 8 bytes per iteration
    (32 iterations total) using `ld` + `xor` + `or`. Early-exit
    on first mismatch is intentionally avoided to keep the
    cycle count constant (256-byte compare is cheap and timing
    invariance is friendlier to gas-cost modeling).

    Calling convention:
      a0 (input)  : bloom_a ptr (256 bytes, read-only)
      a1 (input)  : bloom_b ptr (256 bytes, read-only)
      a2 (input)  : u64 out ptr (1 if equal, 0 if not)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def bloomEq_prog : Program :=
  [ .LI .x5 (32 : Word),
    .MV .x6 .x10,
    .MV .x7 .x11,
    .LI .x30 (0 : Word),
    .BEQ .x5 .x0 (36 : BitVec 13),
    .LD .x28 .x6 (0 : BitVec 12),
    .LD .x29 .x7 (0 : BitVec 12),
    .XOR .x28 .x28 .x29,
    .OR .x30 .x30 .x28,
    .ADDI .x6 .x6 (8 : BitVec 12),
    .ADDI .x7 .x7 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .SLTIU .x30 .x30 (1 : BitVec 12),
    .SD .x12 .x30 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bloomEqFunction : String :=
  "bloom_eq:\n" ++ emitProgram bloomEq_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bloomEq_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bloomEqFunction_eq_prog :
    bloomEqFunction = "bloom_eq:\n" ++ emitProgram bloomEq_prog := rfl

#guard bloomEqFunction.startsWith "bloom_eq:\n"
#guard bloomEq_prog.length = 17
/-! ## running bloom checkpoint helpers

    Side-array storage for hot receipt/block bloom accumulation and
    per-call-depth checkpoints. The descriptor-backed receipt/log-bloom
    materialization remains authoritative; these helpers are only the
    substrate for later call-frame rollback plumbing.

    `running_bloom_zero(ptr)` clears a 256-byte bloom.
    `running_bloom_copy(dst, src)` copies one 256-byte bloom.

    Both routines process aligned 8-byte words, so callers must pass
    8-byte-aligned bloom/checkpoint labels. -/

def runningBloomZero_prog : Program :=
  [ .LI .x5 (32 : Word),
    .MV .x6 .x10,
    .BEQ .x5 .x0 (20 : BitVec 13),
    .SD .x6 .x0 (0 : BitVec 12),
    .ADDI .x6 .x6 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def runningBloomZeroFunction : String :=
  "running_bloom_zero:\n" ++ emitProgram runningBloomZero_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `runningBloomZero_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem runningBloomZeroFunction_eq_prog :
    runningBloomZeroFunction = "running_bloom_zero:\n" ++ emitProgram runningBloomZero_prog := rfl

#guard runningBloomZeroFunction.startsWith "running_bloom_zero:\n"
#guard runningBloomZero_prog.length = 9
def runningBloomCopy_prog : Program :=
  [ .LI .x5 (32 : Word),
    .MV .x6 .x10,
    .MV .x7 .x11,
    .BEQ .x5 .x0 (28 : BitVec 13),
    .LD .x28 .x7 (0 : BitVec 12),
    .SD .x6 .x28 (0 : BitVec 12),
    .ADDI .x6 .x6 (8 : BitVec 12),
    .ADDI .x7 .x7 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def runningBloomCopyFunction : String :=
  "running_bloom_copy:\n" ++ emitProgram runningBloomCopy_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `runningBloomCopy_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem runningBloomCopyFunction_eq_prog :
    runningBloomCopyFunction = "running_bloom_copy:\n" ++ emitProgram runningBloomCopy_prog := rfl

#guard runningBloomCopyFunction.startsWith "running_bloom_copy:\n"
#guard runningBloomCopy_prog.length = 12
end EvmAsm.Codegen
