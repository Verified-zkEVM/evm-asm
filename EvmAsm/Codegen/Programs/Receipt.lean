/-
  EvmAsm.Codegen.Programs.Receipt

  Receipt encoding + the supporting RLP helper carved out of
  `EvmAsm.Codegen.Programs` per the file-size hard cap. Hosts:

    K155  rlp_encode_u64
    K156  receipt_encode

  Depends on `Programs/RlpRead.lean` for the
  `rlpEncodeListPrefixFunction` helper inlined by
  receipt_encode's `zisk_*` probe prologue.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## rlp_encode_u64 -- PR-K155

    Encode a `u64` register value as canonical RLP. A convenience
    wrapper that takes the integer directly rather than the BE
    byte buffer that PR-K30 `rlp_encode_uint_be` requires:

      value == 0       -> 0x80                       (1 byte)
      value < 0x80     -> single byte = value        (1 byte)
      else             -> 0x80 + effective_len + BE bytes
                          (effective_len in 1..8)    (2..9 bytes)

    Pure register arithmetic, leaf-callable, no scratch memory.
    Use cases where K30 with a stack-allocated BE buffer is
    awkward boilerplate -- typical example is receipt encoding:

      rlp_encode_u64(status, buf + cursor, &written); cursor += written
      rlp_encode_u64(cumulative_gas, buf + cursor, &written); cursor += written
      ...

    Calling convention:
      a0 (input)  : value (u64)
      a1 (input)  : output buffer ptr (caller supplies >= 9 bytes)
      a2 (input)  : u64 out length ptr (bytes written; 1..9)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def rlpEncodeU64_prog : Program :=
  [ .BEQ .x10 .x0 (32 : BitVec 13),
    .LI .x5 (128 : Word),
    .BGEU .x10 .x5 (48 : BitVec 13),
    .SB .x11 .x10 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x12 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x5 (128 : Word),
    .SB .x11 .x5 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x12 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x5 (1 : Word),
    .LI .x6 (256 : Word),
    .BLTU .x10 .x6 (80 : BitVec 13),
    .LI .x5 (2 : Word),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .BLTU .x10 .x6 (68 : BitVec 13),
    .LI .x5 (3 : Word),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .BLTU .x10 .x6 (56 : BitVec 13),
    .LI .x5 (4 : Word),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .BLTU .x10 .x6 (44 : BitVec 13),
    .LI .x5 (5 : Word),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .BLTU .x10 .x6 (32 : BitVec 13),
    .LI .x5 (6 : Word),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .BLTU .x10 .x6 (20 : BitVec 13),
    .LI .x5 (7 : Word),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .BLTU .x10 .x6 (8 : BitVec 13),
    .LI .x5 (8 : Word),
    .ADDI .x7 .x5 (128 : BitVec 12),
    .SB .x11 .x7 (0 : BitVec 12),
    .ADDI .x28 .x11 (1 : BitVec 12),
    .ADDI .x29 .x5 (-1 : BitVec 12),
    .BLT .x29 .x0 (28 : BitVec 13),
    .SLLI .x30 .x29 (3 : BitVec 6),
    .SRL .x31 .x10 .x30,
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x6 .x5 (1 : BitVec 12),
    .SD .x12 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def rlpEncodeU64Function : String :=
  "rlp_encode_u64:\n" ++ emitProgram rlpEncodeU64_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `rlpEncodeU64_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem rlpEncodeU64Function_eq_prog :
    rlpEncodeU64Function = "rlp_encode_u64:\n" ++ emitProgram rlpEncodeU64_prog := rfl

#guard rlpEncodeU64Function.startsWith "rlp_encode_u64:\n"
/-- `zisk_rlp_encode_u64`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : value (u64)
    Output layout:
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : bytes_written
      bytes 16..25 : encoded RLP (up to 9 bytes) -/
def ziskRlpEncodeU64Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a0, 8(a3)                # value\n" ++
  "  li a1, 0xa0010010           # output buffer ptr\n" ++
  "  li a2, 0xa0010008           # out length ptr\n" ++
  "  jal ra, rlp_encode_u64\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lreu64_pdone\n" ++
  rlpEncodeU64Function ++ "\n" ++
  ".Lreu64_pdone:"

def ziskRlpEncodeU64DataSection : String :=
  ".section .data\n" ++
  "reu64_pad:\n" ++
  "  .zero 8"


/-! ## receipt_encode -- PR-K156

    Encode an Ethereum tx receipt as RLP:

      receipt = rlp([status, cumulative_gas_used,
                     logs_bloom (256 B), logs])

    This is the encoder side of PR-K152 `receipt_extract_logs_bloom`,
    and the input to receipts-trie / receipts-root computation.
    For typed receipts (EIP-2718), the caller prepends the
    `0x<type>` byte to the output of this helper; the wire-format
    typed receipt is `type_byte || rlp(inner)`.

    Algorithm:
      1. Write status (u64) at receipt_pl_buf[0..]    via K155.
      2. Write cumulative_gas (u64) at next slot      via K155.
      3. Write logs_bloom (256 B as RLP string) at
         next slot                                    via K128.
      4. Copy logs_rlp (pre-encoded list) verbatim    (memcpy).
      5. Compute total payload length.
      6. Write outer list prefix to output[0..]       via K129.
      7. Copy receipt_pl_buf[..total_payload] to
         output[prefix_len..].

    Composes:
      - PR-K155 `rlp_encode_u64`        -- status / gas
      - PR-K128 `rlp_encode_bytes`      -- logs_bloom
      - PR-K129 `rlp_encode_list_prefix`-- outer list prefix

    Calling convention:
      a0 (input)  : status (u64)
      a1 (input)  : cumulative_gas_used (u64)
      a2 (input)  : logs_bloom ptr (exactly 256 bytes)
      a3 (input)  : logs_rlp ptr (pre-encoded list, copied verbatim)
      a4 (input)  : logs_rlp byte length
      a5 (input)  : output buffer ptr
      a6 (input)  : u64 out length ptr (total bytes written)
      ra (input)  : return
      a0 (output) : 0 (always succeeds).

    Uses a 16 KiB scratch buffer `re_payload_buf` in `.data` for
    the intermediate payload. Should comfortably hold mainnet
    receipt payloads (logs_bloom is 257 RLP bytes, status/gas
    add <= 18 bytes, logs section is variable but typically
    KBs at most). -/
def receiptEncode_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .AUIPC .x5 (laHi GuestAddrs.re_cursor (GuestAddrs.receipt_encode + 64)),
    .ADDI .x5 .x5 (laLo GuestAddrs.re_cursor (GuestAddrs.receipt_encode + 64)),
    .SD .x5 .x0 (0 : BitVec 12),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.re_payload_buf (GuestAddrs.receipt_encode + 80)),
    .ADDI .x11 .x11 (laLo GuestAddrs.re_payload_buf (GuestAddrs.receipt_encode + 80)),
    .AUIPC .x12 (laHi GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 88)),
    .ADDI .x12 .x12 (laLo GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 88)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_u64 (GuestAddrs.receipt_encode + 96)),
    .AUIPC .x5 (laHi GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 100)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.re_cursor (GuestAddrs.receipt_encode + 112)),
    .ADDI .x5 .x5 (laLo GuestAddrs.re_cursor (GuestAddrs.receipt_encode + 112)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.re_cursor (GuestAddrs.receipt_encode + 124)),
    .ADDI .x5 .x5 (laLo GuestAddrs.re_cursor (GuestAddrs.receipt_encode + 124)),
    .LD .x7 .x5 (0 : BitVec 12),
    .MV .x10 .x9,
    .AUIPC .x11 (laHi GuestAddrs.re_payload_buf (GuestAddrs.receipt_encode + 140)),
    .ADDI .x11 .x11 (laLo GuestAddrs.re_payload_buf (GuestAddrs.receipt_encode + 140)),
    .ADD .x11 .x11 .x7,
    .AUIPC .x12 (laHi GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 152)),
    .ADDI .x12 .x12 (laLo GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 152)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_u64 (GuestAddrs.receipt_encode + 160)),
    .AUIPC .x5 (laHi GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 164)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.re_cursor (GuestAddrs.receipt_encode + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.re_cursor (GuestAddrs.receipt_encode + 176)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x7 .x7 .x6,
    .AUIPC .x5 (laHi GuestAddrs.re_cursor (GuestAddrs.receipt_encode + 192)),
    .ADDI .x5 .x5 (laLo GuestAddrs.re_cursor (GuestAddrs.receipt_encode + 192)),
    .SD .x5 .x7 (0 : BitVec 12),
    .MV .x10 .x18,
    .LI .x11 (256 : Word),
    .AUIPC .x12 (laHi GuestAddrs.re_payload_buf (GuestAddrs.receipt_encode + 212)),
    .ADDI .x12 .x12 (laLo GuestAddrs.re_payload_buf (GuestAddrs.receipt_encode + 212)),
    .ADD .x12 .x12 .x7,
    .AUIPC .x13 (laHi GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 224)),
    .ADDI .x13 .x13 (laLo GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 224)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.receipt_encode + 232)),
    .AUIPC .x5 (laHi GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 236)),
    .ADDI .x5 .x5 (laLo GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 236)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.re_cursor (GuestAddrs.receipt_encode + 248)),
    .ADDI .x5 .x5 (laLo GuestAddrs.re_cursor (GuestAddrs.receipt_encode + 248)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x7 .x7 .x6,
    .AUIPC .x28 (laHi GuestAddrs.re_payload_buf (GuestAddrs.receipt_encode + 264)),
    .ADDI .x28 .x28 (laLo GuestAddrs.re_payload_buf (GuestAddrs.receipt_encode + 264)),
    .ADD .x28 .x28 .x7,
    .MV .x29 .x19,
    .MV .x30 .x20,
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x29 (0 : BitVec 12),
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x7 .x7 .x20,
    .AUIPC .x5 (laHi GuestAddrs.re_total_payload (GuestAddrs.receipt_encode + 316)),
    .ADDI .x5 .x5 (laLo GuestAddrs.re_total_payload (GuestAddrs.receipt_encode + 316)),
    .SD .x5 .x7 (0 : BitVec 12),
    .MV .x10 .x7,
    .MV .x11 .x21,
    .AUIPC .x12 (laHi GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 336)),
    .ADDI .x12 .x12 (laLo GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 336)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.receipt_encode + 344)),
    .AUIPC .x5 (laHi GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 348)),
    .ADDI .x5 .x5 (laLo GuestAddrs.re_field_len (GuestAddrs.receipt_encode + 348)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.re_total_payload (GuestAddrs.receipt_encode + 360)),
    .ADDI .x5 .x5 (laLo GuestAddrs.re_total_payload (GuestAddrs.receipt_encode + 360)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x28 .x21 .x6,
    .AUIPC .x29 (laHi GuestAddrs.re_payload_buf (GuestAddrs.receipt_encode + 376)),
    .ADDI .x29 .x29 (laLo GuestAddrs.re_payload_buf (GuestAddrs.receipt_encode + 376)),
    .MV .x30 .x7,
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x29 (0 : BitVec 12),
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x6 .x6 .x7,
    .SD .x22 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `receiptEncode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def receiptEncode_relocs : RelocTable :=
  [ (16, .la .x5 "re_cursor"),
    (20, .la .x11 "re_payload_buf"),
    (22, .la .x12 "re_field_len"),
    (24, .jal .x1 "rlp_encode_u64"),
    (25, .la .x5 "re_field_len"),
    (28, .la .x5 "re_cursor"),
    (31, .la .x5 "re_cursor"),
    (35, .la .x11 "re_payload_buf"),
    (38, .la .x12 "re_field_len"),
    (40, .jal .x1 "rlp_encode_u64"),
    (41, .la .x5 "re_field_len"),
    (44, .la .x5 "re_cursor"),
    (48, .la .x5 "re_cursor"),
    (53, .la .x12 "re_payload_buf"),
    (56, .la .x13 "re_field_len"),
    (58, .jal .x1 "rlp_encode_bytes"),
    (59, .la .x5 "re_field_len"),
    (62, .la .x5 "re_cursor"),
    (66, .la .x28 "re_payload_buf"),
    (79, .la .x5 "re_total_payload"),
    (84, .la .x12 "re_field_len"),
    (86, .jal .x1 "rlp_encode_list_prefix"),
    (87, .la .x5 "re_field_len"),
    (90, .la .x5 "re_total_payload"),
    (94, .la .x29 "re_payload_buf") ]

def receiptEncodeFunction : String :=
  "receipt_encode:\n" ++ emitProgramR receiptEncode_prog receiptEncode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `receiptEncode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem receiptEncodeFunction_eq_prog :
    receiptEncodeFunction = "receipt_encode:\n" ++ emitProgramR receiptEncode_prog receiptEncode_relocs := rfl

#guard receiptEncodeFunction.startsWith "receipt_encode:\n"
/-- `zisk_receipt_encode`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : status (u64 LE)
      bytes  8..16 : cumulative_gas (u64 LE)
      bytes 16..272: logs_bloom (256 bytes)
      bytes 272..280: logs_rlp_len (u64 LE)
      bytes 280..   : logs_rlp
    Output layout (256 B ziskemu cap):
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : encoded receipt total length
      bytes 16..   : encoded receipt bytes (truncated to fit) -/
def ziskReceiptEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # status\n" ++
  "  ld a1, 16(a7)               # cumulative_gas\n" ++
  "  addi a2, a7, 24             # logs_bloom ptr (256 B)\n" ++
  "  ld a4, 280(a7)              # logs_rlp_len\n" ++
  "  addi a3, a7, 288            # logs_rlp ptr\n" ++
  "  li a5, 0xa0010010           # output ptr\n" ++
  "  li a6, 0xa0010008           # out length ptr\n" ++
  "  jal ra, receipt_encode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lre_pdone\n" ++
  rlpEncodeU64Function ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  receiptEncodeFunction ++ "\n" ++
  ".Lre_pdone:"

def ziskReceiptEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "re_field_len:\n" ++
  "  .zero 8\n" ++
  "re_cursor:\n" ++
  "  .zero 8\n" ++
  "re_total_payload:\n" ++
  "  .zero 8\n" ++
  "re_payload_buf:\n" ++
  "  .zero 16384"



/-! ## typed_receipt_encode -- EIP-2718 envelope helper

    Encode a typed transaction receipt as `type_byte || receipt_encode(...)`.
    EIP-2718 receipt trie values are the typed envelope bytes, not an RLP list
    containing the type byte. This helper deliberately delegates the inner
    payload to `receipt_encode` so status, cumulative gas, logs_bloom, and logs
    keep exactly the same semantics as legacy receipts.

    Calling convention:
      a0 (input)  : receipt type byte (1..255; low byte is used)
      a1 (input)  : status (u64)
      a2 (input)  : cumulative_gas_used (u64)
      a3 (input)  : logs_bloom ptr (exactly 256 bytes)
      a4 (input)  : logs_rlp ptr (pre-encoded list)
      a5 (input)  : logs_rlp byte length
      a6 (input)  : output buffer ptr
      a7 (input)  : u64 out length ptr (total bytes written)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def typedReceiptEncodeFunction : String :=
  "typed_receipt_encode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # type byte\n" ++
  "  mv s1, a6                   # output ptr\n" ++
  "  mv s2, a7                   # out length ptr\n" ++
  "  sb s0, 0(s1)                # envelope type byte\n" ++
  "  mv s3, a1                   # status\n" ++
  "  mv s4, a2                   # cumulative gas\n" ++
  "  mv s5, a3                   # logs bloom ptr\n" ++
  "  mv s6, a4                   # logs rlp ptr\n" ++
  "  mv a0, s3\n" ++
  "  mv a1, s4\n" ++
  "  mv a2, s5\n" ++
  "  mv a3, s6\n" ++
  "  mv a4, a5                   # logs rlp len\n" ++
  "  addi a5, s1, 1              # inner receipt output after type byte\n" ++
  "  la a6, tre_inner_len\n" ++
  "  jal ra, receipt_encode\n" ++
  "  la t0, tre_inner_len; ld t1, 0(t0)\n" ++
  "  addi t1, t1, 1\n" ++
  "  sd t1, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_typed_receipt_encode`: probe BuildUnit.
    Input layout:
      bytes   0.. 8 : type byte in low u64
      bytes   8..16 : status
      bytes  16..24 : cumulative_gas
      bytes  24..280: logs_bloom
      bytes 280..288: logs_rlp_len
      bytes 288..   : logs_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : bytes_written
      bytes 16..   : typed receipt bytes, capped by ziskemu output. -/
def ziskTypedReceiptEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld t0, 8(a3)                # type byte\n" ++
  "  ld t1, 16(a3)               # status\n" ++
  "  ld t2, 24(a3)               # cumulative gas\n" ++
  "  addi t3, a3, 32             # logs bloom ptr\n" ++
  "  ld t4, 288(a3)              # logs_rlp_len\n" ++
  "  addi t5, a3, 296            # logs_rlp ptr\n" ++
  "  mv a0, t0\n" ++
  "  mv a1, t1\n" ++
  "  mv a2, t2\n" ++
  "  mv a3, t3\n" ++
  "  mv a4, t5\n" ++
  "  mv a5, t4\n" ++
  "  li a6, 0xa0010010           # output typed receipt bytes\n" ++
  "  li a7, 0xa0010008           # out length ptr\n" ++
  "  jal ra, typed_receipt_encode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltre_pdone\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpEncodeU64Function ++ "\n" ++
  receiptEncodeFunction ++ "\n" ++
  typedReceiptEncodeFunction ++ "\n" ++
  ".Ltre_pdone:"

def ziskTypedReceiptEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "re_cursor:\n" ++
  "  .zero 8\n" ++
  "re_field_len:\n" ++
  "  .zero 8\n" ++
  "re_total_payload:\n" ++
  "  .zero 8\n" ++
  "tre_inner_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "re_payload_buf:\n" ++
  "  .zero 16384"


end EvmAsm.Codegen
