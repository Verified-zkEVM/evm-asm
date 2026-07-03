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
#guard rlpEncodeU64_prog.length = 51
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

def ziskRlpEncodeU64ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpEncodeU64Prologue
  dataAsm     := ziskRlpEncodeU64DataSection
}

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
def receiptEncodeFunction : String :=
  "receipt_encode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # status\n" ++
  "  mv s1, a1                   # cumulative_gas\n" ++
  "  mv s2, a2                   # bloom ptr\n" ++
  "  mv s3, a3                   # logs_rlp ptr\n" ++
  "  mv s4, a4                   # logs_rlp len\n" ++
  "  mv s5, a5                   # output ptr\n" ++
  "  mv s6, a6                   # out_length ptr\n" ++
  "  # The running cursor (payload offset within re_payload_buf) is\n" ++
  "  # stashed to `re_cursor` across `jal` calls since t-registers are\n" ++
  "  # caller-saved and the encode helpers clobber them.\n" ++
  "  la t0, re_cursor; sd zero, 0(t0)\n" ++
  "  # ---- Step 1: encode status into re_payload_buf[0..] ----\n" ++
  "  mv a0, s0\n" ++
  "  la a1, re_payload_buf\n" ++
  "  la a2, re_field_len\n" ++
  "  jal ra, rlp_encode_u64\n" ++
  "  la t0, re_field_len; ld t1, 0(t0)         # status_len\n" ++
  "  la t0, re_cursor; sd t1, 0(t0)            # cursor = status_len\n" ++
  "  # ---- Step 2: encode cumulative_gas at re_payload_buf[cursor] ----\n" ++
  "  la t0, re_cursor; ld t2, 0(t0)\n" ++
  "  mv a0, s1\n" ++
  "  la a1, re_payload_buf; add a1, a1, t2\n" ++
  "  la a2, re_field_len\n" ++
  "  jal ra, rlp_encode_u64\n" ++
  "  la t0, re_field_len; ld t1, 0(t0)         # gas_len\n" ++
  "  la t0, re_cursor; ld t2, 0(t0)\n" ++
  "  add t2, t2, t1\n" ++
  "  la t0, re_cursor; sd t2, 0(t0)\n" ++
  "  # ---- Step 3: encode bloom (256 B) ----\n" ++
  "  mv a0, s2; li a1, 256\n" ++
  "  la a2, re_payload_buf; add a2, a2, t2\n" ++
  "  la a3, re_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, re_field_len; ld t1, 0(t0)         # bloom_enc_len\n" ++
  "  la t0, re_cursor; ld t2, 0(t0)\n" ++
  "  add t2, t2, t1\n" ++
  "  # ---- Step 4: copy logs_rlp verbatim ----\n" ++
  "  la t3, re_payload_buf; add t3, t3, t2     # dst\n" ++
  "  mv t4, s3                                 # src\n" ++
  "  mv t5, s4                                 # remaining bytes\n" ++
  ".Lre_logs_cp:\n" ++
  "  beqz t5, .Lre_logs_done\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lre_logs_cp\n" ++
  ".Lre_logs_done:\n" ++
  "  add t2, t2, s4                            # total payload len\n" ++
  "  # Stash total_payload before the next jal clobbers caller-saved t2.\n" ++
  "  la t0, re_total_payload; sd t2, 0(t0)\n" ++
  "  # ---- Step 5: write outer list prefix at output[0..] ----\n" ++
  "  mv a0, t2; mv a1, s5\n" ++
  "  la a2, re_field_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, re_field_len; ld t1, 0(t0)        # outer_prefix_len\n" ++
  "  # ---- Step 6: copy re_payload_buf[..total_payload] to output[prefix_len..] ----\n" ++
  "  # Total payload was last stashed in t2; restore via .data\n" ++
  "  # Actually we lost t2 across jal. Re-derive: total_payload =\n" ++
  "  # bytes_written - bytes_p, but cleaner to re-compute it from\n" ++
  "  # re_payload_buf metadata. Save total_payload before jal next time.\n" ++
  "  # Use the stashed value: we'll save t2 to .data BEFORE the\n" ++
  "  # rlp_encode_list_prefix call.\n" ++
  "  # (Fixed by re-reading the saved payload total below.)\n" ++
  "  la t0, re_total_payload; ld t2, 0(t0)\n" ++
  "  add t3, s5, t1                            # dst = output + prefix_len\n" ++
  "  la t4, re_payload_buf                     # src\n" ++
  "  mv t5, t2                                 # remaining\n" ++
  ".Lre_body_cp:\n" ++
  "  beqz t5, .Lre_body_done\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lre_body_cp\n" ++
  ".Lre_body_done:\n" ++
  "  # total_written = outer_prefix_len + total_payload\n" ++
  "  add t1, t1, t2\n" ++
  "  sd t1, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

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

def ziskReceiptEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskReceiptEncodePrologue
  dataAsm     := ziskReceiptEncodeDataSection
}


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

def ziskTypedReceiptEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTypedReceiptEncodePrologue
  dataAsm     := ziskTypedReceiptEncodeDataSection
}

end EvmAsm.Codegen
