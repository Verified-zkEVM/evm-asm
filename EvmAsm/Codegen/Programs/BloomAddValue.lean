/-
  EvmAsm.Codegen.Programs.BloomAddValue

  Atomic log-bloom helper split out of `Bloom.lean`.

  Hosts:
    K148  bloom_add_value

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bloom_add_value -- PR-K148

    Add a single value to a 2048-bit (256-byte) Ethereum log
    bloom filter, following the yellow-paper / EIP-2718
    definition:

      1. h = keccak256(value)
      2. for idx in {0, 2, 4}:
           raw     = u16(h[idx..idx+2]) & 0x7FF      -- low 11 bits
           bit     = 0x7FF - raw                     -- inverted
           byte_i  = bit / 8
           bit_pos = 7 - (bit mod 8)                 -- MSB-first in byte
           bloom[byte_i] |= 1 << bit_pos

    Called twice for each log:
      * once with `value = log.address` (20 bytes)
      * once per topic with `value = topic` (32 bytes)

    Building block for `logs_bloom` construction in receipt
    encoding, which in turn feeds `block.bloom` (the per-block
    bloom = OR of every receipt's bloom). Used by:
      * `apply_body` when assembling each tx's receipt.
      * `block_validate_logs_bloom` to recompute the header's
        bloom field from receipts.

    Composes:
      - `zkvm_keccak256` (HashBridge) — hashes the value.

    Calling convention:
      a0 (input)  : bloom ptr (256 bytes, mutable, in-place OR)
      a1 (input)  : value ptr
      a2 (input)  : value byte length
      ra (input)  : return
      a0 (output) : 0 (always succeeds).

    Bloom is mutated in place; the caller owns the buffer and
    is responsible for zero-initialising it before the first
    `bloom_add_value` call of a logs sequence. -/
def bloomAddValueFunction : String :=
  "bloom_add_value:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # bloom ptr\n" ++
  "  mv s1, a1                   # value ptr\n" ++
  "  mv s2, a2                   # value len\n" ++
  "  # ---- Compute keccak256(value) → bav_hash ----\n" ++
  "  mv a0, s1; mv a1, s2\n" ++
  "  la a2, bav_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # ---- Set three bits derived from h[0..6] ----\n" ++
  "  la t0, bav_hash\n" ++
  "  li t1, 0                    # idx loop counter (0, 2, 4)\n" ++
  ".Lbav_loop:\n" ++
  "  li t2, 6\n" ++
  "  bge t1, t2, .Lbav_done\n" ++
  "  add t3, t0, t1\n" ++
  "  lbu t4, 0(t3)               # hi byte\n" ++
  "  lbu t5, 1(t3)               # lo byte\n" ++
  "  slli t4, t4, 8\n" ++
  "  or  t4, t4, t5              # raw_word\n" ++
  "  li  t5, 0x7ff\n" ++
  "  and t4, t4, t5              # raw_bit (0..2047)\n" ++
  "  sub t4, t5, t4              # bit_index = 0x7ff - raw_bit\n" ++
  "  srli t5, t4, 3              # byte_index = bit_index / 8\n" ++
  "  andi t6, t4, 7              # bit_index mod 8\n" ++
  "  li  t4, 7\n" ++
  "  sub t6, t4, t6              # bit_pos = 7 - (bit_index mod 8)\n" ++
  "  li  t4, 1\n" ++
  "  sll t6, t4, t6              # bit_mask = 1 << bit_pos\n" ++
  "  add t5, s0, t5              # &bloom[byte_index]\n" ++
  "  lbu t4, 0(t5)\n" ++
  "  or  t4, t4, t6\n" ++
  "  sb  t4, 0(t5)\n" ++
  "  addi t1, t1, 2\n" ++
  "  j .Lbav_loop\n" ++
  ".Lbav_done:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_bloom_add_value`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : value_len
      bytes  8..   : value bytes
    Output layout:
      bytes  0..256 : zero-initialised bloom, then bloom_add_value
                      run once on the supplied value. -/
def ziskBloomAddValuePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a2, 8(a3)                # value_len\n" ++
  "  addi a1, a3, 16             # value ptr\n" ++
  "  li a0, 0xa0010000           # output bloom ptr\n" ++
  "  jal ra, bloom_add_value\n" ++
  "  j .Lbav_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bloomAddValueFunction ++ "\n" ++
  ".Lbav_pdone:"

def ziskBloomAddValueDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bav_hash:\n" ++
  "  .zero 32"

def ziskBloomAddValueProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBloomAddValuePrologue
  dataAsm     := ziskBloomAddValueDataSection
}

end EvmAsm.Codegen
