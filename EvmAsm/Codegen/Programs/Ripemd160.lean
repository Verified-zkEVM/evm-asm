/-
  EvmAsm.Codegen.Programs.Ripemd160

  Software RIPEMD-160 kernel behind the 0x03 precompile's
  `zkvm_ripemd160(data, len, output)` ABI.

  ZisK has NO RIPEMD-160 accelerator (the installed ziskemu 0.16.0
  syscall surface 0x800..0x819 covers keccak-f / sha256-f / arith /
  secp256k1 / secp256r1 / bn254 / bls12-381 / blake2b only), so unlike
  `zkvm_sha256` this is a pure RV64 software implementation: the
  standard two-line (left/right) 5x16-step compression, table-driven
  over the message-selection / rotation / round-constant tables in
  `ripemd160DataFragment`, with Merkle-Damgård padding (0x80, zeros,
  64-bit LITTLE-endian bit length).

  Cost is ~5.3k instructions per 64-byte block — negligible against the
  1e9 stateless step budget for EEST-sized inputs.

  ABI (matches zkvm-standards `zkvm_ripemd160`, zkvm_accelerators.h:218):
    a0 = data ptr (arbitrary alignment — input is byte-copied into the
         8-aligned `ripemd_w_input` staging block, so all loads stay
         naturally aligned per the project invariant)
    a1 = byte length
    a2 = output ptr (32 bytes: 12 zero bytes ++ 20-byte hash, i.e. the
         EVM left-padded returndata encoding; must be 4-aligned — the
         dispatcher passes `evm_precompile_frame + 16`)
    returns a0 = 0 (ZKVM_EOK; RIPEMD-160 cannot fail on valid memory)

  Clobbers t0..t6, a0..a7; saves/restores s0..s9 + ra on the caller's
  stack (s10/s11 are preserved untouched for the dispatcher's saved
  x10/x12).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- The `zkvm_ripemd160` function text: driver (`zkvm_ripemd160`),
    compression (`ripemd_compress`), and the shared single-line walker
    (`ripemd_line160`, s9 = 0 left / 1 right). Pairs with
    `ripemd160DataFragment` in the data section. -/
def zkvmRipemd160Function : String :=
  "zkvm_ripemd160:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp)\n" ++
  "  sd s6, 56(sp)\n" ++
  "  sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  sd s9, 80(sp)\n" ++
  "  # s0 = data ptr; s1 = remaining len; s2 = output ptr;\n" ++
  "  # s3 = bit length; s4 = ripemd_w_input staging base.\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  slli s3, a1, 3\n" ++
  "  la s4, ripemd_w_input\n" ++
  "  # initialise chaining state from the RIPEMD-160 IV\n" ++
  "  la t1, ripemd_w_state\n" ++
  "  li t2, 0x67452301\n" ++
  "  sw t2, 0(t1)\n" ++
  "  li t2, 0xefcdab89\n" ++
  "  sw t2, 4(t1)\n" ++
  "  li t2, 0x98badcfe\n" ++
  "  sw t2, 8(t1)\n" ++
  "  li t2, 0x10325476\n" ++
  "  sw t2, 12(t1)\n" ++
  "  li t2, 0xc3d2e1f0\n" ++
  "  sw t2, 16(t1)\n" ++
  "  # absorb full 64-byte blocks (byte-copied: input alignment is arbitrary)\n" ++
  ".Lrip_blk_loop:\n" ++
  "  li t0, 64\n" ++
  "  bltu s1, t0, .Lrip_final\n" ++
  "  mv t1, s0\n" ++
  "  mv t2, s4\n" ++
  "  li t3, 64\n" ++
  ".Lrip_bcopy64:\n" ++
  "  lbu t4, 0(t1)\n" ++
  "  sb t4, 0(t2)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  bnez t3, .Lrip_bcopy64\n" ++
  "  jal ra, ripemd_compress\n" ++
  "  addi s0, s0, 64\n" ++
  "  addi s1, s1, -64\n" ++
  "  j .Lrip_blk_loop\n" ++
  ".Lrip_final:\n" ++
  "  # zero the staging block\n" ++
  "  sd zero, 0(s4)\n" ++
  "  sd zero, 8(s4)\n" ++
  "  sd zero, 16(s4)\n" ++
  "  sd zero, 24(s4)\n" ++
  "  sd zero, 32(s4)\n" ++
  "  sd zero, 40(s4)\n" ++
  "  sd zero, 48(s4)\n" ++
  "  sd zero, 56(s4)\n" ++
  "  # byte-copy the remaining s1 (< 64) bytes\n" ++
  "  mv t1, s0\n" ++
  "  mv t2, s4\n" ++
  "  mv t3, s1\n" ++
  ".Lrip_bcopyrem:\n" ++
  "  beqz t3, .Lrip_pad\n" ++
  "  lbu t4, 0(t1)\n" ++
  "  sb t4, 0(t2)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lrip_bcopyrem\n" ++
  ".Lrip_pad:\n" ++
  "  # 0x80 terminator at offset s1\n" ++
  "  add t1, s4, s1\n" ++
  "  li t2, 0x80\n" ++
  "  sb t2, 0(t1)\n" ++
  "  # remainder >= 56: compress this block, then a length-only block\n" ++
  "  li t0, 56\n" ++
  "  bltu s1, t0, .Lrip_writelen\n" ++
  "  jal ra, ripemd_compress\n" ++
  "  sd zero, 0(s4)\n" ++
  "  sd zero, 8(s4)\n" ++
  "  sd zero, 16(s4)\n" ++
  "  sd zero, 24(s4)\n" ++
  "  sd zero, 32(s4)\n" ++
  "  sd zero, 40(s4)\n" ++
  "  sd zero, 48(s4)\n" ++
  "  sd zero, 56(s4)\n" ++
  ".Lrip_writelen:\n" ++
  "  # 64-bit LITTLE-endian bit length at offset 56 (8-aligned store)\n" ++
  "  sd s3, 56(s4)\n" ++
  "  jal ra, ripemd_compress\n" ++
  "  # output: 12 zero bytes ++ h0..h4 (each little-endian = sw)\n" ++
  "  sw zero, 0(s2)\n" ++
  "  sw zero, 4(s2)\n" ++
  "  sw zero, 8(s2)\n" ++
  "  la t1, ripemd_w_state\n" ++
  "  lw t2, 0(t1)\n" ++
  "  sw t2, 12(s2)\n" ++
  "  lw t2, 4(t1)\n" ++
  "  sw t2, 16(s2)\n" ++
  "  lw t2, 8(t1)\n" ++
  "  sw t2, 20(s2)\n" ++
  "  lw t2, 12(t1)\n" ++
  "  sw t2, 24(s2)\n" ++
  "  lw t2, 16(t1)\n" ++
  "  sw t2, 28(s2)\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp)\n" ++
  "  ld s6, 56(sp)\n" ++
  "  ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n" ++
  "# One RIPEMD-160 compression of ripemd_w_input into ripemd_w_state.\n" ++
  "# Clobbers a3..a7, t0..t6, s5..s9.\n" ++
  "ripemd_compress:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  li s9, 0\n" ++
  "  jal ra, ripemd_line160\n" ++
  "  li s9, 1\n" ++
  "  jal ra, ripemd_line160\n" ++
  "  # combine: h0' = h1+cL+dR; h1' = h2+dL+eR; h2' = h3+eL+aR;\n" ++
  "  #          h3' = h4+aL+bR; h4' = h0+bL+cR\n" ++
  "  la t1, ripemd_w_state\n" ++
  "  lw t2, 0(t1)\n" ++
  "  lw t3, 4(t1)\n" ++
  "  lw t4, 8(t1)\n" ++
  "  lw t5, 12(t1)\n" ++
  "  lw t6, 16(t1)\n" ++
  "  la t0, ripemd_line_out\n" ++
  "  lw a3, 0(t0)\n" ++
  "  lw a4, 4(t0)\n" ++
  "  lw a5, 8(t0)\n" ++
  "  lw a6, 12(t0)\n" ++
  "  lw a7, 16(t0)\n" ++
  "  lw s5, 20(t0)\n" ++
  "  lw s6, 24(t0)\n" ++
  "  lw s7, 28(t0)\n" ++
  "  lw s8, 32(t0)\n" ++
  "  lw s9, 36(t0)\n" ++
  "  addw t3, t3, a5\n" ++
  "  addw t3, t3, s8\n" ++
  "  addw t4, t4, a6\n" ++
  "  addw t4, t4, s9\n" ++
  "  addw t5, t5, a7\n" ++
  "  addw t5, t5, s5\n" ++
  "  addw t6, t6, a3\n" ++
  "  addw t6, t6, s6\n" ++
  "  addw t2, t2, a4\n" ++
  "  addw t2, t2, s7\n" ++
  "  sw t3, 0(t1)\n" ++
  "  sw t4, 4(t1)\n" ++
  "  sw t5, 8(t1)\n" ++
  "  sw t6, 12(t1)\n" ++
  "  sw t2, 16(t1)\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret\n" ++
  "# One 80-step line. s9 = 0 (left) / 1 (right) selects the table\n" ++
  "# halves, round constants, and boolean-function order (left round i\n" ++
  "# uses f_i, right uses f_{5-i}). State A..E in a4 a5 a6 a7 t0;\n" ++
  "# result stored at ripemd_line_out + 20*s9.\n" ++
  "ripemd_line160:\n" ++
  "  li t2, 80\n" ++
  "  mul t2, t2, s9\n" ++
  "  la s5, ripemd_rho\n" ++
  "  add s5, s5, t2\n" ++
  "  la s6, ripemd_shift\n" ++
  "  add s6, s6, t2\n" ++
  "  li t2, 20\n" ++
  "  mul t2, t2, s9\n" ++
  "  la s7, ripemd_k\n" ++
  "  add s7, s7, t2\n" ++
  "  la s8, ripemd_w_input\n" ++
  "  la t1, ripemd_w_state\n" ++
  "  lw a4, 0(t1)\n" ++
  "  lw a5, 4(t1)\n" ++
  "  lw a6, 8(t1)\n" ++
  "  lw a7, 12(t1)\n" ++
  "  lw t0, 16(t1)\n" ++
  "  li a3, 0\n" ++
  ".Lrip_step:\n" ++
  "  lbu t1, 0(s5)\n" ++              -- message word index r[j]
  "  addi s5, s5, 1\n" ++
  "  lbu t2, 0(s6)\n" ++              -- rotation amount s[j]
  "  addi s6, s6, 1\n" ++
  "  srli t3, a3, 4\n" ++             -- round = j / 16
  "  slli t4, t3, 2\n" ++
  "  add t4, s7, t4\n" ++
  "  lw t5, 0(t4)\n" ++               -- K[line][round]
  "  beqz s9, .Lrip_fsel\n" ++
  "  li t4, 4\n" ++
  "  sub t3, t4, t3\n" ++             -- right line: f index = 4 - round
  ".Lrip_fsel:\n" ++
  "  beqz t3, .Lrip_f0\n" ++
  "  li t4, 1\n" ++
  "  beq t3, t4, .Lrip_f1\n" ++
  "  li t4, 2\n" ++
  "  beq t3, t4, .Lrip_f2\n" ++
  "  li t4, 3\n" ++
  "  beq t3, t4, .Lrip_f3\n" ++
  "  xori t4, a7, -1\n" ++            -- f5 = B ^ (C | ~D)
  "  or t4, a6, t4\n" ++
  "  xor t6, a5, t4\n" ++
  "  j .Lrip_fdone\n" ++
  ".Lrip_f0:\n" ++                    -- f1 = B ^ C ^ D
  "  xor t6, a5, a6\n" ++
  "  xor t6, t6, a7\n" ++
  "  j .Lrip_fdone\n" ++
  ".Lrip_f1:\n" ++                    -- f2 = (B & C) | (~B & D)
  "  and t6, a5, a6\n" ++
  "  xori t4, a5, -1\n" ++
  "  and t4, t4, a7\n" ++
  "  or t6, t6, t4\n" ++
  "  j .Lrip_fdone\n" ++
  ".Lrip_f2:\n" ++                    -- f3 = (B | ~C) ^ D
  "  xori t4, a6, -1\n" ++
  "  or t4, a5, t4\n" ++
  "  xor t6, t4, a7\n" ++
  "  j .Lrip_fdone\n" ++
  ".Lrip_f3:\n" ++                    -- f4 = (B & D) | (C & ~D)
  "  and t6, a5, a7\n" ++
  "  xori t4, a7, -1\n" ++
  "  and t4, a6, t4\n" ++
  "  or t6, t6, t4\n" ++
  ".Lrip_fdone:\n" ++
  "  slli t1, t1, 2\n" ++
  "  add t1, s8, t1\n" ++
  "  lw t1, 0(t1)\n" ++               -- X[r[j]] (LE word from aligned staging)
  "  addw t6, t6, a4\n" ++            -- T = A + f + X + K
  "  addw t6, t6, t1\n" ++
  "  addw t6, t6, t5\n" ++
  "  sllw t4, t6, t2\n" ++            -- T = rol_{s[j]}(T)
  "  li t5, 32\n" ++
  "  sub t5, t5, t2\n" ++
  "  srlw t6, t6, t5\n" ++
  "  or t6, t4, t6\n" ++
  "  addw t6, t6, t0\n" ++            -- T += E
  "  mv a4, t0\n" ++                  -- A = E
  "  mv t0, a7\n" ++                  -- E = D
  "  slliw t4, a6, 10\n" ++           -- D = rol10(C)
  "  srliw t5, a6, 22\n" ++
  "  or a7, t4, t5\n" ++
  "  mv a6, a5\n" ++                  -- C = B
  "  mv a5, t6\n" ++                  -- B = T
  "  addi a3, a3, 1\n" ++
  "  li t4, 80\n" ++
  "  bltu a3, t4, .Lrip_step\n" ++
  "  la t1, ripemd_line_out\n" ++
  "  li t2, 20\n" ++
  "  mul t2, t2, s9\n" ++
  "  add t1, t1, t2\n" ++
  "  sw a4, 0(t1)\n" ++
  "  sw a5, 4(t1)\n" ++
  "  sw a6, 8(t1)\n" ++
  "  sw a7, 12(t1)\n" ++
  "  sw t0, 16(t1)\n" ++
  "  ret"

/-- Data labels for `zkvm_ripemd160`: chaining state + 64-byte aligned
    staging block + per-line result scratch, then the standard RIPEMD-160
    message-selection (`ripemd_rho`), rotation (`ripemd_shift`), and
    round-constant (`ripemd_k`, LE u32) tables — left line first 80 / 5
    entries, right line second. -/
def ripemd160DataFragment : String :=
  ".balign 8\n" ++
  "ripemd_w_state:\n" ++
  "  .zero 24\n" ++
  ".balign 8\n" ++
  "ripemd_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ripemd_line_out:\n" ++
  "  .zero 40\n" ++
  "ripemd_rho:\n" ++
  -- left line message word order
  "  .byte 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15\n" ++
  "  .byte 7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8\n" ++
  "  .byte 3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12\n" ++
  "  .byte 1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2\n" ++
  "  .byte 4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13\n" ++
  -- right line message word order
  "  .byte 5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12\n" ++
  "  .byte 6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2\n" ++
  "  .byte 15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13\n" ++
  "  .byte 8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14\n" ++
  "  .byte 12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11\n" ++
  "ripemd_shift:\n" ++
  -- left line rotation amounts
  "  .byte 11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8\n" ++
  "  .byte 7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12\n" ++
  "  .byte 11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5\n" ++
  "  .byte 11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12\n" ++
  "  .byte 9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6\n" ++
  -- right line rotation amounts
  "  .byte 8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6\n" ++
  "  .byte 9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11\n" ++
  "  .byte 9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5\n" ++
  "  .byte 15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8\n" ++
  "  .byte 8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11\n" ++
  ".balign 4\n" ++
  "ripemd_k:\n" ++
  -- left K: 0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e (LE)
  "  .byte 0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x99,0x79,0x82,0x5a\n" ++
  "  .byte 0xa1,0xeb,0xd9,0x6e\n" ++
  "  .byte 0xdc,0xbc,0x1b,0x8f\n" ++
  "  .byte 0x4e,0xfd,0x53,0xa9\n" ++
  -- right K': 0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000 (LE)
  "  .byte 0xe6,0x8b,0xa2,0x50\n" ++
  "  .byte 0x24,0xd1,0x4d,0x5c\n" ++
  "  .byte 0xf3,0x3e,0x70,0x6d\n" ++
  "  .byte 0xe9,0x76,0x6d,0x7a\n" ++
  "  .byte 0x00,0x00,0x00,0x00\n"

/-- Probe: hash whatever is at `INPUT_ADDR + 16` (length u64 LE at
    `INPUT_ADDR + 8`, ziskemu input-region layout) and write the 32-byte
    left-padded digest to `OUTPUT_ADDR`. Mirrors
    `ziskSha256FromInputProbeUnit`. -/
def ziskRipemd160FromInputPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)\n" ++
  "  addi a0, a3, 16\n" ++
  "  li a2, 0xa0010000\n" ++
  "  jal ra, zkvm_ripemd160\n" ++
  "  j .Lzkrip_done\n" ++
  zkvmRipemd160Function ++ "\n" ++
  ".Lzkrip_done:"

def ziskRipemd160FromInputDataSection : String :=
  ".section .data\n" ++
  ripemd160DataFragment


end EvmAsm.Codegen
