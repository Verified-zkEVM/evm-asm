/-
  EvmAsm.Codegen.Programs.Ssz

  SSZ merkleization kernels: the precomputed zero-hashes table plus the
  hash-tree-root building blocks (merkleize, pack_bytes, and the
  `hash_tree_root` variants) that back the shims in
  `EvmAsm.Stateless.SSZ.HashTreeRoot.Program`.

  Extracted from `EvmAsm.Codegen.Programs` so the registry hub stays
  manageable.
 -/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Stateless.SSZ.HashTreeRoot.Program
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## ssz_zero_hashes — PR-S5 precomputed SSZ Z_0..Z_31 table

    Pre-computed SSZ "zero hashes" sequence:
      Z_0 = 0x00..00 (32 zero bytes)
      Z_i = sha256(Z_{i-1} ‖ Z_{i-1})

    Emitted as a single 1024-byte `.rodata` block. Entry `i` lives
    at `ssz_zero_hashes + i * 32`. Cached at codegen time so the
    PR-S6 merkleize loop can short-circuit all-zero subtrees of
    depth ≤ 31 without re-running SHA-256.

    Values generated once with Python:

        import hashlib
        z = [b"\x00" * 32]
        for _ in range(31):
            z.append(hashlib.sha256(z[-1] + z[-1]).digest())

    `z[1]` matches the PR-S4 fixture (`f5a5fd42..fb4b`).
 -/
def sszZeroHashesDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "ssz_zero_hashes:\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00    # Z_0\n" ++
  "  .byte 0xf5, 0xa5, 0xfd, 0x42, 0xd1, 0x6a, 0x20, 0x30, 0x27, 0x98, 0xef, 0x6e, 0xd3, 0x09, 0x97, 0x9b, 0x43, 0x00, 0x3d, 0x23, 0x20, 0xd9, 0xf0, 0xe8, 0xea, 0x98, 0x31, 0xa9, 0x27, 0x59, 0xfb, 0x4b    # Z_1\n" ++
  "  .byte 0xdb, 0x56, 0x11, 0x4e, 0x00, 0xfd, 0xd4, 0xc1, 0xf8, 0x5c, 0x89, 0x2b, 0xf3, 0x5a, 0xc9, 0xa8, 0x92, 0x89, 0xaa, 0xec, 0xb1, 0xeb, 0xd0, 0xa9, 0x6c, 0xde, 0x60, 0x6a, 0x74, 0x8b, 0x5d, 0x71    # Z_2\n" ++
  "  .byte 0xc7, 0x80, 0x09, 0xfd, 0xf0, 0x7f, 0xc5, 0x6a, 0x11, 0xf1, 0x22, 0x37, 0x06, 0x58, 0xa3, 0x53, 0xaa, 0xa5, 0x42, 0xed, 0x63, 0xe4, 0x4c, 0x4b, 0xc1, 0x5f, 0xf4, 0xcd, 0x10, 0x5a, 0xb3, 0x3c    # Z_3\n" ++
  "  .byte 0x53, 0x6d, 0x98, 0x83, 0x7f, 0x2d, 0xd1, 0x65, 0xa5, 0x5d, 0x5e, 0xea, 0xe9, 0x14, 0x85, 0x95, 0x44, 0x72, 0xd5, 0x6f, 0x24, 0x6d, 0xf2, 0x56, 0xbf, 0x3c, 0xae, 0x19, 0x35, 0x2a, 0x12, 0x3c    # Z_4\n" ++
  "  .byte 0x9e, 0xfd, 0xe0, 0x52, 0xaa, 0x15, 0x42, 0x9f, 0xae, 0x05, 0xba, 0xd4, 0xd0, 0xb1, 0xd7, 0xc6, 0x4d, 0xa6, 0x4d, 0x03, 0xd7, 0xa1, 0x85, 0x4a, 0x58, 0x8c, 0x2c, 0xb8, 0x43, 0x0c, 0x0d, 0x30    # Z_5\n" ++
  "  .byte 0xd8, 0x8d, 0xdf, 0xee, 0xd4, 0x00, 0xa8, 0x75, 0x55, 0x96, 0xb2, 0x19, 0x42, 0xc1, 0x49, 0x7e, 0x11, 0x4c, 0x30, 0x2e, 0x61, 0x18, 0x29, 0x0f, 0x91, 0xe6, 0x77, 0x29, 0x76, 0x04, 0x1f, 0xa1    # Z_6\n" ++
  "  .byte 0x87, 0xeb, 0x0d, 0xdb, 0xa5, 0x7e, 0x35, 0xf6, 0xd2, 0x86, 0x67, 0x38, 0x02, 0xa4, 0xaf, 0x59, 0x75, 0xe2, 0x25, 0x06, 0xc7, 0xcf, 0x4c, 0x64, 0xbb, 0x6b, 0xe5, 0xee, 0x11, 0x52, 0x7f, 0x2c    # Z_7\n" ++
  "  .byte 0x26, 0x84, 0x64, 0x76, 0xfd, 0x5f, 0xc5, 0x4a, 0x5d, 0x43, 0x38, 0x51, 0x67, 0xc9, 0x51, 0x44, 0xf2, 0x64, 0x3f, 0x53, 0x3c, 0xc8, 0x5b, 0xb9, 0xd1, 0x6b, 0x78, 0x2f, 0x8d, 0x7d, 0xb1, 0x93    # Z_8\n" ++
  "  .byte 0x50, 0x6d, 0x86, 0x58, 0x2d, 0x25, 0x24, 0x05, 0xb8, 0x40, 0x01, 0x87, 0x92, 0xca, 0xd2, 0xbf, 0x12, 0x59, 0xf1, 0xef, 0x5a, 0xa5, 0xf8, 0x87, 0xe1, 0x3c, 0xb2, 0xf0, 0x09, 0x4f, 0x51, 0xe1    # Z_9\n" ++
  "  .byte 0xff, 0xff, 0x0a, 0xd7, 0xe6, 0x59, 0x77, 0x2f, 0x95, 0x34, 0xc1, 0x95, 0xc8, 0x15, 0xef, 0xc4, 0x01, 0x4e, 0xf1, 0xe1, 0xda, 0xed, 0x44, 0x04, 0xc0, 0x63, 0x85, 0xd1, 0x11, 0x92, 0xe9, 0x2b    # Z_10\n" ++
  "  .byte 0x6c, 0xf0, 0x41, 0x27, 0xdb, 0x05, 0x44, 0x1c, 0xd8, 0x33, 0x10, 0x7a, 0x52, 0xbe, 0x85, 0x28, 0x68, 0x89, 0x0e, 0x43, 0x17, 0xe6, 0xa0, 0x2a, 0xb4, 0x76, 0x83, 0xaa, 0x75, 0x96, 0x42, 0x20    # Z_11\n" ++
  "  .byte 0xb7, 0xd0, 0x5f, 0x87, 0x5f, 0x14, 0x00, 0x27, 0xef, 0x51, 0x18, 0xa2, 0x24, 0x7b, 0xbb, 0x84, 0xce, 0x8f, 0x2f, 0x0f, 0x11, 0x23, 0x62, 0x30, 0x85, 0xda, 0xf7, 0x96, 0x0c, 0x32, 0x9f, 0x5f    # Z_12\n" ++
  "  .byte 0xdf, 0x6a, 0xf5, 0xf5, 0xbb, 0xdb, 0x6b, 0xe9, 0xef, 0x8a, 0xa6, 0x18, 0xe4, 0xbf, 0x80, 0x73, 0x96, 0x08, 0x67, 0x17, 0x1e, 0x29, 0x67, 0x6f, 0x8b, 0x28, 0x4d, 0xea, 0x6a, 0x08, 0xa8, 0x5e    # Z_13\n" ++
  "  .byte 0xb5, 0x8d, 0x90, 0x0f, 0x5e, 0x18, 0x2e, 0x3c, 0x50, 0xef, 0x74, 0x96, 0x9e, 0xa1, 0x6c, 0x77, 0x26, 0xc5, 0x49, 0x75, 0x7c, 0xc2, 0x35, 0x23, 0xc3, 0x69, 0x58, 0x7d, 0xa7, 0x29, 0x37, 0x84    # Z_14\n" ++
  "  .byte 0xd4, 0x9a, 0x75, 0x02, 0xff, 0xcf, 0xb0, 0x34, 0x0b, 0x1d, 0x78, 0x85, 0x68, 0x85, 0x00, 0xca, 0x30, 0x81, 0x61, 0xa7, 0xf9, 0x6b, 0x62, 0xdf, 0x9d, 0x08, 0x3b, 0x71, 0xfc, 0xc8, 0xf2, 0xbb    # Z_15\n" ++
  "  .byte 0x8f, 0xe6, 0xb1, 0x68, 0x92, 0x56, 0xc0, 0xd3, 0x85, 0xf4, 0x2f, 0x5b, 0xbe, 0x20, 0x27, 0xa2, 0x2c, 0x19, 0x96, 0xe1, 0x10, 0xba, 0x97, 0xc1, 0x71, 0xd3, 0xe5, 0x94, 0x8d, 0xe9, 0x2b, 0xeb    # Z_16\n" ++
  "  .byte 0x8d, 0x0d, 0x63, 0xc3, 0x9e, 0xba, 0xde, 0x85, 0x09, 0xe0, 0xae, 0x3c, 0x9c, 0x38, 0x76, 0xfb, 0x5f, 0xa1, 0x12, 0xbe, 0x18, 0xf9, 0x05, 0xec, 0xac, 0xfe, 0xcb, 0x92, 0x05, 0x76, 0x03, 0xab    # Z_17\n" ++
  "  .byte 0x95, 0xee, 0xc8, 0xb2, 0xe5, 0x41, 0xca, 0xd4, 0xe9, 0x1d, 0xe3, 0x83, 0x85, 0xf2, 0xe0, 0x46, 0x61, 0x9f, 0x54, 0x49, 0x6c, 0x23, 0x82, 0xcb, 0x6c, 0xac, 0xd5, 0xb9, 0x8c, 0x26, 0xf5, 0xa4    # Z_18\n" ++
  "  .byte 0xf8, 0x93, 0xe9, 0x08, 0x91, 0x77, 0x75, 0xb6, 0x2b, 0xff, 0x23, 0x29, 0x4d, 0xbb, 0xe3, 0xa1, 0xcd, 0x8e, 0x6c, 0xc1, 0xc3, 0x5b, 0x48, 0x01, 0x88, 0x7b, 0x64, 0x6a, 0x6f, 0x81, 0xf1, 0x7f    # Z_19\n" ++
  "  .byte 0xcd, 0xdb, 0xa7, 0xb5, 0x92, 0xe3, 0x13, 0x33, 0x93, 0xc1, 0x61, 0x94, 0xfa, 0xc7, 0x43, 0x1a, 0xbf, 0x2f, 0x54, 0x85, 0xed, 0x71, 0x1d, 0xb2, 0x82, 0x18, 0x3c, 0x81, 0x9e, 0x08, 0xeb, 0xaa    # Z_20\n" ++
  "  .byte 0x8a, 0x8d, 0x7f, 0xe3, 0xaf, 0x8c, 0xaa, 0x08, 0x5a, 0x76, 0x39, 0xa8, 0x32, 0x00, 0x14, 0x57, 0xdf, 0xb9, 0x12, 0x8a, 0x80, 0x61, 0x14, 0x2a, 0xd0, 0x33, 0x56, 0x29, 0xff, 0x23, 0xff, 0x9c    # Z_21\n" ++
  "  .byte 0xfe, 0xb3, 0xc3, 0x37, 0xd7, 0xa5, 0x1a, 0x6f, 0xbf, 0x00, 0xb9, 0xe3, 0x4c, 0x52, 0xe1, 0xc9, 0x19, 0x5c, 0x96, 0x9b, 0xd4, 0xe7, 0xa0, 0xbf, 0xd5, 0x1d, 0x5c, 0x5b, 0xed, 0x9c, 0x11, 0x67    # Z_22\n" ++
  "  .byte 0xe7, 0x1f, 0x0a, 0xa8, 0x3c, 0xc3, 0x2e, 0xdf, 0xbe, 0xfa, 0x9f, 0x4d, 0x3e, 0x01, 0x74, 0xca, 0x85, 0x18, 0x2e, 0xec, 0x9f, 0x3a, 0x09, 0xf6, 0xa6, 0xc0, 0xdf, 0x63, 0x77, 0xa5, 0x10, 0xd7    # Z_23\n" ++
  "  .byte 0x31, 0x20, 0x6f, 0xa8, 0x0a, 0x50, 0xbb, 0x6a, 0xbe, 0x29, 0x08, 0x50, 0x58, 0xf1, 0x62, 0x12, 0x21, 0x2a, 0x60, 0xee, 0xc8, 0xf0, 0x49, 0xfe, 0xcb, 0x92, 0xd8, 0xc8, 0xe0, 0xa8, 0x4b, 0xc0    # Z_24\n" ++
  "  .byte 0x21, 0x35, 0x2b, 0xfe, 0xcb, 0xed, 0xdd, 0xe9, 0x93, 0x83, 0x9f, 0x61, 0x4c, 0x3d, 0xac, 0x0a, 0x3e, 0xe3, 0x75, 0x43, 0xf9, 0xb4, 0x12, 0xb1, 0x61, 0x99, 0xdc, 0x15, 0x8e, 0x23, 0xb5, 0x44    # Z_25\n" ++
  "  .byte 0x61, 0x9e, 0x31, 0x27, 0x24, 0xbb, 0x6d, 0x7c, 0x31, 0x53, 0xed, 0x9d, 0xe7, 0x91, 0xd7, 0x64, 0xa3, 0x66, 0xb3, 0x89, 0xaf, 0x13, 0xc5, 0x8b, 0xf8, 0xa8, 0xd9, 0x04, 0x81, 0xa4, 0x67, 0x65    # Z_26\n" ++
  "  .byte 0x7c, 0xdd, 0x29, 0x86, 0x26, 0x82, 0x50, 0x62, 0x8d, 0x0c, 0x10, 0xe3, 0x85, 0xc5, 0x8c, 0x61, 0x91, 0xe6, 0xfb, 0xe0, 0x51, 0x91, 0xbc, 0xc0, 0x4f, 0x13, 0x3f, 0x2c, 0xea, 0x72, 0xc1, 0xc4    # Z_27\n" ++
  "  .byte 0x84, 0x89, 0x30, 0xbd, 0x7b, 0xa8, 0xca, 0xc5, 0x46, 0x61, 0x07, 0x21, 0x13, 0xfb, 0x27, 0x88, 0x69, 0xe0, 0x7b, 0xb8, 0x58, 0x7f, 0x91, 0x39, 0x29, 0x33, 0x37, 0x4d, 0x01, 0x7b, 0xcb, 0xe1    # Z_28\n" ++
  "  .byte 0x88, 0x69, 0xff, 0x2c, 0x22, 0xb2, 0x8c, 0xc1, 0x05, 0x10, 0xd9, 0x85, 0x32, 0x92, 0x80, 0x33, 0x28, 0xbe, 0x4f, 0xb0, 0xe8, 0x04, 0x95, 0xe8, 0xbb, 0x8d, 0x27, 0x1f, 0x5b, 0x88, 0x96, 0x36    # Z_29\n" ++
  "  .byte 0xb5, 0xfe, 0x28, 0xe7, 0x9f, 0x1b, 0x85, 0x0f, 0x86, 0x58, 0x24, 0x6c, 0xe9, 0xb6, 0xa1, 0xe7, 0xb4, 0x9f, 0xc0, 0x6d, 0xb7, 0x14, 0x3e, 0x8f, 0xe0, 0xb4, 0xf2, 0xb0, 0xc5, 0x52, 0x3a, 0x5c    # Z_30\n" ++
  "  .byte 0x98, 0x5e, 0x92, 0x9f, 0x70, 0xaf, 0x28, 0xd0, 0xbd, 0xd1, 0xa9, 0x0a, 0x80, 0x8f, 0x97, 0x7f, 0x59, 0x7c, 0x7c, 0x77, 0x8c, 0x48, 0x9e, 0x98, 0xd3, 0xbd, 0x89, 0x10, 0xd3, 0x1a, 0xc0, 0xf7    # Z_31"

/-! ## ssz_merkleize_pow2 — PR-S6 pair-hash reduction loop

    SSZ pairwise merkleization for a power-of-two chunk count.
    Implements:

        while n > 1:
            for i in 0..n/2:
                chunks[i] = sha256_pair(chunks[2i], chunks[2i+1])
            n = n / 2
        root = chunks[0]

    Reads `n * 32` bytes from the caller's input pointer into
    `ssz_merkleize_scratch` (a 1024-byte working buffer), then
    reduces in place. Final root is copied to the caller's output
    pointer; the scratch buffer's first 32 bytes hold the same
    root after the call (intentional, reusable by chained
    merkleizers).

    Calling convention:
      a0 (input)  : ptr to `n * 32` chunk bytes
      a1 (input)  : n (power of two; 1 ≤ n ≤ 32)
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (ZKVM_EOK)

    Clobbers t0..t6, a0..a2. Saves/restores s0..s6 and ra via
    its own 64-byte stack frame. Requires `sp` to point at
    writable RAM. -/
def sszMerkleizePow2_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x11,
    .MV .x22 .x12,
    .AUIPC .x21 (laHi GuestAddrs.ssz_merkleize_scratch (GuestAddrs.ssz_merkleize_pow2 + 44)),
    .ADDI .x21 .x21 (laLo GuestAddrs.ssz_merkleize_scratch (GuestAddrs.ssz_merkleize_pow2 + 44)),
    .MV .x5 .x10,
    .MV .x6 .x21,
    .SLLI .x7 .x8 (5 : BitVec 6),
    .BEQ .x7 .x0 (28 : BitVec 13),
    .LD .x28 .x5 (0 : BitVec 12),
    .SD .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (8 : BitVec 12),
    .ADDI .x7 .x7 (-8 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x5 (1 : Word),
    .BEQ .x8 .x5 (60 : BitVec 13),
    .SRLI .x9 .x8 (1 : BitVec 6),
    .MV .x18 .x21,
    .MV .x19 .x21,
    .BEQ .x9 .x0 (36 : BitVec 13),
    .MV .x10 .x18,
    .MV .x12 .x19,
    .LI .x11 (64 : Word),
    .JAL .x1 (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.ssz_merkleize_pow2 + 128)),
    .ADDI .x18 .x18 (64 : BitVec 12),
    .ADDI .x19 .x19 (32 : BitVec 12),
    .ADDI .x9 .x9 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .SRLI .x8 .x8 (1 : BitVec 6),
    .JAL .x0 (-60 : BitVec 21),
    .LD .x5 .x21 (0 : BitVec 12),
    .SD .x22 .x5 (0 : BitVec 12),
    .LD .x5 .x21 (8 : BitVec 12),
    .SD .x22 .x5 (8 : BitVec 12),
    .LD .x5 .x21 (16 : BitVec 12),
    .SD .x22 .x5 (16 : BitVec 12),
    .LD .x5 .x21 (24 : BitVec 12),
    .SD .x22 .x5 (24 : BitVec 12),
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

/-- Reloc side-table for `sszMerkleizePow2_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def sszMerkleizePow2_relocs : RelocTable :=
  [ (11, .la .x21 "ssz_merkleize_scratch"),
    (32, .jal .x1 "zkvm_sha256") ]

def sszMerkleizePow2Function : String :=
  "ssz_merkleize_pow2:\n" ++ emitProgramR sszMerkleizePow2_prog sszMerkleizePow2_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `sszMerkleizePow2_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem sszMerkleizePow2Function_eq_prog :
    sszMerkleizePow2Function = "ssz_merkleize_pow2:\n" ++ emitProgramR sszMerkleizePow2_prog sszMerkleizePow2_relocs := rfl

#guard sszMerkleizePow2Function.startsWith "ssz_merkleize_pow2:\n"
#guard sszMerkleizePow2_prog.length = 58

/-! ## ssz_merkleize — PR-S7 arbitrary-length SSZ merkleization

    Lifts `ssz_merkleize_pow2` (PR-S6) to the general SSZ case
    by zero-padding short inputs out to a power of two, then
    further padding the resulting root up to the SSZ capacity by
    pair-hashing with `Z_d` from the PR-S5 table at each missing
    depth.

    Two phases:
      1. Pad chunks up to `M = next_pow2(n)` with `Z_0`. Reduce
         in place via `ssz_merkleize_pow2`. Result: partial root
         at depth `d_M = log2(M)`.
      2. For `d` from `d_M` to `limit_log2 - 1`:
             partial_root = sha256_pair(partial_root, Z_d)

    Edge case `n = 0`: result is `Z_{limit_log2}` straight from
    the zero-hashes table; phase 1 is skipped.

    Calling convention:
      a0 (input)  : ptr to `n * 32` chunk bytes
      a1 (input)  : n (0 ≤ n ≤ 32)
      a2 (input)  : limit_log2 L (0 ≤ L ≤ 31; capacity = 2^L)
      a3 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (ZKVM_EOK)

    Clobbers t0..t6, a0..a3. Saves/restores s0..s6 and ra via
    a 64-byte stack frame. -/
def sszMerkleize_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x21 .x10,
    .MV .x8 .x11,
    .MV .x9 .x12,
    .MV .x22 .x13,
    .BEQ .x8 .x0 (272 : BitVec 13),
    .LI .x5 (1 : Word),
    .LI .x20 (0 : Word),
    .BGE .x5 .x8 (16 : BitVec 13),
    .SLLI .x5 .x5 (1 : BitVec 6),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-12 : BitVec 21),
    .MV .x19 .x5,
    .AUIPC .x5 (laHi GuestAddrs.ssz_merkleize_padded (GuestAddrs.ssz_merkleize + 84)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssz_merkleize_padded (GuestAddrs.ssz_merkleize + 84)),
    .SLLI .x6 .x8 (5 : BitVec 6),
    .MV .x7 .x21,
    .MV .x28 .x5,
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LD .x29 .x7 (0 : BitVec 12),
    .SD .x28 .x29 (0 : BitVec 12),
    .ADDI .x7 .x7 (8 : BitVec 12),
    .ADDI .x28 .x28 (8 : BitVec 12),
    .ADDI .x6 .x6 (-8 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .SUB .x6 .x19 .x8,
    .SLLI .x6 .x6 (5 : BitVec 6),
    .BEQ .x6 .x0 (20 : BitVec 13),
    .SD .x28 .x0 (0 : BitVec 12),
    .ADDI .x28 .x28 (8 : BitVec 12),
    .ADDI .x6 .x6 (-8 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.ssz_merkleize_padded (GuestAddrs.ssz_merkleize + 160)),
    .ADDI .x10 .x10 (laLo GuestAddrs.ssz_merkleize_padded (GuestAddrs.ssz_merkleize + 160)),
    .MV .x11 .x19,
    .AUIPC .x12 (laHi GuestAddrs.ssz_merkleize_partial (GuestAddrs.ssz_merkleize + 172)),
    .ADDI .x12 .x12 (laLo GuestAddrs.ssz_merkleize_partial (GuestAddrs.ssz_merkleize + 172)),
    .JAL .x1 (jalOff GuestAddrs.ssz_merkleize_pow2 (GuestAddrs.ssz_merkleize + 180)),
    .BEQ .x20 .x9 (96 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.ssz_zero_hashes (GuestAddrs.ssz_merkleize + 188)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssz_zero_hashes (GuestAddrs.ssz_merkleize + 188)),
    .SLLI .x6 .x20 (5 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .AUIPC .x7 (laHi GuestAddrs.ssz_merkleize_partial (GuestAddrs.ssz_merkleize + 204)),
    .ADDI .x7 .x7 (laLo GuestAddrs.ssz_merkleize_partial (GuestAddrs.ssz_merkleize + 204)),
    .ADDI .x7 .x7 (32 : BitVec 12),
    .LD .x28 .x5 (0 : BitVec 12),
    .SD .x7 .x28 (0 : BitVec 12),
    .LD .x28 .x5 (8 : BitVec 12),
    .SD .x7 .x28 (8 : BitVec 12),
    .LD .x28 .x5 (16 : BitVec 12),
    .SD .x7 .x28 (16 : BitVec 12),
    .LD .x28 .x5 (24 : BitVec 12),
    .SD .x7 .x28 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.ssz_merkleize_partial (GuestAddrs.ssz_merkleize + 248)),
    .ADDI .x10 .x10 (laLo GuestAddrs.ssz_merkleize_partial (GuestAddrs.ssz_merkleize + 248)),
    .LI .x11 (64 : Word),
    .AUIPC .x12 (laHi GuestAddrs.ssz_merkleize_partial (GuestAddrs.ssz_merkleize + 260)),
    .ADDI .x12 .x12 (laLo GuestAddrs.ssz_merkleize_partial (GuestAddrs.ssz_merkleize + 260)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.ssz_merkleize + 268)),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-92 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.ssz_merkleize_partial (GuestAddrs.ssz_merkleize + 280)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssz_merkleize_partial (GuestAddrs.ssz_merkleize + 280)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x22 .x6 (0 : BitVec 12),
    .LD .x6 .x5 (8 : BitVec 12),
    .SD .x22 .x6 (8 : BitVec 12),
    .LD .x6 .x5 (16 : BitVec 12),
    .SD .x22 .x6 (16 : BitVec 12),
    .LD .x6 .x5 (24 : BitVec 12),
    .SD .x22 .x6 (24 : BitVec 12),
    .JAL .x0 (52 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.ssz_zero_hashes (GuestAddrs.ssz_merkleize + 324)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssz_zero_hashes (GuestAddrs.ssz_merkleize + 324)),
    .SLLI .x6 .x9 (5 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x22 .x6 (0 : BitVec 12),
    .LD .x6 .x5 (8 : BitVec 12),
    .SD .x22 .x6 (8 : BitVec 12),
    .LD .x6 .x5 (16 : BitVec 12),
    .SD .x22 .x6 (16 : BitVec 12),
    .LD .x6 .x5 (24 : BitVec 12),
    .SD .x22 .x6 (24 : BitVec 12),
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

/-- Reloc side-table for `sszMerkleize_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def sszMerkleize_relocs : RelocTable :=
  [ (21, .la .x5 "ssz_merkleize_padded"),
    (40, .la .x10 "ssz_merkleize_padded"),
    (43, .la .x12 "ssz_merkleize_partial"),
    (45, .jal .x1 "ssz_merkleize_pow2"),
    (47, .la .x5 "ssz_zero_hashes"),
    (51, .la .x7 "ssz_merkleize_partial"),
    (62, .la .x10 "ssz_merkleize_partial"),
    (65, .la .x12 "ssz_merkleize_partial"),
    (67, .jal .x1 "zkvm_sha256"),
    (70, .la .x5 "ssz_merkleize_partial"),
    (81, .la .x5 "ssz_zero_hashes") ]

def sszMerkleizeFunction : String :=
  "ssz_merkleize:\n" ++ emitProgramR sszMerkleize_prog sszMerkleize_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `sszMerkleize_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem sszMerkleizeFunction_eq_prog :
    sszMerkleizeFunction = "ssz_merkleize:\n" ++ emitProgramR sszMerkleize_prog sszMerkleize_relocs := rfl

#guard sszMerkleizeFunction.startsWith "ssz_merkleize:\n"
#guard sszMerkleize_prog.length = 104

/-! ## ssz_pack_bytes — PR-S8 SSZ byte chunker

    Packs an arbitrary byte string into 32-byte chunks for
    consumption by `ssz_merkleize`. The byte stream is copied
    verbatim; the final chunk is right-zero-padded if the byte
    count is not a multiple of 32. Returns the chunk count.

    Calling convention:
      a0 (input)  : src ptr
      a1 (input)  : byte length L (0 ≤ L ≤ 1024)
      a2 (input)  : dst chunk buffer ptr (32 * ceil(L/32) bytes)
      ra (input)  : return
      a0 (output) : chunk count = ceil(L / 32)
      bytes at *a2: source bytes followed by zero-padding

    Byte-at-a-time copy (slow path, ~L instructions). Acceptable
    for bring-up; a future PR can specialise to 8-byte units
    when alignment is known. -/
def sszPackBytes_prog : Program :=
  [ .MV .x5 .x10,
    .MV .x6 .x12,
    .MV .x7 .x11,
    .BEQ .x7 .x0 (28 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ANDI .x7 .x11 (31 : BitVec 12),
    .BEQ .x7 .x0 (32 : BitVec 13),
    .LI .x28 (32 : Word),
    .SUB .x7 .x28 .x7,
    .BEQ .x7 .x0 (20 : BitVec 13),
    .SB .x6 .x0 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .ADDI .x5 .x11 (31 : BitVec 12),
    .SRLI .x10 .x5 (5 : BitVec 6),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def sszPackBytesFunction : String :=
  "ssz_pack_bytes:\n" ++ emitProgram sszPackBytes_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `sszPackBytes_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem sszPackBytesFunction_eq_prog :
    sszPackBytesFunction = "ssz_pack_bytes:\n" ++ emitProgram sszPackBytes_prog := rfl

#guard sszPackBytesFunction.startsWith "ssz_pack_bytes:\n"
#guard sszPackBytes_prog.length = 22

/-! ## ssz_hash_tree_root_bytes — PR-S9 SSZ hash_tree_root(Bytes)

    Composes PR-S8 `ssz_pack_bytes`, PR-S7 `ssz_merkleize`, and
    PR-S2 `zkvm_sha256` into a single named entry point:

        chunks       = pack(value)
        partial_root = merkleize(chunks, limit_log2_chunks)
        root         = sha256(partial_root || u256_le(len))

    Matches the SSZ spec for variable-length `Bytes` with
    declared capacity `B_max = 32 * 2^limit_log2_chunks` bytes.

    Calling convention:
      a0 (input)  : src bytes ptr
      a1 (input)  : L (bounded by the linked `ssz_hb_chunks` scratch)
      a2 (input)  : limit_log2_chunks (0 ≤ L_log2 ≤ 31)
      a3 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (ZKVM_EOK)

    Uses three scratches in `.data`:
      ssz_hb_chunks           -- packed chunks before merkleize
      ssz_hb_partial (32 B)   -- partial root from merkleize
      ssz_hb_mix     (64 B)   -- (partial || length) buffer
                                 for the final sha256 -/
def sszHashTreeRootBytes_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.ssz_hb_chunks (GuestAddrs.ssz_hash_tree_root_bytes + 52)),
    .ADDI .x12 .x12 (laLo GuestAddrs.ssz_hb_chunks (GuestAddrs.ssz_hash_tree_root_bytes + 52)),
    .JAL .x1 (jalOff GuestAddrs.ssz_pack_bytes (GuestAddrs.ssz_hash_tree_root_bytes + 60)),
    .MV .x20 .x10,
    .AUIPC .x10 (laHi GuestAddrs.ssz_hb_chunks (GuestAddrs.ssz_hash_tree_root_bytes + 68)),
    .ADDI .x10 .x10 (laLo GuestAddrs.ssz_hb_chunks (GuestAddrs.ssz_hash_tree_root_bytes + 68)),
    .MV .x11 .x20,
    .MV .x12 .x18,
    .AUIPC .x13 (laHi GuestAddrs.ssz_hb_partial (GuestAddrs.ssz_hash_tree_root_bytes + 84)),
    .ADDI .x13 .x13 (laLo GuestAddrs.ssz_hb_partial (GuestAddrs.ssz_hash_tree_root_bytes + 84)),
    .JAL .x1 (jalOff GuestAddrs.ssz_merkleize (GuestAddrs.ssz_hash_tree_root_bytes + 92)),
    .AUIPC .x5 (laHi GuestAddrs.ssz_hb_partial (GuestAddrs.ssz_hash_tree_root_bytes + 96)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssz_hb_partial (GuestAddrs.ssz_hash_tree_root_bytes + 96)),
    .AUIPC .x6 (laHi GuestAddrs.ssz_hb_mix (GuestAddrs.ssz_hash_tree_root_bytes + 104)),
    .ADDI .x6 .x6 (laLo GuestAddrs.ssz_hb_mix (GuestAddrs.ssz_hash_tree_root_bytes + 104)),
    .LD .x7 .x5 (0 : BitVec 12),
    .SD .x6 .x7 (0 : BitVec 12),
    .LD .x7 .x5 (8 : BitVec 12),
    .SD .x6 .x7 (8 : BitVec 12),
    .LD .x7 .x5 (16 : BitVec 12),
    .SD .x6 .x7 (16 : BitVec 12),
    .LD .x7 .x5 (24 : BitVec 12),
    .SD .x6 .x7 (24 : BitVec 12),
    .SD .x6 .x9 (32 : BitVec 12),
    .SD .x6 .x0 (40 : BitVec 12),
    .SD .x6 .x0 (48 : BitVec 12),
    .SD .x6 .x0 (56 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.ssz_hb_mix (GuestAddrs.ssz_hash_tree_root_bytes + 160)),
    .ADDI .x10 .x10 (laLo GuestAddrs.ssz_hb_mix (GuestAddrs.ssz_hash_tree_root_bytes + 160)),
    .LI .x11 (64 : Word),
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.ssz_hash_tree_root_bytes + 176)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `sszHashTreeRootBytes_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def sszHashTreeRootBytes_relocs : RelocTable :=
  [ (13, .la .x12 "ssz_hb_chunks"),
    (15, .jal .x1 "ssz_pack_bytes"),
    (17, .la .x10 "ssz_hb_chunks"),
    (21, .la .x13 "ssz_hb_partial"),
    (23, .jal .x1 "ssz_merkleize"),
    (24, .la .x5 "ssz_hb_partial"),
    (26, .la .x6 "ssz_hb_mix"),
    (40, .la .x10 "ssz_hb_mix"),
    (44, .jal .x1 "zkvm_sha256") ]

def sszHashTreeRootBytesFunction : String :=
  "ssz_hash_tree_root_bytes:\n" ++ emitProgramR sszHashTreeRootBytes_prog sszHashTreeRootBytes_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `sszHashTreeRootBytes_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem sszHashTreeRootBytesFunction_eq_prog :
    sszHashTreeRootBytesFunction = "ssz_hash_tree_root_bytes:\n" ++ emitProgramR sszHashTreeRootBytes_prog sszHashTreeRootBytes_relocs := rfl

#guard sszHashTreeRootBytesFunction.startsWith "ssz_hash_tree_root_bytes:\n"
#guard sszHashTreeRootBytes_prog.length = 54

/-! ## ssz_hash_tree_root_list_bytelist — PR-S11

    SSZ hash_tree_root for `List[ByteList[B], M]`.

    Reads the SSZ-encoded list section directly (inner-offset
    table at the start, concatenated element bytes after).
    Iterates over elements, recursively SSZ-hashes each as a
    `ByteList[B]` via `ssz_hash_tree_root_bytes`, merkleizes the
    resulting child roots with capacity `2^count_log2`, then
    mixes in the element count.

    Calling convention:
      a0 (input)  : section ptr (read-only)
      a1 (input)  : section_len (0 = empty list)
      a2 (input)  : per-element byte_limit_log2_chunks
      a3 (input)  : list count_limit_log2 (capacity = 2^a3)
      a4 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (ZKVM_EOK), 1 if the section exceeds this helper's
                    scratch-supported bounds

    PR-S11 caps N (element count) at 4096, matching the enlarged stateless
    scratch, and each ByteList element at 2 MiB, matching the current
    `ssz_hash_tree_root_bytes` stateless scratch. Output is byte-identical to
    `SszList[ByteList[B], M](...).hash_tree_root()` from
    `remerkleable` for any input within those helper bounds. -/
def sszHashTreeRootListBytelist_prog : Program :=
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
    .BEQ .x9 .x0 (396 : BitVec 13),
    .LBU .x5 .x8 (0 : BitVec 12),
    .LBU .x30 .x8 (1 : BitVec 12),
    .SLLI .x30 .x30 (8 : BitVec 6),
    .OR .x5 .x5 .x30,
    .LBU .x30 .x8 (2 : BitVec 12),
    .SLLI .x30 .x30 (16 : BitVec 6),
    .OR .x5 .x5 .x30,
    .LBU .x30 .x8 (3 : BitVec 12),
    .SLLI .x30 .x30 (24 : BitVec 6),
    .OR .x5 .x5 .x30,
    .ANDI .x30 .x5 (3 : BitVec 12),
    .BNE .x30 .x0 (448 : BitVec 13),
    .SRLI .x21 .x5 (2 : BitVec 6),
    .BEQ .x21 .x0 (440 : BitVec 13),
    .LUI .x30 (1 : BitVec 20),
    .BLTU .x30 .x21 (432 : BitVec 13),
    .BLTU .x9 .x5 (428 : BitVec 13),
    .LI .x22 (0 : Word),
    .BEQ .x22 .x21 (204 : BitVec 13),
    .SLLI .x5 .x22 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LBU .x7 .x6 (0 : BitVec 12),
    .LBU .x30 .x6 (1 : BitVec 12),
    .SLLI .x30 .x30 (8 : BitVec 6),
    .OR .x7 .x7 .x30,
    .LBU .x30 .x6 (2 : BitVec 12),
    .SLLI .x30 .x30 (16 : BitVec 6),
    .OR .x7 .x7 .x30,
    .LBU .x30 .x6 (3 : BitVec 12),
    .SLLI .x30 .x30 (24 : BitVec 6),
    .OR .x7 .x7 .x30,
    .SLLI .x28 .x21 (2 : BitVec 6),
    .BLTU .x7 .x28 (364 : BitVec 13),
    .BLTU .x9 .x7 (360 : BitVec 13),
    .ADD .x10 .x8 .x7,
    .ADDI .x28 .x22 (1 : BitVec 12),
    .BEQ .x28 .x21 (68 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LBU .x29 .x28 (0 : BitVec 12),
    .LBU .x30 .x28 (1 : BitVec 12),
    .SLLI .x30 .x30 (8 : BitVec 6),
    .OR .x29 .x29 .x30,
    .LBU .x30 .x28 (2 : BitVec 12),
    .SLLI .x30 .x30 (16 : BitVec 6),
    .OR .x29 .x29 .x30,
    .LBU .x30 .x28 (3 : BitVec 12),
    .SLLI .x30 .x30 (24 : BitVec 6),
    .OR .x29 .x29 .x30,
    .BLTU .x29 .x7 (296 : BitVec 13),
    .BLTU .x9 .x29 (292 : BitVec 13),
    .ADD .x29 .x8 .x29,
    .JAL .x0 (8 : BitVec 21),
    .ADD .x29 .x8 .x9,
    .SUB .x11 .x29 .x10,
    .LI .x6 (32 : Word),
    .SLL .x6 .x6 .x18,
    .BLTU .x6 .x11 (264 : BitVec 13),
    .LUI .x5 (512 : BitVec 20),
    .BLTU .x5 .x11 (256 : BitVec 13),
    .MV .x12 .x18,
    .AUIPC .x13 (laHi GuestAddrs.ssz_ltb_child_roots (GuestAddrs.ssz_hash_tree_root_list_bytelist + 304)),
    .ADDI .x13 .x13 (laLo GuestAddrs.ssz_ltb_child_roots (GuestAddrs.ssz_hash_tree_root_list_bytelist + 304)),
    .SLLI .x5 .x22 (5 : BitVec 6),
    .ADD .x13 .x13 .x5,
    .JAL .x1 (jalOff GuestAddrs.ssz_hash_tree_root_bytes (GuestAddrs.ssz_hash_tree_root_list_bytelist + 320)),
    .BNE .x10 .x0 (228 : BitVec 13),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (-200 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.ssz_ltb_child_roots (GuestAddrs.ssz_hash_tree_root_list_bytelist + 336)),
    .ADDI .x10 .x10 (laLo GuestAddrs.ssz_ltb_child_roots (GuestAddrs.ssz_hash_tree_root_list_bytelist + 336)),
    .MV .x11 .x21,
    .MV .x12 .x19,
    .AUIPC .x13 (laHi GuestAddrs.ssz_ltb_partial (GuestAddrs.ssz_hash_tree_root_list_bytelist + 352)),
    .ADDI .x13 .x13 (laLo GuestAddrs.ssz_ltb_partial (GuestAddrs.ssz_hash_tree_root_list_bytelist + 352)),
    .JAL .x1 (jalOff GuestAddrs.ssz_merkleize (GuestAddrs.ssz_hash_tree_root_list_bytelist + 360)),
    .AUIPC .x5 (laHi GuestAddrs.ssz_ltb_partial (GuestAddrs.ssz_hash_tree_root_list_bytelist + 364)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssz_ltb_partial (GuestAddrs.ssz_hash_tree_root_list_bytelist + 364)),
    .AUIPC .x6 (laHi GuestAddrs.ssz_ltb_mix (GuestAddrs.ssz_hash_tree_root_list_bytelist + 372)),
    .ADDI .x6 .x6 (laLo GuestAddrs.ssz_ltb_mix (GuestAddrs.ssz_hash_tree_root_list_bytelist + 372)),
    .LD .x7 .x5 (0 : BitVec 12),
    .SD .x6 .x7 (0 : BitVec 12),
    .LD .x7 .x5 (8 : BitVec 12),
    .SD .x6 .x7 (8 : BitVec 12),
    .LD .x7 .x5 (16 : BitVec 12),
    .SD .x6 .x7 (16 : BitVec 12),
    .LD .x7 .x5 (24 : BitVec 12),
    .SD .x6 .x7 (24 : BitVec 12),
    .SD .x6 .x21 (32 : BitVec 12),
    .SD .x6 .x0 (40 : BitVec 12),
    .SD .x6 .x0 (48 : BitVec 12),
    .SD .x6 .x0 (56 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.ssz_ltb_mix (GuestAddrs.ssz_hash_tree_root_list_bytelist + 428)),
    .ADDI .x10 .x10 (laLo GuestAddrs.ssz_ltb_mix (GuestAddrs.ssz_hash_tree_root_list_bytelist + 428)),
    .LI .x11 (64 : Word),
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.ssz_hash_tree_root_list_bytelist + 444)),
    .JAL .x0 (96 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.ssz_zero_hashes (GuestAddrs.ssz_hash_tree_root_list_bytelist + 452)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssz_zero_hashes (GuestAddrs.ssz_hash_tree_root_list_bytelist + 452)),
    .SLLI .x6 .x19 (5 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .AUIPC .x6 (laHi GuestAddrs.ssz_ltb_mix (GuestAddrs.ssz_hash_tree_root_list_bytelist + 468)),
    .ADDI .x6 .x6 (laLo GuestAddrs.ssz_ltb_mix (GuestAddrs.ssz_hash_tree_root_list_bytelist + 468)),
    .LD .x7 .x5 (0 : BitVec 12),
    .SD .x6 .x7 (0 : BitVec 12),
    .LD .x7 .x5 (8 : BitVec 12),
    .SD .x6 .x7 (8 : BitVec 12),
    .LD .x7 .x5 (16 : BitVec 12),
    .SD .x6 .x7 (16 : BitVec 12),
    .LD .x7 .x5 (24 : BitVec 12),
    .SD .x6 .x7 (24 : BitVec 12),
    .SD .x6 .x0 (32 : BitVec 12),
    .SD .x6 .x0 (40 : BitVec 12),
    .SD .x6 .x0 (48 : BitVec 12),
    .SD .x6 .x0 (56 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.ssz_ltb_mix (GuestAddrs.ssz_hash_tree_root_list_bytelist + 524)),
    .ADDI .x10 .x10 (laLo GuestAddrs.ssz_ltb_mix (GuestAddrs.ssz_hash_tree_root_list_bytelist + 524)),
    .LI .x11 (64 : Word),
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.ssz_hash_tree_root_list_bytelist + 540)),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .SD .x20 .x0 (0 : BitVec 12),
    .SD .x20 .x0 (8 : BitVec 12),
    .SD .x20 .x0 (16 : BitVec 12),
    .SD .x20 .x0 (24 : BitVec 12),
    .LI .x10 (1 : Word),
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

/-- Reloc side-table for `sszHashTreeRootListBytelist_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def sszHashTreeRootListBytelist_relocs : RelocTable :=
  [ (76, .la .x13 "ssz_ltb_child_roots"),
    (80, .jal .x1 "ssz_hash_tree_root_bytes"),
    (84, .la .x10 "ssz_ltb_child_roots"),
    (88, .la .x13 "ssz_ltb_partial"),
    (90, .jal .x1 "ssz_merkleize"),
    (91, .la .x5 "ssz_ltb_partial"),
    (93, .la .x6 "ssz_ltb_mix"),
    (107, .la .x10 "ssz_ltb_mix"),
    (111, .jal .x1 "zkvm_sha256"),
    (113, .la .x5 "ssz_zero_hashes"),
    (117, .la .x6 "ssz_ltb_mix"),
    (131, .la .x10 "ssz_ltb_mix"),
    (135, .jal .x1 "zkvm_sha256") ]

def sszHashTreeRootListByteListFunction : String :=
  "ssz_hash_tree_root_list_bytelist:\n" ++ emitProgramR sszHashTreeRootListBytelist_prog sszHashTreeRootListBytelist_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `sszHashTreeRootListBytelist_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem sszHashTreeRootListByteListFunction_eq_prog :
    sszHashTreeRootListByteListFunction = "ssz_hash_tree_root_list_bytelist:\n" ++ emitProgramR sszHashTreeRootListBytelist_prog sszHashTreeRootListBytelist_relocs := rfl

#guard sszHashTreeRootListByteListFunction.startsWith "ssz_hash_tree_root_list_bytelist:\n"
#guard sszHashTreeRootListBytelist_prog.length = 153

/-! ## ssz_hash_tree_root_execution_witness — PR-S12

    SSZ Container hash for the amsterdam `ExecutionWitness`.
    Three variable-size fields (state, codes, headers); each
    field is itself a `List[ByteList[B_i], M_i]` and gets
    hashed via `ssz_hash_tree_root_list_bytelist` (PR-S11). The
    three resulting child roots are merkleized with capacity 4
    slots (`limit_log2 = ceil(log2(3)) = 2`) to produce the
    Container root.

    Per the SSZ spec for Containers, NO mix_in_length step
    follows -- only variable-length List/Bytes types mix in
    length.

    Calling convention:
      a0 (input)  : section ptr (SSZ-encoded ExecutionWitness)
      a1 (input)  : section_len
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (ZKVM_EOK), nonzero if a nested list exceeds helper bounds

    Per-field caps inherited from PR-S11: each list's N ≤ 32.
    Test fixtures stay well below; production-sized witnesses
    are a follow-up. -/
/-! Probe-only local PC placeholder. -/
def sszHashTreeRootExecutionWitnessPc : Nat := 0x80000000

def sszHashTreeRootExecutionWitness_prog : Program :=
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
    .LWU .x19 .x8 (0 : BitVec 12),
    .LWU .x20 .x8 (4 : BitVec 12),
    .LWU .x21 .x8 (8 : BitVec 12),
    .ADD .x22 .x8 .x9,
    .ADD .x10 .x8 .x19,
    .ADD .x5 .x8 .x20,
    .SUB .x11 .x5 .x10,
    .LI .x12 (5 : Word),
    .LI .x13 (22 : Word),
    .AUIPC .x14 (laHi 0 (sszHashTreeRootExecutionWitnessPc + 84)),
    .ADDI .x14 .x14 (laLo 0 (sszHashTreeRootExecutionWitnessPc + 84)),
    .JAL .x1 (jalOff GuestAddrs.ssz_hash_tree_root_list_bytelist (sszHashTreeRootExecutionWitnessPc + 92)),
    .BNE .x10 .x0 (brOff (sszHashTreeRootExecutionWitnessPc + 204) (sszHashTreeRootExecutionWitnessPc + 96)),
    .ADD .x10 .x8 .x20,
    .ADD .x5 .x8 .x21,
    .SUB .x11 .x5 .x10,
    .LI .x12 (11 : Word),
    .LI .x13 (18 : Word),
    .AUIPC .x14 (laHi 0 (sszHashTreeRootExecutionWitnessPc + 120)),
    .ADDI .x14 .x14 (laLo 0 (sszHashTreeRootExecutionWitnessPc + 120)),
    .ADDI .x14 .x14 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.ssz_hash_tree_root_list_bytelist (sszHashTreeRootExecutionWitnessPc + 132)),
    .BNE .x10 .x0 (brOff (sszHashTreeRootExecutionWitnessPc + 204) (sszHashTreeRootExecutionWitnessPc + 136)),
    .ADD .x10 .x8 .x21,
    .SUB .x11 .x22 .x10,
    .LI .x12 (5 : Word),
    .LI .x13 (8 : Word),
    .AUIPC .x14 (laHi 0 (sszHashTreeRootExecutionWitnessPc + 156)),
    .ADDI .x14 .x14 (laLo 0 (sszHashTreeRootExecutionWitnessPc + 156)),
    .ADDI .x14 .x14 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.ssz_hash_tree_root_list_bytelist (sszHashTreeRootExecutionWitnessPc + 168)),
    .BNE .x10 .x0 (32 : BitVec 13),
    .AUIPC .x10 (laHi 0 (sszHashTreeRootExecutionWitnessPc + 176)),
    .ADDI .x10 .x10 (laLo 0 (sszHashTreeRootExecutionWitnessPc + 176)),
    .LI .x11 (3 : Word),
    .LI .x12 (2 : Word),
    .MV .x13 .x18,
    .JAL .x1 (jalOff GuestAddrs.ssz_merkleize (sszHashTreeRootExecutionWitnessPc + 196)),
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

/-- Reloc side-table for `sszHashTreeRootExecutionWitness_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def sszHashTreeRootExecutionWitness_relocs : RelocTable :=
  [ (21, .la .x14 "ssz_ew_field_roots"),
    (23, .jal .x1 "ssz_hash_tree_root_list_bytelist"),
    (30, .la .x14 "ssz_ew_field_roots"),
    (33, .jal .x1 "ssz_hash_tree_root_list_bytelist"),
    (39, .la .x14 "ssz_ew_field_roots"),
    (42, .jal .x1 "ssz_hash_tree_root_list_bytelist"),
    (44, .la .x10 "ssz_ew_field_roots"),
    (49, .jal .x1 "ssz_merkleize") ]

def sszHashTreeRootExecutionWitnessFunction : String :=
  "ssz_hash_tree_root_execution_witness:\n" ++ emitProgramR sszHashTreeRootExecutionWitness_prog sszHashTreeRootExecutionWitness_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `sszHashTreeRootExecutionWitness_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem sszHashTreeRootExecutionWitnessFunction_eq_prog :
    sszHashTreeRootExecutionWitnessFunction = "ssz_hash_tree_root_execution_witness:\n" ++ emitProgramR sszHashTreeRootExecutionWitness_prog sszHashTreeRootExecutionWitness_relocs := rfl

#guard sszHashTreeRootExecutionWitnessFunction.startsWith "ssz_hash_tree_root_execution_witness:\n"
#guard sszHashTreeRootExecutionWitness_prog.length = 61

end EvmAsm.Codegen
