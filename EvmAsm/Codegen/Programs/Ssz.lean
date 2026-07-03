/-
  EvmAsm.Codegen.Programs.Ssz

  SSZ merkleization probes (`zisk_ssz_*`): hash-tree-root building
  blocks that exercise the merkleization shims in
  `EvmAsm.Stateless.SSZ.HashTreeRoot.Program` end-to-end on ziskemu.

  Extracted from `EvmAsm.Codegen.Programs` so the registry hub stays
  manageable.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Stateless.SSZ.HashTreeRoot.Program
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## zisk_ssz_pair_hash — PR-S4 SSZ merkleization primitive

    First consumer of the SSZ `hash_tree_root` shim:
    `sha256_pair(L, R) = sha256(L ‖ R)`.

    The shim lives at `Stateless/SSZ/HashTreeRoot/Program.lean`
    (`sszPairHashCallAsm`); this BuildUnit is the executable that
    exercises it end-to-end on ziskemu. The driver reads two
    32-byte values from the host-supplied input region (laid out
    contiguously at INPUT_ADDR + 16..80 so they're already in
    L ‖ R order), passes the buffer base in `a0` and the OUTPUT
    pointer in `a2`, and lets the shim hand off to the PR-S2
    `zkvm_sha256` wrapper.

    ### Fixture (32-byte SSZ "zero leaf" pair)

      L = 0x00..00 (32 bytes)
      R = 0x00..00 (32 bytes)

    Expected (this is `Z_1` in the SSZ zero-hashes sequence):

      sha256(0x00 * 64) =
        f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b

    The test script feeds those 64 zero bytes via `ziskemu -i` and
    diffs the 32-byte digest at OUTPUT_ADDR against Python's
    `hashlib.sha256(b"\\x00" * 64).digest()`.

    ### Why this isn't redundant with the PR-S2 in-data fixture

    PR-S2 tested `zkvm_sha256` on `.data`-resident constants;
    PR-S3 tested it on host-supplied input. PR-S4 additionally
    pins the `ssz_pair_hash` *symbol* -- the named entry point
    that higher SSZ machinery (PR-S5+ merkleize, mix_in_length)
    will call. Once that symbol exists, the merkleize loop is a
    straightforward "load chunk, call `ssz_pair_hash`, store
    result" iteration; no further sha256 layout decisions.
-/
def ziskSszPairHashPrologue : String :=
  "  # set up stack\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # point at the 64-byte L||R buffer in host input region\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  addi a0, a3, 16             # a0 = L||R ptr (INPUT_ADDR + 16)\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  EvmAsm.Stateless.SSZ.HashTreeRoot.sszPairHashCallAsm ++ "\n" ++
  "  j .Lzs4_done\n" ++
  zkvmSha256Function ++ "\n" ++
  ".Lzs4_done:"

/-- `.data` for the SSZ pair-hash probe: same scratch buffers
    used by `zkvm_sha256` (IV, state, input block, params). The
    L‖R bytes come from host input, not from `.data`. -/
def ziskSszPairHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667    # LE(h0) || LE(h1)\n" ++
  "  .quad 0xa54ff53a3c6ef372    # LE(h2) || LE(h3)\n" ++
  "  .quad 0x9b05688c510e527f    # LE(h4) || LE(h5)\n" ++
  "  .quad 0x5be0cd191f83d9ab    # LE(h6) || LE(h7)\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input"

def ziskSszPairHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszPairHashPrologue
  dataAsm     := ziskSszPairHashDataSection
}

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

    `z[1]` matches the PR-S4 fixture (`f5a5fd42..fb4b`), and the
    full table is regression-checked by the
    `zisk_ssz_zero_hashes` probe BuildUnit below: it accepts a
    depth `i` via host input, looks up Z_i, and writes 32 bytes
    to OUTPUT. The check script iterates i = 0..31 and diffs
    each Z_i against Python's recomputation.
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

/-- `zisk_ssz_zero_hashes`: probe BuildUnit that reads a u64
    depth index from `INPUT_ADDR + 8` (LE; first 8 bytes of the
    ziskemu input file) and writes the 32 bytes of `Z_i` to
    `OUTPUT_ADDR`. -/
def ziskSszZeroHashesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a0, 8(a3)                # a0 = depth index i (u64 LE)\n" ++
  "  slli a0, a0, 5              # a0 = i * 32 (byte offset)\n" ++
  "  la a1, ssz_zero_hashes\n" ++
  "  add a1, a1, a0              # a1 = &Z_i\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  ld t0, 0(a1);  sd t0, 0(a2)\n" ++
  "  ld t0, 8(a1);  sd t0, 8(a2)\n" ++
  "  ld t0, 16(a1); sd t0, 16(a2)\n" ++
  "  ld t0, 24(a1); sd t0, 24(a2)"

def ziskSszZeroHashesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszZeroHashesPrologue
  dataAsm     := sszZeroHashesDataSection
}

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
def sszMerkleizePow2Function : String :=
  "ssz_merkleize_pow2:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp)\n" ++
  "  sd s6, 56(sp)\n" ++
  "  # s0 = n (current chunk count); s5 = scratch base; s6 = caller out ptr\n" ++
  "  mv s0, a1\n" ++
  "  mv s6, a2\n" ++
  "  la s5, ssz_merkleize_scratch\n" ++
  "  # copy n*32 input bytes into scratch (in 8-byte units)\n" ++
  "  mv t0, a0\n" ++
  "  mv t1, s5\n" ++
  "  slli t2, s0, 5             # t2 = n * 32 bytes to copy\n" ++
  ".Lmrk_copy:\n" ++
  "  beqz t2, .Lmrk_iter\n" ++
  "  ld t3, 0(t0)\n" ++
  "  sd t3, 0(t1)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, -8\n" ++
  "  j .Lmrk_copy\n" ++
  ".Lmrk_iter:\n" ++
  "  # if n == 1: root is at scratch[0..32]\n" ++
  "  li t0, 1\n" ++
  "  beq s0, t0, .Lmrk_done\n" ++
  "  # pair-hash adjacent chunks into the lower half of scratch\n" ++
  "  srli s1, s0, 1             # s1 = n/2 = pair count\n" ++
  "  mv s2, s5                  # s2 = src pair ptr (64-byte step)\n" ++
  "  mv s3, s5                  # s3 = dst slot ptr (32-byte step)\n" ++
  ".Lmrk_pair:\n" ++
  "  beqz s1, .Lmrk_advance\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  li a1, 64\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  addi s2, s2, 64\n" ++
  "  addi s3, s3, 32\n" ++
  "  addi s1, s1, -1\n" ++
  "  j .Lmrk_pair\n" ++
  ".Lmrk_advance:\n" ++
  "  srli s0, s0, 1             # n /= 2\n" ++
  "  j .Lmrk_iter\n" ++
  ".Lmrk_done:\n" ++
  "  # copy 32 bytes scratch[0..32] -> caller out ptr (s6)\n" ++
  "  ld t0,  0(s5);  sd t0,  0(s6)\n" ++
  "  ld t0,  8(s5);  sd t0,  8(s6)\n" ++
  "  ld t0, 16(s5);  sd t0, 16(s6)\n" ++
  "  ld t0, 24(s5);  sd t0, 24(s6)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp)\n" ++
  "  ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_ssz_merkleize_pow2`: probe BuildUnit that reads `n`
    from `INPUT_ADDR + 8` (u64 LE) and `n * 32` chunk bytes
    starting at `INPUT_ADDR + 16`, then calls `ssz_merkleize_pow2`
    and writes the 32-byte root to `OUTPUT_ADDR`.

    Test fixtures (in `scripts/codegen-zisk-ssz-merkleize-pow2-check.sh`):
      * n = 1, single zero chunk           → Z_0
      * n = 2, two zero chunks             → Z_1
      * n = 4, four zero chunks            → Z_2
      * n = 8, eight zero chunks           → Z_3
      * n = 16, sixteen zero chunks        → Z_4
      * n = 32, thirty-two zero chunks     → Z_5

    These align with the PR-S5 `Z_d` table values, so a passing
    probe confirms the merkleize loop walks the tree correctly. -/
def ziskSszMerkleizePow2Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a1, 8(a3)                # a1 = n\n" ++
  "  addi a0, a3, 16             # a0 = chunks ptr\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  jal ra, ssz_merkleize_pow2\n" ++
  "  j .Lzs6_done\n" ++
  zkvmSha256Function ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  ".Lzs6_done:"

def ziskSszMerkleizePow2DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 1024"

def ziskSszMerkleizePow2ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszMerkleizePow2Prologue
  dataAsm     := ziskSszMerkleizePow2DataSection
}

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
def sszMerkleizeFunction : String :=
  "ssz_merkleize:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp)\n" ++
  "  sd s6, 56(sp)\n" ++
  "  # s5 = chunks_in ptr; s0 = n; s1 = limit_log2 L; s6 = out ptr\n" ++
  "  mv s5, a0\n" ++
  "  mv s0, a1\n" ++
  "  mv s1, a2\n" ++
  "  mv s6, a3\n" ++
  "  # n == 0 → root is Z_L (look up directly)\n" ++
  "  beqz s0, .Lszm_zero_path\n" ++
  "  # phase 1: compute M = next_pow2(n) and depth_M = log2(M)\n" ++
  "  li t0, 1                    # candidate M\n" ++
  "  li s4, 0                    # candidate depth\n" ++
  ".Lszm_pow2_scan:\n" ++
  "  bge t0, s0, .Lszm_have_M\n" ++
  "  slli t0, t0, 1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lszm_pow2_scan\n" ++
  ".Lszm_have_M:\n" ++
  "  mv s3, t0                   # s3 = M; s4 = depth_M = log2(M)\n" ++
  "  # copy n*32 input bytes into ssz_merkleize_padded, zero-pad the rest\n" ++
  "  la t0, ssz_merkleize_padded\n" ++
  "  slli t1, s0, 5              # t1 = n*32 bytes to copy\n" ++
  "  mv t2, s5                   # src\n" ++
  "  mv t3, t0                   # dst\n" ++
  ".Lszm_cp:\n" ++
  "  beqz t1, .Lszm_pad\n" ++
  "  ld t4, 0(t2)\n" ++
  "  sd t4, 0(t3)\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t1, t1, -8\n" ++
  "  j .Lszm_cp\n" ++
  ".Lszm_pad:\n" ++
  "  sub t1, s3, s0              # t1 = M - n (slots to zero)\n" ++
  "  slli t1, t1, 5              # t1 = (M-n)*32 bytes\n" ++
  ".Lszm_zr:\n" ++
  "  beqz t1, .Lszm_call_pow2\n" ++
  "  sd zero, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t1, t1, -8\n" ++
  "  j .Lszm_zr\n" ++
  ".Lszm_call_pow2:\n" ++
  "  # call ssz_merkleize_pow2(padded, M, ssz_merkleize_partial)\n" ++
  "  la a0, ssz_merkleize_padded\n" ++
  "  mv a1, s3\n" ++
  "  la a2, ssz_merkleize_partial\n" ++
  "  jal ra, ssz_merkleize_pow2\n" ++
  "  # phase 2: mix in Z_d for d in [depth_M, L)\n" ++
  ".Lszm_mix:\n" ++
  "  beq s4, s1, .Lszm_copy_out\n" ++
  "  # ssz_merkleize_partial[0..32]   = current root (input L)\n" ++
  "  # ssz_merkleize_partial[32..64]  = Z_{s4}        (input R)\n" ++
  "  la t0, ssz_zero_hashes\n" ++
  "  slli t1, s4, 5              # offset = s4*32\n" ++
  "  add t0, t0, t1              # &Z_{s4}\n" ++
  "  la t2, ssz_merkleize_partial\n" ++
  "  addi t2, t2, 32             # &partial[32..]\n" ++
  "  ld t3,  0(t0); sd t3,  0(t2)\n" ++
  "  ld t3,  8(t0); sd t3,  8(t2)\n" ++
  "  ld t3, 16(t0); sd t3, 16(t2)\n" ++
  "  ld t3, 24(t0); sd t3, 24(t2)\n" ++
  "  la a0, ssz_merkleize_partial\n" ++
  "  li a1, 64\n" ++
  "  la a2, ssz_merkleize_partial\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lszm_mix\n" ++
  ".Lszm_copy_out:\n" ++
  "  la t0, ssz_merkleize_partial\n" ++
  "  ld t1,  0(t0); sd t1,  0(s6)\n" ++
  "  ld t1,  8(t0); sd t1,  8(s6)\n" ++
  "  ld t1, 16(t0); sd t1, 16(s6)\n" ++
  "  ld t1, 24(t0); sd t1, 24(s6)\n" ++
  "  j .Lszm_ret\n" ++
  ".Lszm_zero_path:\n" ++
  "  # root = Z_L (n == 0 case)\n" ++
  "  la t0, ssz_zero_hashes\n" ++
  "  slli t1, s1, 5\n" ++
  "  add t0, t0, t1\n" ++
  "  ld t1,  0(t0); sd t1,  0(s6)\n" ++
  "  ld t1,  8(t0); sd t1,  8(s6)\n" ++
  "  ld t1, 16(t0); sd t1, 16(s6)\n" ++
  "  ld t1, 24(t0); sd t1, 24(s6)\n" ++
  ".Lszm_ret:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp)\n" ++
  "  ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_ssz_merkleize`: probe BuildUnit that reads
    `(limit_log2 : u64, n : u64, chunks : n * 32 bytes)` from
    the host input region and writes the SSZ root to OUTPUT.
    Input layout:
      bytes  0.. 8 : ignored ziskemu length prefix
      bytes  8..16 : limit_log2 (u64 LE)
      bytes 16..24 : n (u64 LE)
      bytes 24..   : n * 32 chunk bytes -/
def ziskSszMerkleizePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a2, 8(a3)                # a2 = limit_log2 L\n" ++
  "  ld a1, 16(a3)               # a1 = n\n" ++
  "  addi a0, a3, 24             # a0 = chunks ptr\n" ++
  "  li a3, 0xa0010000           # a3 = OUTPUT_ADDR (now caller out ptr)\n" ++
  "  jal ra, ssz_merkleize\n" ++
  "  j .Lzs7_done\n" ++
  zkvmSha256Function ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  sszMerkleizeFunction ++ "\n" ++
  ".Lzs7_done:"

def ziskSszMerkleizeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_padded:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_partial:\n" ++
  "  .zero 64\n" ++
  sszZeroHashesDataSection

def ziskSszMerkleizeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszMerkleizePrologue
  dataAsm     := ziskSszMerkleizeDataSection
}

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
/-- `zisk_ssz_pack_bytes`: probe BuildUnit that reads
    `(L : u64, data : L bytes)` from the host input region,
    calls `ssz_pack_bytes`, and writes the result to OUTPUT in
    the layout `(chunk_count : u64, chunks : chunk_count * 32
    bytes)`. The test script diffs the entire OUTPUT against
    Python's recomputation. Input layout:
      bytes  0.. 8 : L (u64 LE)
      bytes  8..   : L source bytes -/
def ziskSszPackBytesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # a1 = L\n" ++
  "  addi a0, a3, 16             # a0 = src ptr\n" ++
  "  li a2, 0xa0010008           # a2 = dst chunks (OUTPUT + 8)\n" ++
  "  jal ra, ssz_pack_bytes\n" ++
  "  # write chunk count (a0) at OUTPUT + 0\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lzs8_done\n" ++
  sszPackBytesFunction ++ "\n" ++
  ".Lzs8_done:"

def ziskSszPackBytesDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ssz_pack_bytes_scratch:\n" ++
  "  .zero 8"

def ziskSszPackBytesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszPackBytesPrologue
  dataAsm     := ziskSszPackBytesDataSection
}

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
def sszHashTreeRootBytesFunction : String :=
  "ssz_hash_tree_root_bytes:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  # s0 = src; s1 = L; s2 = limit_log2; s3 = out ptr\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv s3, a3\n" ++
  "  # Step 1: pack(src, L) -> ssz_hb_chunks. Returns chunk count in a0.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, ssz_hb_chunks\n" ++
  "  jal ra, ssz_pack_bytes\n" ++
  "  mv s4, a0                  # s4 = chunks count\n" ++
  "  # Step 2: merkleize(ssz_hb_chunks, s4, s2, ssz_hb_partial)\n" ++
  "  la a0, ssz_hb_chunks\n" ++
  "  mv a1, s4\n" ++
  "  mv a2, s2\n" ++
  "  la a3, ssz_hb_partial\n" ++
  "  jal ra, ssz_merkleize\n" ++
  "  # Step 3: write length chunk (u256 LE of L) at ssz_hb_mix + 32..64\n" ++
  "  # Copy partial root into ssz_hb_mix[0..32]\n" ++
  "  la t0, ssz_hb_partial\n" ++
  "  la t1, ssz_hb_mix\n" ++
  "  ld t2,  0(t0); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t0); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  # Length chunk at ssz_hb_mix + 32..64: u64 LE of L, then 24 zero bytes.\n" ++
  "  sd s1, 32(t1)               # low 8 bytes = L (LE)\n" ++
  "  sd zero, 40(t1)\n" ++
  "  sd zero, 48(t1)\n" ++
  "  sd zero, 56(t1)\n" ++
  "  # Step 4: sha256(ssz_hb_mix, 64) -> caller's out ptr (s3)\n" ++
  "  la a0, ssz_hb_mix\n" ++
  "  li a1, 64\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_ssz_hash_tree_root_bytes`: probe BuildUnit that reads
    `(L, limit_log2, data)` from host input, calls the wrapper,
    writes the 32-byte SSZ root to OUTPUT_ADDR.
    Input layout:
      file bytes  0.. 8 : L            (at INPUT_ADDR +  8)
      file bytes  8..16 : limit_log2   (at INPUT_ADDR + 16)
      file bytes 16..   : L source bytes (at INPUT_ADDR + 24) -/
def ziskSszHashTreeRootBytesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # a1 = L\n" ++
  "  ld a2, 16(a4)               # a2 = limit_log2_chunks\n" ++
  "  addi a0, a4, 24             # a0 = src ptr\n" ++
  "  li a3, 0xa0010000           # a3 = OUTPUT_ADDR\n" ++
  "  jal ra, ssz_hash_tree_root_bytes\n" ++
  "  j .Lzs9_done\n" ++
  zkvmSha256Function ++ "\n" ++
  sszPackBytesFunction ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  sszMerkleizeFunction ++ "\n" ++
  sszHashTreeRootBytesFunction ++ "\n" ++
  ".Lzs9_done:"

def ziskSszHashTreeRootBytesDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_padded:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_partial:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_hb_chunks:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_hb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_hb_mix:\n" ++
  "  .zero 64\n" ++
  sszZeroHashesDataSection

def ziskSszHashTreeRootBytesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszHashTreeRootBytesPrologue
  dataAsm     := ziskSszHashTreeRootBytesDataSection
}

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
def sszHashTreeRootListByteListFunction : String :=
  "ssz_hash_tree_root_list_bytelist:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = byte_log2\n" ++
  "  mv s3, a3                  # s3 = count_log2\n" ++
  "  mv s4, a4                  # s4 = out ptr\n" ++
  "  beqz s1, .Lszls_N0          # empty section ⇒ N = 0\n" ++
  "  lbu t0, 0(s0)              # offset_0 = 4*N (LBU-packed: section ptr may be unaligned)\n" ++
  "  lbu t5, 1(s0); slli t5, t5, 8;  or t0, t0, t5\n" ++
  "  lbu t5, 2(s0); slli t5, t5, 16; or t0, t0, t5\n" ++
  "  lbu t5, 3(s0); slli t5, t5, 24; or t0, t0, t5\n" ++
  "  andi t5, t0, 3\n" ++
  "  bnez t5, .Lszls_fail       # offset_0 must equal 4*N\n" ++
  "  srli s5, t0, 2             # s5 = N (element count)\n" ++
  "  beqz s5, .Lszls_fail       # non-empty section cannot encode an empty list\n" ++
  "  li t5, 4096\n" ++
  "  bltu t5, s5, .Lszls_fail   # child root scratch is 4096 roots\n" ++
  "  bltu s1, t0, .Lszls_fail   # offset table must fit in section\n" ++
  "  li s6, 0                   # s6 = i (loop counter)\n" ++
  ".Lszls_loop:\n" ++
  "  beq s6, s5, .Lszls_done_loop\n" ++
  "  slli t0, s6, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lbu t2, 0(t1)              # inner_off_i (LBU-packed)\n" ++
  "  lbu t5, 1(t1); slli t5, t5, 8;  or t2, t2, t5\n" ++
  "  lbu t5, 2(t1); slli t5, t5, 16; or t2, t2, t5\n" ++
  "  lbu t5, 3(t1); slli t5, t5, 24; or t2, t2, t5\n" ++
  "  slli t3, s5, 2\n" ++
  "  bltu t2, t3, .Lszls_fail   # element data starts after offset table\n" ++
  "  bltu s1, t2, .Lszls_fail   # element start must be in section\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s6, 1\n" ++
  "  beq t3, s5, .Lszls_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lbu t4, 0(t3)              # inner_off_{i+1} (LBU-packed)\n" ++
  "  lbu t5, 1(t3); slli t5, t5, 8;  or t4, t4, t5\n" ++
  "  lbu t5, 2(t3); slli t5, t5, 16; or t4, t4, t5\n" ++
  "  lbu t5, 3(t3); slli t5, t5, 24; or t4, t4, t5\n" ++
  "  bltu t4, t2, .Lszls_fail   # offsets must be monotone\n" ++
  "  bltu s1, t4, .Lszls_fail   # next element start must be in section\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lszls_have_end\n" ++
  ".Lszls_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lszls_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  li t1, 32\n" ++
  "  sll t1, t1, s2             # declared ByteList byte capacity\n" ++
  "  bltu t1, a1, .Lszls_fail   # reject element longer than ByteList[B]\n" ++
  "  li t0, 0x200000\n" ++
  "  bltu t0, a1, .Lszls_fail   # ssz_hash_tree_root_bytes scratch supports <=2MiB\n" ++
  "  mv a2, s2                  # byte_log2\n" ++
  "  la a3, ssz_ltb_child_roots\n" ++
  "  slli t0, s6, 5             # 32*i\n" ++
  "  add a3, a3, t0             # &child_roots[i]\n" ++
  "  jal ra, ssz_hash_tree_root_bytes\n" ++
  "  bnez a0, .Lszls_fail\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lszls_loop\n" ++
  ".Lszls_done_loop:\n" ++
  "  la a0, ssz_ltb_child_roots\n" ++
  "  mv a1, s5                  # N\n" ++
  "  mv a2, s3                  # count_log2\n" ++
  "  la a3, ssz_ltb_partial\n" ++
  "  jal ra, ssz_merkleize\n" ++
  "  la t0, ssz_ltb_partial\n" ++
  "  la t1, ssz_ltb_mix\n" ++
  "  ld t2,  0(t0); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t0); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  sd s5, 32(t1)              # length = N (u64 LE)\n" ++
  "  sd zero, 40(t1)\n" ++
  "  sd zero, 48(t1)\n" ++
  "  sd zero, 56(t1)\n" ++
  "  la a0, ssz_ltb_mix\n" ++
  "  li a1, 64\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  j .Lszls_ret\n" ++
  ".Lszls_N0:\n" ++
  "  la t0, ssz_zero_hashes\n" ++
  "  slli t1, s3, 5\n" ++
  "  add t0, t0, t1             # &Z_{count_log2}\n" ++
  "  la t1, ssz_ltb_mix\n" ++
  "  ld t2,  0(t0); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t0); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  sd zero, 32(t1); sd zero, 40(t1)\n" ++
  "  sd zero, 48(t1); sd zero, 56(t1)\n" ++
  "  la a0, ssz_ltb_mix\n" ++
  "  li a1, 64\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, zkvm_sha256\n" ++
  ".Lszls_ret:\n" ++
  "  li a0, 0\n" ++
  "  j .Lszls_restore\n" ++
  ".Lszls_fail:\n" ++
  "  sd zero,  0(s4)\n" ++
  "  sd zero,  8(s4)\n" ++
  "  sd zero, 16(s4)\n" ++
  "  sd zero, 24(s4)\n" ++
  "  li a0, 1\n" ++
  ".Lszls_restore:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_ssz_hash_tree_root_list_bytelist`: probe BuildUnit
    that reads the SSZ-encoded list section from host input and
    writes the SSZ root to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len
      bytes  8..16 : byte_limit_log2
      bytes 16..24 : count_limit_log2
      bytes 24..   : SSZ list section bytes -/
def ziskSszHashTreeRootListByteListPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # section_len\n" ++
  "  ld a2, 16(a5)               # byte_log2\n" ++
  "  ld a3, 24(a5)               # count_log2\n" ++
  "  addi a0, a5, 32             # section ptr\n" ++
  "  li a4, 0xa0010000           # OUTPUT_ADDR\n" ++
  "  jal ra, ssz_hash_tree_root_list_bytelist\n" ++
  "  li t0, 0xa0010020\n" ++
  "  sd a0, 0(t0)                # OUTPUT+32 = status\n" ++
  "  j .Lzs11_done\n" ++
  zkvmSha256Function ++ "\n" ++
  sszPackBytesFunction ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  sszMerkleizeFunction ++ "\n" ++
  sszHashTreeRootBytesFunction ++ "\n" ++
  sszHashTreeRootListByteListFunction ++ "\n" ++
  ".Lzs11_done:"

def ziskSszHashTreeRootListByteListDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_padded:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_partial:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_hb_chunks:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_hb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_hb_mix:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_ltb_child_roots:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_ltb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_ltb_mix:\n" ++
  "  .zero 64\n" ++
  sszZeroHashesDataSection

def ziskSszHashTreeRootListByteListProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszHashTreeRootListByteListPrologue
  dataAsm     := ziskSszHashTreeRootListByteListDataSection
}

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
def sszHashTreeRootExecutionWitnessFunction : String :=
  "ssz_hash_tree_root_execution_witness:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # s0 = section ptr\n" ++
  "  mv s1, a1                   # s1 = section_len\n" ++
  "  mv s2, a2                   # s2 = out ptr\n" ++
  "  lwu s3, 0(s0)               # off_state\n" ++
  "  lwu s4, 4(s0)               # off_codes\n" ++
  "  lwu s5, 8(s0)               # off_headers\n" ++
  "  add s6, s0, s1              # section_end\n" ++
  "  # Field 0: state (List[ByteList[2^20], 2^20]; byte_log2=15, count_log2=20)\n" ++
  "  add a0, s0, s3              # state_start\n" ++
  "  add t0, s0, s4              # state_end\n" ++
  "  sub a1, t0, a0\n" ++
  "  li a2, 15\n" ++
  "  li a3, 20\n" ++
  "  la a4, ssz_ew_field_roots\n" ++
  "  jal ra, ssz_hash_tree_root_list_bytelist\n" ++
  "  bnez a0, .Lszew_ret\n" ++
  "  # Field 1: codes (List[ByteList[2^24], 2^16]; byte_log2=19, count_log2=16)\n" ++
  "  add a0, s0, s4              # codes_start\n" ++
  "  add t0, s0, s5              # codes_end\n" ++
  "  sub a1, t0, a0\n" ++
  "  li a2, 19\n" ++
  "  li a3, 16\n" ++
  "  la a4, ssz_ew_field_roots\n" ++
  "  addi a4, a4, 32\n" ++
  "  jal ra, ssz_hash_tree_root_list_bytelist\n" ++
  "  bnez a0, .Lszew_ret\n" ++
  "  # Field 2: headers (List[ByteList[2^10], 2^8]; byte_log2=5, count_log2=8)\n" ++
  "  add a0, s0, s5              # headers_start\n" ++
  "  sub a1, s6, a0\n" ++
  "  li a2, 5\n" ++
  "  li a3, 8\n" ++
  "  la a4, ssz_ew_field_roots\n" ++
  "  addi a4, a4, 64\n" ++
  "  jal ra, ssz_hash_tree_root_list_bytelist\n" ++
  "  bnez a0, .Lszew_ret\n" ++
  "  # Merkleize 3 field roots, capacity = 4 slots (limit_log2 = 2)\n" ++
  "  la a0, ssz_ew_field_roots\n" ++
  "  li a1, 3\n" ++
  "  li a2, 2\n" ++
  "  mv a3, s2\n" ++
  "  jal ra, ssz_merkleize\n" ++
  "  li a0, 0\n" ++
  ".Lszew_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_ssz_hash_tree_root_execution_witness`: probe BuildUnit
    that reads the SSZ-encoded ExecutionWitness section from host
    input and writes the SSZ root to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len
      bytes  8..   : SSZ ExecutionWitness section bytes -/
def ziskSszHashTreeRootExecutionWitnessPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010000           # OUTPUT_ADDR\n" ++
  "  jal ra, ssz_hash_tree_root_execution_witness\n" ++
  "  li t0, 0xa0010020\n" ++
  "  sd a0, 0(t0)                # OUTPUT+32 = status\n" ++
  "  j .Lzs12_done\n" ++
  zkvmSha256Function ++ "\n" ++
  sszPackBytesFunction ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  sszMerkleizeFunction ++ "\n" ++
  sszHashTreeRootBytesFunction ++ "\n" ++
  sszHashTreeRootListByteListFunction ++ "\n" ++
  sszHashTreeRootExecutionWitnessFunction ++ "\n" ++
  ".Lzs12_done:"

def ziskSszHashTreeRootExecutionWitnessDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_padded:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_partial:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_hb_chunks:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_hb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_hb_mix:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_ltb_child_roots:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_ltb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_ltb_mix:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_ew_field_roots:\n" ++
  "  .zero 96\n" ++
  sszZeroHashesDataSection

def ziskSszHashTreeRootExecutionWitnessProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszHashTreeRootExecutionWitnessPrologue
  dataAsm     := ziskSszHashTreeRootExecutionWitnessDataSection
}

end EvmAsm.Codegen
