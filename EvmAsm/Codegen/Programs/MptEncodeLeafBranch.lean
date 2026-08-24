/-
  EvmAsm.Codegen.Programs.MptEncodeLeafBranch

  MPT leaf-from-nibbles and branch-node keccak helpers split out
  from EvmAsm.Codegen.Programs.MptEncode.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! Conservative bound for `mlnen_payload_buf`.

    The helper RLP-encodes `hp_path || value` into a fixed 16 KiB scratch.
    Keep the accepted raw value below that capacity with enough room for the
    value's own RLP prefix and the small HP field. Larger values need a
    streaming/large-buffer path; returning failure is better than corrupting
    adjacent globals. -/
def mptLeafNodeMaxScratchValueBytes : Nat := 16000

/-! ## mpt_leaf_node_encode_from_nibbles -- PR-K168

    Encode an MPT leaf node directly from a *nibble* path (one
    byte per nibble, low 4 bits) and a raw value, without the
    bytes-to-nibbles expansion step. Mirrors PR-K162
    `mpt_leaf_node_encode` but skips the path-bytes-to-nibbles
    front:

      hp_path     = hp_encode_nibbles(path_nibbles, is_leaf=true)
      leaf_node   = rlp([hp_path, value])

    The bytes-input variant (K162) is the right helper when the
    path comes from a raw key (e.g., `rlp(i)` for a
    transactions-trie key). The nibbles-input variant (this PR)
    is the right helper for multi-leaf MPT construction where
    the leaf path is a *suffix of nibbles* produced by walking
    down from a shared prefix.

    Composes:
      - PR-K32  `hp_encode_nibbles` with is_leaf=true
      - PR-K128 `rlp_encode_bytes`  for hp_path / value
      - PR-K129 `rlp_encode_list_prefix` for the outer list

    Calling convention:
      a0 (input)  : path_nibbles ptr (one byte per nibble,
                    low 4 bits)
      a1 (input)  : nibble count
      a2 (input)  : value ptr
      a3 (input)  : value byte length
      a4 (input)  : output buffer ptr (caller-supplied)
      a5 (input)  : u64 out length ptr (total bytes written)
      ra (input)  : return
      a0 (output) : 0 on success, 1 on invalid output pointer. -/
def mptLeafNodeEncodeFromNibbles_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
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
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .ADDIW .x5 .x0 (5 : BitVec 12),
    .SLLI .x5 .x5 (29 : BitVec 6),
    .BLTU .x20 .x5 (brOff (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 460) (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 64)),
    .BLTU .x21 .x5 (brOff (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 460) (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 68)),
    .ADDIW .x5 .x0 (3 : BitVec 12),
    .SLLI .x5 .x5 (30 : BitVec 6),
    .BGEU .x20 .x5 (brOff (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 460) (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 80)),
    .ADDIW .x5 .x0 (3 : BitVec 12),
    .SLLI .x5 .x5 (30 : BitVec 6),
    .ADDI .x5 .x5 (-8 : BitVec 12),
    .BLTU .x5 .x21 (brOff (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 460) (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 96)),
    .LUI .x5 (4 : BitVec 20),
    .ADDIW .x5 .x5 (-384 : BitVec 12),
    .BLTU .x5 .x19 (brOff (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 460) (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 108)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mlnen_hp_buf (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 124)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mlnen_hp_buf (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 124)),
    .JAL .x1 (jalOff GuestAddrs.hp_encode_nibbles (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 132)),
    .AUIPC .x5 (laHi GuestAddrs.mlnen_hp_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 136)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mlnen_hp_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 136)),
    .SD .x5 .x10 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.mlnen_hp_buf (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 148)),
    .ADDI .x10 .x10 (laLo GuestAddrs.mlnen_hp_buf (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 148)),
    .AUIPC .x5 (laHi GuestAddrs.mlnen_hp_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 156)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mlnen_hp_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 156)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.mlnen_payload_buf (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 168)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mlnen_payload_buf (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 168)),
    .AUIPC .x13 (laHi GuestAddrs.mlnen_field_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 176)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mlnen_field_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 176)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 184)),
    .AUIPC .x5 (laHi GuestAddrs.mlnen_field_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 188)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mlnen_field_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 188)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mlnen_cursor (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mlnen_cursor (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 200)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mlnen_cursor (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 212)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mlnen_cursor (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 212)),
    .LD .x6 .x5 (0 : BitVec 12),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .AUIPC .x12 (laHi GuestAddrs.mlnen_payload_buf (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 232)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mlnen_payload_buf (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 232)),
    .ADD .x12 .x12 .x6,
    .AUIPC .x13 (laHi GuestAddrs.mlnen_field_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 244)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mlnen_field_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 244)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 252)),
    .AUIPC .x5 (laHi GuestAddrs.mlnen_field_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 256)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mlnen_field_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 256)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mlnen_cursor (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 268)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mlnen_cursor (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 268)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x7 .x7 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mlnen_total_payload (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 284)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mlnen_total_payload (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 284)),
    .SD .x5 .x7 (0 : BitVec 12),
    .MV .x10 .x7,
    .MV .x11 .x20,
    .AUIPC .x12 (laHi GuestAddrs.mlnen_field_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 304)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mlnen_field_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 304)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 312)),
    .AUIPC .x5 (laHi GuestAddrs.mlnen_field_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 316)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mlnen_field_len (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 316)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mlnen_total_payload (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 328)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mlnen_total_payload (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 328)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x31 .x20 .x6,
    .BLTU .x31 .x20 (brOff (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 460) (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 344)),
    .ADD .x31 .x31 .x7,
    .BLTU .x31 .x20 (brOff (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 460) (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 352)),
    .ADDIW .x5 .x0 (3 : BitVec 12),
    .SLLI .x5 .x5 (30 : BitVec 6),
    .BLTU .x5 .x31 (brOff (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 460) (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 364)),
    .ADD .x28 .x20 .x6,
    .AUIPC .x29 (laHi GuestAddrs.mlnen_payload_buf (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 372)),
    .ADDI .x29 .x29 (laLo GuestAddrs.mlnen_payload_buf (GuestAddrs.mpt_leaf_node_encode_from_nibbles + 372)),
    .MV .x30 .x7,
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x29 (0 : BitVec 12),
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x6 .x6 .x7,
    .SD .x21 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptLeafNodeEncodeFromNibbles_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptLeafNodeEncodeFromNibbles_relocs : RelocTable :=
  [ (31, .la .x13 "mlnen_hp_buf"),
    (33, .jal .x1 "hp_encode_nibbles"),
    (34, .la .x5 "mlnen_hp_len"),
    (37, .la .x10 "mlnen_hp_buf"),
    (39, .la .x5 "mlnen_hp_len"),
    (42, .la .x12 "mlnen_payload_buf"),
    (44, .la .x13 "mlnen_field_len"),
    (46, .jal .x1 "rlp_encode_bytes"),
    (47, .la .x5 "mlnen_field_len"),
    (50, .la .x5 "mlnen_cursor"),
    (53, .la .x5 "mlnen_cursor"),
    (58, .la .x12 "mlnen_payload_buf"),
    (61, .la .x13 "mlnen_field_len"),
    (63, .jal .x1 "rlp_encode_bytes"),
    (64, .la .x5 "mlnen_field_len"),
    (67, .la .x5 "mlnen_cursor"),
    (71, .la .x5 "mlnen_total_payload"),
    (76, .la .x12 "mlnen_field_len"),
    (78, .jal .x1 "rlp_encode_list_prefix"),
    (79, .la .x5 "mlnen_field_len"),
    (82, .la .x5 "mlnen_total_payload"),
    (93, .la .x29 "mlnen_payload_buf") ]

def mptLeafNodeEncodeFromNibblesFunction : String :=
  "mpt_leaf_node_encode_from_nibbles:\n" ++ emitProgramR mptLeafNodeEncodeFromNibbles_prog mptLeafNodeEncodeFromNibbles_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptLeafNodeEncodeFromNibbles_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptLeafNodeEncodeFromNibblesFunction_eq_prog :
    mptLeafNodeEncodeFromNibblesFunction = "mpt_leaf_node_encode_from_nibbles:\n" ++ emitProgramR mptLeafNodeEncodeFromNibbles_prog mptLeafNodeEncodeFromNibbles_relocs := rfl

#guard mptLeafNodeEncodeFromNibblesFunction.startsWith "mpt_leaf_node_encode_from_nibbles:\n"
#guard mptLeafNodeEncodeFromNibbles_prog.length = 125
/-- `zisk_mpt_leaf_node_encode_from_nibbles`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : nibble_count
      bytes  8..16 : value_len
      bytes 16..16+nibble_count: path_nibbles
      bytes (16+nibble_count)..: value -/
def ziskMptLeafNodeEncodeFromNibblesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # nibble_count\n" ++
  "  ld a3, 16(a6)               # value_len\n" ++
  "  addi a0, a6, 24             # path_nibbles ptr\n" ++
  "  add a2, a0, a1              # value ptr\n" ++
  "  li a4, 0xa0010010           # output buffer ptr\n" ++
  "  li a5, 0xa0010008           # out_length ptr\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmlnen_pdone\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  ".Lmlnen_pdone:"

def ziskMptLeafNodeEncodeFromNibblesDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mlnen_field_len:\n" ++
  "  .zero 8\n" ++
  "mlnen_hp_len:\n" ++
  "  .zero 8\n" ++
  "mlnen_cursor:\n" ++
  "  .zero 8\n" ++
  "mlnen_total_payload:\n" ++
  "  .zero 8\n" ++
  "mlnen_hp_buf:\n" ++
  "  .zero 1024\n" ++
  "mlnen_payload_buf:\n" ++
  "  .zero 16384"


/-! ## mpt_branch_node_keccak -- PR-K169

    Compose PR-K165 `mpt_branch_node_encode` with
    `zkvm_keccak256`: given a pre-concatenated 17-slot payload,
    produce the 32-byte keccak256 of the branch-node RLP.

    Direct primitive for the trie root when the trie's root *is*
    a branch node. This is the common case for 2-entry indexed
    tries (transactions / receipts / withdrawals) when the two
    keys diverge at the first nibble:

      * `rlp(0) = 0x80` (nibbles `[8, 0]`)
      * `rlp(1) = 0x01` (nibbles `[0, 1]`)

    The shared prefix is empty (cpl = 0; cf. PR-K166), so the
    root is directly `keccak256(branch_node_rlp)` with the two
    leaves' parent-slot encodings sitting at slots 0 and 8 (and
    the rest empty, per K167's payload-assembler).

    Composes:
      - PR-K165 `mpt_branch_node_encode`  for the outer wrap
      - `zkvm_keccak256` (HashBridge)     for the root hash

    Calling convention:
      a0 (input)  : slot_payload ptr (pre-concatenated 17-slot
                    bytes; caller's responsibility to put the
                    slots in nibble order and end with the value
                    slot)
      a1 (input)  : slot_payload byte length
      a2 (input)  : 32-byte output root ptr
      ra (input)  : return
      a0 (output) : 0 (always succeeds).

    Uses a 16 KiB `.data` scratch buffer for the branch-node RLP
    bytes between the K165 emit step and the keccak step. -/
def mptBranchNodeKeccakFunction : String :=
  "mpt_branch_node_keccak:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # slot_payload ptr\n" ++
  "  mv s1, a1                   # slot_payload len\n" ++
  "  mv s2, a2                   # output root ptr\n" ++
  "  # ---- Step 1: emit branch-node RLP to mbnk_node_buf ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mbnk_node_buf\n" ++
  "  la a3, mbnk_node_len\n" ++
  "  jal ra, mpt_branch_node_encode\n" ++
  "  # ---- Step 2: keccak256(mbnk_node_buf, mbnk_node_len) ----\n" ++
  "  la a0, mbnk_node_buf\n" ++
  "  la t0, mbnk_node_len; ld a1, 0(t0)\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_mpt_branch_node_keccak`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : slot_payload_len
      bytes  8..   : slot_payload bytes
    Output layout:
      bytes  0..32 : 32-byte branch-node keccak256 root -/
def ziskMptBranchNodeKeccakPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # slot_payload_len\n" ++
  "  addi a0, a3, 16             # slot_payload ptr\n" ++
  "  li a2, 0xa0010000           # output root ptr (32 B)\n" ++
  "  jal ra, mpt_branch_node_keccak\n" ++
  "  j .Lmbnk_pdone\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptBranchNodeEncodeFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptBranchNodeKeccakFunction ++ "\n" ++
  ".Lmbnk_pdone:"

def ziskMptBranchNodeKeccakDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "mbne_field_len:\n" ++
  "  .zero 8\n" ++
  "mbnk_node_len:\n" ++
  "  .zero 8\n" ++
  "mbnk_node_buf:\n" ++
  "  .zero 16384"




end EvmAsm.Codegen
