/-
  EvmAsm.Codegen.Programs.MptEncodeLeafBranch

  MPT leaf-from-nibbles and branch-node keccak helpers split out
  from EvmAsm.Codegen.Programs.MptEncode.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.MptEncode

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

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
      a0 (output) : 0 (always succeeds). -/
def mptLeafNodeEncodeFromNibblesFunction : String :=
  "mpt_leaf_node_encode_from_nibbles:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # path_nibbles ptr\n" ++
  "  mv s1, a1                   # nibble count\n" ++
  "  mv s2, a2                   # value ptr\n" ++
  "  mv s3, a3                   # value len\n" ++
  "  mv s4, a4                   # output ptr\n" ++
  "  mv s5, a5                   # out_length ptr\n" ++
  "  # ---- Step 1: HP-encode (leaf=true) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, mlnen_hp_buf\n" ++
  "  jal ra, hp_encode_nibbles\n" ++
  "  la t0, mlnen_hp_len; sd a0, 0(t0)\n" ++
  "  # ---- Step 2: RLP-encode hp_path into payload_buf ----\n" ++
  "  la a0, mlnen_hp_buf\n" ++
  "  la t0, mlnen_hp_len; ld a1, 0(t0)\n" ++
  "  la a2, mlnen_payload_buf\n" ++
  "  la a3, mlnen_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, mlnen_field_len; ld t1, 0(t0)\n" ++
  "  la t0, mlnen_cursor; sd t1, 0(t0)\n" ++
  "  # ---- Step 3: RLP-encode value at payload[cursor..] ----\n" ++
  "  la t0, mlnen_cursor; ld t1, 0(t0)\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, mlnen_payload_buf; add a2, a2, t1\n" ++
  "  la a3, mlnen_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, mlnen_field_len; ld t1, 0(t0)\n" ++
  "  la t0, mlnen_cursor; ld t2, 0(t0)\n" ++
  "  add t2, t2, t1\n" ++
  "  la t0, mlnen_total_payload; sd t2, 0(t0)\n" ++
  "  # ---- Step 4: outer list prefix to output[0..] ----\n" ++
  "  mv a0, t2; mv a1, s4\n" ++
  "  la a2, mlnen_field_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, mlnen_field_len; ld t1, 0(t0)\n" ++
  "  la t0, mlnen_total_payload; ld t2, 0(t0)\n" ++
  "  # ---- Step 5: copy payload after prefix ----\n" ++
  "  add t3, s4, t1\n" ++
  "  la t4, mlnen_payload_buf\n" ++
  "  mv t5, t2\n" ++
  ".Lmlnen_cp:\n" ++
  "  beqz t5, .Lmlnen_cp_done\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lmlnen_cp\n" ++
  ".Lmlnen_cp_done:\n" ++
  "  add t1, t1, t2\n" ++
  "  sd t1, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

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

def ziskMptLeafNodeEncodeFromNibblesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptLeafNodeEncodeFromNibblesPrologue
  dataAsm     := ziskMptLeafNodeEncodeFromNibblesDataSection
}

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

def ziskMptBranchNodeKeccakProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptBranchNodeKeccakPrologue
  dataAsm     := ziskMptBranchNodeKeccakDataSection
}



end EvmAsm.Codegen
