/-
  EvmAsm.Codegen.Programs.MptEncode

  MPT encoding helpers + single/two-leaf root computers carved
  out of `EvmAsm.Codegen.Programs.Mpt` per the file-size hard
  cap. Hosts:

    K157  single_leaf_trie_root
    K162  mpt_leaf_node_encode
    K163  mpt_node_slot_encode
    K164  mpt_extension_node_encode
    K165  mpt_branch_node_encode
    K166  nibbles_common_prefix_len
    K167  mpt_branch_payload_two_slots
    K170  mpt_two_leaf_root_indexed
    K171  block_validate_transactions_root_two_tx
    K185  mpt_one_leaf_root_indexed
    K186  block_validate_transactions_root_one_tx

  The cluster covers everything from per-node RLP encoding
  through to two-leaf trie root computation and the matching
  header-field validator. K168/K169 live in
  `Programs/MptEncodeLeafBranch.lean`. Depends on K25
  `bytes_to_nibbles`, K32 `hp_encode_nibbles` (which remain in
  `Programs/Mpt.lean`) plus RLP / Keccak helpers from sibling
  submodules.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.Mpt

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## single_leaf_trie_root -- PR-K157

    Compute the Merkle-Patricia-Trie root for a trie containing
    *exactly one* (key, value) entry:

      path_nibbles = bytes_to_nibbles(key)
      hp_path      = hp_encode_nibbles(path_nibbles, is_leaf=true)
      leaf_node    = rlp([hp_path, value])
      trie_root    = keccak256(leaf_node)

    Direct counterpart of PR-K33 `state_root_single_account`,
    generalised for arbitrary `(key, value)` pairs.

    Use cases:
      * `transactions_root` for a single-tx block: key = rlp(0),
        value = tx_rlp (typed envelope or legacy RLP).
      * `withdrawals_root` for a single-withdrawal block: key =
        rlp(0), value = withdrawal_rlp.
      * `receipts_root` for a single-receipt block: key = rlp(0),
        value = receipt_rlp.

    For multi-entry tries this helper does not apply -- those
    require branch / extension nodes and the full MPT construction
    machinery (separate PR series).

    Composes:
      - PR-K25 `bytes_to_nibbles`        -- expand key bytes
      - PR-K32 `hp_encode_nibbles`       -- HP-encode the path
      - PR-K128 `rlp_encode_bytes`       -- encode hp_path
                                            and value as RLP strings
      - PR-K129 `rlp_encode_list_prefix` -- outer list prefix
      - `zkvm_keccak256` (HashBridge)    -- root hash

    Calling convention:
      a0 (input)  : key ptr (raw key bytes)
      a1 (input)  : key byte length
      a2 (input)  : value ptr (raw value bytes)
      a3 (input)  : value byte length
      a4 (input)  : 32-byte output root ptr
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def singleLeafTrieRootFunction : String :=
  "single_leaf_trie_root:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # key ptr\n" ++
  "  mv s1, a1                   # key len\n" ++
  "  mv s2, a2                   # value ptr\n" ++
  "  mv s3, a3                   # value len\n" ++
  "  mv s4, a4                   # output root ptr\n" ++
  "  # ---- Step 1: expand key bytes to nibbles ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, sltr_nibbles\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  # a0 = 2 * key_len nibbles emitted -- store for HP step\n" ++
  "  la t0, sltr_nibble_count; sd a0, 0(t0)\n" ++
  "  # ---- Step 2: HP-encode the nibbles (leaf=true) ----\n" ++
  "  la a0, sltr_nibbles\n" ++
  "  la t0, sltr_nibble_count; ld a1, 0(t0)\n" ++
  "  li a2, 1                                    # is_leaf = 1\n" ++
  "  la a3, sltr_hp_buf\n" ++
  "  jal ra, hp_encode_nibbles\n" ++
  "  la t0, sltr_hp_len; sd a0, 0(t0)\n" ++
  "  # ---- Step 3: RLP-encode hp_path into the payload buffer ----\n" ++
  "  la a0, sltr_hp_buf\n" ++
  "  la t0, sltr_hp_len; ld a1, 0(t0)\n" ++
  "  la a2, sltr_payload_buf\n" ++
  "  la a3, sltr_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, sltr_field_len; ld t1, 0(t0)         # hp_rlp_len\n" ++
  "  la t0, sltr_cursor; sd t1, 0(t0)            # cursor = hp_rlp_len\n" ++
  "  # ---- Step 4: RLP-encode value at payload[cursor..] ----\n" ++
  "  la t0, sltr_cursor; ld t1, 0(t0)\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, sltr_payload_buf; add a2, a2, t1\n" ++
  "  la a3, sltr_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, sltr_field_len; ld t1, 0(t0)         # value_rlp_len\n" ++
  "  la t0, sltr_cursor; ld t2, 0(t0)\n" ++
  "  add t2, t2, t1                              # total inner payload len\n" ++
  "  la t0, sltr_total_payload; sd t2, 0(t0)\n" ++
  "  # ---- Step 5: write outer list prefix at node_buf[0..] ----\n" ++
  "  mv a0, t2\n" ++
  "  la a1, sltr_node_buf\n" ++
  "  la a2, sltr_field_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, sltr_field_len; ld t1, 0(t0)         # outer_prefix_len\n" ++
  "  la t0, sltr_total_payload; ld t2, 0(t0)\n" ++
  "  # ---- Step 6: copy payload after prefix in node_buf ----\n" ++
  "  la t3, sltr_node_buf; add t3, t3, t1        # dst\n" ++
  "  la t4, sltr_payload_buf                     # src\n" ++
  "  mv t5, t2                                   # remaining\n" ++
  ".Lsltr_cp:\n" ++
  "  beqz t5, .Lsltr_cp_done\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lsltr_cp\n" ++
  ".Lsltr_cp_done:\n" ++
  "  add t1, t1, t2                              # full leaf-node RLP length\n" ++
  "  # ---- Step 7: keccak256(node_buf, full_len) → root ----\n" ++
  "  la a0, sltr_node_buf\n" ++
  "  mv a1, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_single_leaf_trie_root`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : key_len
      bytes  8..16 : value_len
      bytes 16..16+key_len: key
      bytes 16+key_len..   : value (8-byte aligned padding)
    Output layout (256 B):
      bytes  0..32 : 32-byte trie root -/
def ziskSingleLeafTrieRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # key_len\n" ++
  "  ld a3, 16(a5)               # value_len\n" ++
  "  addi a0, a5, 24             # key ptr\n" ++
  "  # value ptr = key_ptr + key_len (rounded up to 8B alignment? No, raw).\n" ++
  "  add a2, a0, a1\n" ++
  "  li a4, 0xa0010000           # output root ptr (32 B)\n" ++
  "  jal ra, single_leaf_trie_root\n" ++
  "  j .Lsltr_pdone\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  singleLeafTrieRootFunction ++ "\n" ++
  ".Lsltr_pdone:"

def ziskSingleLeafTrieRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "sltr_field_len:\n" ++
  "  .zero 8\n" ++
  "sltr_nibble_count:\n" ++
  "  .zero 8\n" ++
  "sltr_hp_len:\n" ++
  "  .zero 8\n" ++
  "sltr_cursor:\n" ++
  "  .zero 8\n" ++
  "sltr_total_payload:\n" ++
  "  .zero 8\n" ++
  "sltr_nibbles:\n" ++
  "  .zero 2048\n" ++
  "sltr_hp_buf:\n" ++
  "  .zero 1024\n" ++
  "sltr_payload_buf:\n" ++
  "  .zero 16384\n" ++
  "sltr_node_buf:\n" ++
  "  .zero 16384"

def ziskSingleLeafTrieRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSingleLeafTrieRootPrologue
  dataAsm     := ziskSingleLeafTrieRootDataSection
}

/-! ## mpt_leaf_node_encode -- PR-K162

    Encode an MPT *leaf node* into RLP, without hashing. This is
    exactly the step before the final keccak in PR-K157
    `single_leaf_trie_root`:

      hp_path     = hp_encode_nibbles(
                      bytes_to_nibbles(path), is_leaf=true)
      leaf_node   = rlp([hp_path, value])
      -- (K157 would now keccak256 this; K162 stops here.)

    Use cases:
      * Multi-leaf MPT construction where a leaf becomes a *child*
        of a branch / extension node. The parent slot encoding
        embeds either the leaf's hash (`keccak256(leaf_node)`)
        if `len(leaf_node) >= 32`, or the leaf's RLP bytes
        verbatim if shorter. K162 produces the bytes that the
        parent-encoder slots in either form.
      * Diagnostics: callers that want to inspect a leaf's wire
        bytes (e.g., for debugging trie shapes) get them without
        the keccak detour.

    Composes:
      - PR-K25 `bytes_to_nibbles`        -- expand path bytes
      - PR-K32 `hp_encode_nibbles`       -- HP-encode (leaf=true)
      - PR-K128 `rlp_encode_bytes`       -- encode hp_path / value
      - PR-K129 `rlp_encode_list_prefix` -- outer list prefix

    Calling convention:
      a0 (input)  : path ptr (raw key bytes)
      a1 (input)  : path byte length
      a2 (input)  : value ptr
      a3 (input)  : value byte length
      a4 (input)  : output buffer ptr
                    (caller supplies enough space)
      a5 (input)  : u64 out length ptr (total bytes written)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def mptLeafNodeEncodeFunction : String :=
  "mpt_leaf_node_encode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # path ptr\n" ++
  "  mv s1, a1                   # path len\n" ++
  "  mv s2, a2                   # value ptr\n" ++
  "  mv s3, a3                   # value len\n" ++
  "  mv s4, a4                   # output ptr\n" ++
  "  mv s5, a5                   # out_length ptr\n" ++
  "  # ---- Step 1: expand path bytes to nibbles ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mlne_nibbles\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  la t0, mlne_nibble_count; sd a0, 0(t0)\n" ++
  "  # ---- Step 2: HP-encode (leaf=true) ----\n" ++
  "  la a0, mlne_nibbles\n" ++
  "  la t0, mlne_nibble_count; ld a1, 0(t0)\n" ++
  "  li a2, 1\n" ++
  "  la a3, mlne_hp_buf\n" ++
  "  jal ra, hp_encode_nibbles\n" ++
  "  la t0, mlne_hp_len; sd a0, 0(t0)\n" ++
  "  # ---- Step 3: RLP-encode hp_path into payload_buf ----\n" ++
  "  la a0, mlne_hp_buf\n" ++
  "  la t0, mlne_hp_len; ld a1, 0(t0)\n" ++
  "  la a2, mlne_payload_buf\n" ++
  "  la a3, mlne_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, mlne_field_len; ld t1, 0(t0)\n" ++
  "  la t0, mlne_cursor; sd t1, 0(t0)\n" ++
  "  # ---- Step 4: RLP-encode value at payload[cursor..] ----\n" ++
  "  la t0, mlne_cursor; ld t1, 0(t0)\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, mlne_payload_buf; add a2, a2, t1\n" ++
  "  la a3, mlne_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, mlne_field_len; ld t1, 0(t0)\n" ++
  "  la t0, mlne_cursor; ld t2, 0(t0)\n" ++
  "  add t2, t2, t1\n" ++
  "  la t0, mlne_total_payload; sd t2, 0(t0)\n" ++
  "  # ---- Step 5: write outer list prefix to output[0..] ----\n" ++
  "  mv a0, t2\n" ++
  "  mv a1, s4\n" ++
  "  la a2, mlne_field_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, mlne_field_len; ld t1, 0(t0)\n" ++
  "  la t0, mlne_total_payload; ld t2, 0(t0)\n" ++
  "  # ---- Step 6: copy payload after prefix in output ----\n" ++
  "  add t3, s4, t1\n" ++
  "  la t4, mlne_payload_buf\n" ++
  "  mv t5, t2\n" ++
  ".Lmlne_cp:\n" ++
  "  beqz t5, .Lmlne_cp_done\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lmlne_cp\n" ++
  ".Lmlne_cp_done:\n" ++
  "  add t1, t1, t2\n" ++
  "  sd t1, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_mpt_leaf_node_encode`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : path_len
      bytes  8..16 : value_len
      bytes 16..16+path_len: path
      bytes (16+path_len)..: value
    Output layout (256 B):
      bytes  0.. 8 : status
      bytes  8..16 : leaf-node RLP length
      bytes 16..   : leaf-node RLP bytes (truncated to fit ziskemu cap) -/
def ziskMptLeafNodeEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # path_len\n" ++
  "  ld a3, 16(a6)               # value_len\n" ++
  "  addi a0, a6, 24             # path ptr\n" ++
  "  add a2, a0, a1              # value ptr\n" ++
  "  li a4, 0xa0010010           # output buffer ptr\n" ++
  "  li a5, 0xa0010008           # out_length ptr\n" ++
  "  jal ra, mpt_leaf_node_encode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmlne_pdone\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFunction ++ "\n" ++
  ".Lmlne_pdone:"

def ziskMptLeafNodeEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mlne_field_len:\n" ++
  "  .zero 8\n" ++
  "mlne_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mlne_hp_len:\n" ++
  "  .zero 8\n" ++
  "mlne_cursor:\n" ++
  "  .zero 8\n" ++
  "mlne_total_payload:\n" ++
  "  .zero 8\n" ++
  "mlne_nibbles:\n" ++
  "  .zero 2048\n" ++
  "mlne_hp_buf:\n" ++
  "  .zero 1024\n" ++
  "mlne_payload_buf:\n" ++
  "  .zero 16384"

def ziskMptLeafNodeEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptLeafNodeEncodePrologue
  dataAsm     := ziskMptLeafNodeEncodeDataSection
}

/-! ## mpt_node_slot_encode -- PR-K163

    Given a child MPT node's RLP, produce the bytes that go
    *verbatim* into a parent node's child-slot when assembling
    the parent's outer RLP list.

      if len(node_rlp) < 32:
        slot_bytes = node_rlp                  -- inline embed
      else:
        slot_bytes = 0xa0 || keccak256(node_rlp)  -- 32-byte
                                                -- string item

    This is the parent-side complement of PR-K112
    `mpt_encode_internal_node`. K112 returns the *raw reference*
    (either RLP bytes verbatim or just the 32-byte hash); K163
    wraps the hashed case with the 0xa0 RLP string-prefix so the
    output is ready to splice into the parent's RLP payload.

    Building block for `mpt_branch_node_encode` (future) and
    `mpt_extension_node_encode` (future).

    Composes:
      - `zkvm_keccak256` (HashBridge) when node_rlp_len >= 32

    Calling convention:
      a0 (input)  : node_rlp ptr
      a1 (input)  : node_rlp byte length
      a2 (input)  : output bytes ptr
                    (caller supplies max(node_rlp_len, 33) bytes)
      a3 (input)  : u64 out length ptr
                    (33 when hashed, node_rlp_len when inline)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def mptNodeSlotEncodeFunction : String :=
  "mpt_node_slot_encode:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a2                   # output ptr\n" ++
  "  mv s1, a3                   # out_length ptr\n" ++
  "  li t0, 32\n" ++
  "  bltu a1, t0, .Lmnse_inline\n" ++
  "  # Hash path: out[0] = 0xa0; keccak256(node_rlp) -> out[1..33].\n" ++
  "  li t1, 0xa0\n" ++
  "  sb t1, 0(s0)\n" ++
  "  mv s2, a0                   # node_rlp ptr stashed\n" ++
  "  # zkvm_keccak256(node_rlp, len, out + 1).\n" ++
  "  addi a2, s0, 1\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li t0, 33\n" ++
  "  sd t0, 0(s1)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmnse_ret\n" ++
  ".Lmnse_inline:\n" ++
  "  # Inline path: copy node_rlp bytes to out.\n" ++
  "  mv t0, a0                   # src cursor\n" ++
  "  mv t1, s0                   # dst cursor\n" ++
  "  mv t2, a1                   # remaining\n" ++
  ".Lmnse_cp:\n" ++
  "  beqz t2, .Lmnse_cp_done\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  sb  t3, 0(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lmnse_cp\n" ++
  ".Lmnse_cp_done:\n" ++
  "  sd a1, 0(s1)\n" ++
  "  li a0, 0\n" ++
  ".Lmnse_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_mpt_node_slot_encode`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : node_rlp_len
      bytes  8..   : node_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : out_length
      bytes 16..   : slot_bytes (up to 33 bytes for hash; up to
                      ziskemu cap minus 16 for inline) -/
def ziskMptNodeSlotEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # node_rlp_len\n" ++
  "  addi a0, a4, 16             # node_rlp ptr\n" ++
  "  li a2, 0xa0010010           # output slot ptr\n" ++
  "  li a3, 0xa0010008           # out_length ptr\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmnse_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  ".Lmnse_pdone:"

def ziskMptNodeSlotEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskMptNodeSlotEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptNodeSlotEncodePrologue
  dataAsm     := ziskMptNodeSlotEncodeDataSection
}

/-! ## mpt_extension_node_encode -- PR-K164

    Encode an MPT *extension* node as RLP:

      ext_node = rlp([hp_encode_nibbles(shared_path, is_leaf=false),
                      child_ref_bytes])

    Where `child_ref_bytes` is the parent-slot encoding of the
    child node produced by PR-K163 `mpt_node_slot_encode` (either
    the child's inline RLP or `0xa0 || keccak256(child_rlp)`).

    Used during multi-leaf MPT root computation: when two
    sub-tries share a path prefix, the parent above the divergence
    is an extension whose path encodes the shared nibbles and
    whose single child is the sub-trie at the divergence point.

    Composes:
      - PR-K32  `hp_encode_nibbles` with is_leaf=false
      - PR-K128 `rlp_encode_bytes`  for hp_path
      - PR-K129 `rlp_encode_list_prefix` for outer list

    Calling convention:
      a0 (input)  : path_nibbles ptr (one byte per nibble,
                    low 4 bits)
      a1 (input)  : nibble count
      a2 (input)  : child_ref_bytes ptr (output of K163 -- already
                    a valid RLP item, embedded verbatim)
      a3 (input)  : child_ref byte length
      a4 (input)  : output buffer ptr
      a5 (input)  : u64 out length ptr (total bytes written)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def mptExtensionNodeEncodeFunction : String :=
  "mpt_extension_node_encode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # path_nibbles ptr\n" ++
  "  mv s1, a1                   # nibble count\n" ++
  "  mv s2, a2                   # child_ref ptr\n" ++
  "  mv s3, a3                   # child_ref len\n" ++
  "  mv s4, a4                   # output ptr\n" ++
  "  mv s5, a5                   # out_length ptr\n" ++
  "  # ---- Step 1: HP-encode nibbles (is_leaf=0) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, mxne_hp_buf\n" ++
  "  jal ra, hp_encode_nibbles\n" ++
  "  la t0, mxne_hp_len; sd a0, 0(t0)\n" ++
  "  # ---- Step 2: RLP-encode hp_path into payload[0..] ----\n" ++
  "  la a0, mxne_hp_buf\n" ++
  "  la t0, mxne_hp_len; ld a1, 0(t0)\n" ++
  "  la a2, mxne_payload_buf\n" ++
  "  la a3, mxne_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, mxne_field_len; ld t1, 0(t0)         # hp_rlp_len\n" ++
  "  la t0, mxne_cursor; sd t1, 0(t0)\n" ++
  "  # ---- Step 3: copy child_ref verbatim into payload[cursor..] ----\n" ++
  "  la t0, mxne_cursor; ld t1, 0(t0)\n" ++
  "  la t2, mxne_payload_buf; add t2, t2, t1     # dst\n" ++
  "  mv t3, s2                                    # src\n" ++
  "  mv t4, s3                                    # remaining\n" ++
  ".Lmxne_cref_cp:\n" ++
  "  beqz t4, .Lmxne_cref_done\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t2)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lmxne_cref_cp\n" ++
  ".Lmxne_cref_done:\n" ++
  "  la t0, mxne_cursor; ld t1, 0(t0)\n" ++
  "  add t2, t1, s3                                # total payload len\n" ++
  "  la t0, mxne_total_payload; sd t2, 0(t0)\n" ++
  "  # ---- Step 4: outer list prefix to output[0..] ----\n" ++
  "  mv a0, t2; mv a1, s4\n" ++
  "  la a2, mxne_field_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, mxne_field_len; ld t1, 0(t0)          # outer_prefix_len\n" ++
  "  la t0, mxne_total_payload; ld t2, 0(t0)\n" ++
  "  # ---- Step 5: copy payload after prefix ----\n" ++
  "  add t3, s4, t1                                # dst\n" ++
  "  la t4, mxne_payload_buf                       # src\n" ++
  "  mv t5, t2                                     # remaining\n" ++
  ".Lmxne_body_cp:\n" ++
  "  beqz t5, .Lmxne_body_done\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lmxne_body_cp\n" ++
  ".Lmxne_body_done:\n" ++
  "  add t1, t1, t2                                # total written = prefix + payload\n" ++
  "  sd t1, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_mpt_extension_node_encode`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : nibble_count
      bytes  8..16 : child_ref_len
      bytes 16..16+nibble_count: path_nibbles (1 byte per nibble)
      bytes (16+nibble_count)..: child_ref bytes
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : ext-node RLP length
      bytes 16..   : ext-node RLP bytes (truncated to ziskemu cap) -/
def ziskMptExtensionNodeEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # nibble_count\n" ++
  "  ld a3, 16(a6)               # child_ref_len\n" ++
  "  addi a0, a6, 24             # path_nibbles ptr\n" ++
  "  add a2, a0, a1              # child_ref ptr\n" ++
  "  li a4, 0xa0010010           # output buffer ptr\n" ++
  "  li a5, 0xa0010008           # out_length ptr\n" ++
  "  jal ra, mpt_extension_node_encode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmxne_pdone\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptExtensionNodeEncodeFunction ++ "\n" ++
  ".Lmxne_pdone:"

def ziskMptExtensionNodeEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mxne_field_len:\n" ++
  "  .zero 8\n" ++
  "mxne_hp_len:\n" ++
  "  .zero 8\n" ++
  "mxne_cursor:\n" ++
  "  .zero 8\n" ++
  "mxne_total_payload:\n" ++
  "  .zero 8\n" ++
  "mxne_hp_buf:\n" ++
  "  .zero 1024\n" ++
  "mxne_payload_buf:\n" ++
  "  .zero 16384"

def ziskMptExtensionNodeEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptExtensionNodeEncodePrologue
  dataAsm     := ziskMptExtensionNodeEncodeDataSection
}

/-! ## mpt_branch_node_encode -- PR-K165

    Encode an MPT *branch* node as RLP, given a pre-concatenated
    17-slot payload:

      branch_node = rlp([slot_0, slot_1, ..., slot_15, value])

    Each of the 17 slots is one RLP item, already encoded by the
    caller in one of three forms:
      * empty: `0x80`              (1 byte)
      * inline child: `child_rlp`  (variable; len < 32)
      * hashed child: `0xa0 || keccak256(child_rlp)` (33 bytes)
      * value slot: `0x80` if no value lives at this prefix, else
        the RLP-encoded value bytes.

    The caller arranges all 17 slot encodings in order and passes
    the concatenated payload; this helper just emits the outer
    list prefix for that payload length, then copies the payload.
    Use PR-K163 `mpt_node_slot_encode` to produce each child
    slot's bytes.

    Composes:
      - PR-K129 `rlp_encode_list_prefix` for the outer prefix

    Calling convention:
      a0 (input)  : slot_payload ptr (pre-concatenated 17-slot
                    bytes; caller's responsibility to put the
                    slots in nibble order and end with the value
                    slot)
      a1 (input)  : slot_payload byte length
      a2 (input)  : output buffer ptr
                    (caller supplies >= 9 + a1 bytes)
      a3 (input)  : u64 out length ptr (total bytes written:
                    prefix_len + payload_len)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def mptBranchNodeEncodeFunction : String :=
  "mpt_branch_node_encode:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # slot_payload ptr\n" ++
  "  mv s1, a1                   # slot_payload len\n" ++
  "  mv s2, a2                   # output ptr\n" ++
  "  mv s3, a3                   # out_length ptr\n" ++
  "  # ---- Write outer list prefix at output[0..] ----\n" ++
  "  mv a0, s1; mv a1, s2\n" ++
  "  la a2, mbne_field_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, mbne_field_len; ld t1, 0(t0)         # prefix_len\n" ++
  "  # ---- Copy payload after prefix ----\n" ++
  "  add t2, s2, t1                                # dst = output + prefix_len\n" ++
  "  mv t3, s0                                     # src\n" ++
  "  mv t4, s1                                     # remaining\n" ++
  ".Lmbne_cp:\n" ++
  "  beqz t4, .Lmbne_cp_done\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t2)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lmbne_cp\n" ++
  ".Lmbne_cp_done:\n" ++
  "  add t1, t1, s1                                # total written\n" ++
  "  sd t1, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_mpt_branch_node_encode`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : slot_payload_len
      bytes  8..   : slot_payload (pre-concatenated 17-slot bytes)
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : branch-node RLP length
      bytes 16..   : branch-node RLP bytes (truncated to ziskemu
                     cap if oversized) -/
def ziskMptBranchNodeEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # slot_payload_len\n" ++
  "  addi a0, a4, 16             # slot_payload ptr\n" ++
  "  li a2, 0xa0010010           # output buffer ptr\n" ++
  "  li a3, 0xa0010008           # out_length ptr\n" ++
  "  jal ra, mpt_branch_node_encode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmbne_pdone\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptBranchNodeEncodeFunction ++ "\n" ++
  ".Lmbne_pdone:"

def ziskMptBranchNodeEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbne_field_len:\n" ++
  "  .zero 8"

def ziskMptBranchNodeEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptBranchNodeEncodePrologue
  dataAsm     := ziskMptBranchNodeEncodeDataSection
}

/-! ## nibbles_common_prefix_len -- PR-K166

    Walk two nibble arrays (one byte per nibble, low 4 bits) from
    the start and return the length of their shared prefix. Stops
    at the first differing nibble or at the end of the shorter
    array, whichever comes first.

    Direct building block for multi-leaf MPT root computation:
    given two leaf paths in nibble form, the depth at which they
    diverge tells the constructor whether to emit an extension
    node (for the shared prefix) followed by a branch (at the
    divergence point), or just a branch directly (if cpl == 0).

    Example: for sequential indices 0 and 1 in an indexed trie,
    `rlp(0) = 0x80` and `rlp(1) = 0x01` expand to nibbles
    `[0x8, 0x0]` and `[0x0, 0x1]`; their common prefix is empty
    (cpl == 0), so the root is a branch.

    Pure register arithmetic, leaf-callable, no scratch.

    Calling convention:
      a0 (input)  : nibbles_a ptr (1 byte per nibble)
      a1 (input)  : nibbles_a count
      a2 (input)  : nibbles_b ptr
      a3 (input)  : nibbles_b count
      a4 (input)  : u64 out ptr (common prefix length, in nibbles)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def nibblesCommonPrefixLenFunction : String :=
  "nibbles_common_prefix_len:\n" ++
  "  # min(a_count, b_count)\n" ++
  "  bltu a1, a3, .Lncpl_min_ok\n" ++
  "  mv a1, a3\n" ++
  ".Lncpl_min_ok:\n" ++
  "  li t0, 0                   # cpl accumulator\n" ++
  "  mv t1, a0                  # a cursor\n" ++
  "  mv t2, a2                  # b cursor\n" ++
  ".Lncpl_loop:\n" ++
  "  bge t0, a1, .Lncpl_done\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bne t3, t4, .Lncpl_done\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lncpl_loop\n" ++
  ".Lncpl_done:\n" ++
  "  sd t0, 0(a4)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_nibbles_common_prefix_len`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : a_count
      bytes  8..16 : b_count
      bytes 16..16+a_count: nibbles_a
      bytes (16+a_count)..: nibbles_b
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : common prefix length -/
def ziskNibblesCommonPrefixLenPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # a_count\n" ++
  "  ld a3, 16(a5)               # b_count\n" ++
  "  addi a0, a5, 24             # nibbles_a ptr\n" ++
  "  add a2, a0, a1              # nibbles_b ptr\n" ++
  "  li a4, 0xa0010008           # cpl out\n" ++
  "  jal ra, nibbles_common_prefix_len\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lncpl_pdone\n" ++
  nibblesCommonPrefixLenFunction ++ "\n" ++
  ".Lncpl_pdone:"

def ziskNibblesCommonPrefixLenDataSection : String :=
  ".section .data\n" ++
  "ncpl_pad:\n" ++
  "  .zero 8"

def ziskNibblesCommonPrefixLenProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskNibblesCommonPrefixLenPrologue
  dataAsm     := ziskNibblesCommonPrefixLenDataSection
}

/-! ## mpt_branch_payload_two_slots -- PR-K167

    Produce the 17-slot payload bytes for an MPT branch node
    with exactly two active slots and the remaining 15 slots
    (plus the value slot at index 16) filled with empty
    encodings (`0x80`).

    Direct building block for **two-leaf MPT root computation**:
    after PR-K166 has determined the divergence nibble and
    PR-K162/K163 have produced each leaf's parent-slot bytes,
    this helper builds the branch payload that PR-K165 then
    wraps into the final branch-node RLP.

    Empty slots use the RLP empty-string marker `0x80` (1 byte
    each). The value slot is always empty for indexed-trie use
    cases (transactions / receipts / withdrawals); callers that
    need a value at the branch's exact prefix pass that slot
    explicitly as one of the two active slots (idx = 16).

    Output length: `16 + len_a + len_b` bytes (15 empty children
    slots + 1 empty value slot at 0x80 each + the two active
    slots' bytes).

    Composes: nothing (pure byte copying / 0x80 fill).

    Calling convention:
      a0 (input)  : idx_a (u64; 0..16)
      a1 (input)  : bytes_a ptr (slot a's parent-slot encoding)
      a2 (input)  : len_a
      a3 (input)  : idx_b (u64; 0..16; must differ from idx_a)
      a4 (input)  : bytes_b ptr
      a5 (input)  : len_b
      a6 (input)  : output buffer ptr
                    (caller supplies >= 16 + len_a + len_b bytes)
      a7 (input)  : u64 out length ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : idx_a >= 17 or idx_b >= 17 or idx_a == idx_b -/
def mptBranchPayloadTwoSlotsFunction : String :=
  "mpt_branch_payload_two_slots:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # idx_a\n" ++
  "  mv s1, a1                   # bytes_a ptr\n" ++
  "  mv s2, a2                   # len_a\n" ++
  "  mv s3, a3                   # idx_b\n" ++
  "  mv s4, a4                   # bytes_b ptr\n" ++
  "  mv s5, a5                   # len_b\n" ++
  "  # ---- Validate ----\n" ++
  "  li t0, 17\n" ++
  "  bgeu s0, t0, .Lmbpts_fail\n" ++
  "  bgeu s3, t0, .Lmbpts_fail\n" ++
  "  beq  s0, s3, .Lmbpts_fail\n" ++
  "  # ---- Walk slot indices 0..16, emitting bytes ----\n" ++
  "  mv t1, a6                   # output cursor\n" ++
  "  li t2, 0                    # i\n" ++
  ".Lmbpts_loop:\n" ++
  "  li t0, 17\n" ++
  "  bge t2, t0, .Lmbpts_done\n" ++
  "  beq t2, s0, .Lmbpts_emit_a\n" ++
  "  beq t2, s3, .Lmbpts_emit_b\n" ++
  "  # Empty slot: write 0x80.\n" ++
  "  li t3, 0x80\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t1, t1, 1\n" ++
  "  j .Lmbpts_next\n" ++
  ".Lmbpts_emit_a:\n" ++
  "  # Copy len_a bytes from bytes_a to output.\n" ++
  "  mv t3, s1\n" ++
  "  mv t4, s2\n" ++
  ".Lmbpts_cp_a:\n" ++
  "  beqz t4, .Lmbpts_next\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t1)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lmbpts_cp_a\n" ++
  ".Lmbpts_emit_b:\n" ++
  "  mv t3, s4\n" ++
  "  mv t4, s5\n" ++
  ".Lmbpts_cp_b:\n" ++
  "  beqz t4, .Lmbpts_next\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t1)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lmbpts_cp_b\n" ++
  ".Lmbpts_next:\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lmbpts_loop\n" ++
  ".Lmbpts_done:\n" ++
  "  # out_length = cursor - output_start.\n" ++
  "  sub t1, t1, a6\n" ++
  "  sd t1, 0(a7)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbpts_ret\n" ++
  ".Lmbpts_fail:\n" ++
  "  sd zero, 0(a7)\n" ++
  "  li a0, 1\n" ++
  ".Lmbpts_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_mpt_branch_payload_two_slots`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : idx_a
      bytes  8..16 : len_a
      bytes 16..24 : idx_b
      bytes 24..32 : len_b
      bytes 32..32+len_a: bytes_a
      bytes (32+len_a)..: bytes_b
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : out_length
      bytes 16..   : 17-slot payload bytes (truncated to ziskemu cap) -/
def ziskMptBranchPayloadTwoSlotsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a0, 8(t0)                # idx_a\n" ++
  "  ld a2, 16(t0)               # len_a\n" ++
  "  ld a3, 24(t0)               # idx_b\n" ++
  "  ld a5, 32(t0)               # len_b\n" ++
  "  addi a1, t0, 40             # bytes_a ptr\n" ++
  "  add  a4, a1, a2             # bytes_b ptr\n" ++
  "  li a6, 0xa0010010           # output ptr\n" ++
  "  li a7, 0xa0010008           # out_length ptr\n" ++
  "  jal ra, mpt_branch_payload_two_slots\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmbpts_pdone\n" ++
  mptBranchPayloadTwoSlotsFunction ++ "\n" ++
  ".Lmbpts_pdone:"

def ziskMptBranchPayloadTwoSlotsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbpts_pad:\n" ++
  "  .zero 8"

def ziskMptBranchPayloadTwoSlotsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptBranchPayloadTwoSlotsPrologue
  dataAsm     := ziskMptBranchPayloadTwoSlotsDataSection
}

end EvmAsm.Codegen
