/-
  EvmAsm.Codegen.Programs.MptInsertWalk

  mpt_insert_walk (bead evm-asm-fhsxz.2.4.2.6.1): the divergence-classifying
  descent that is the foundation for inserting a NEW key into a witness-backed
  MPT (account creation for withdrawals to absent/precompile recipients).

  It mirrors `mpt_set_record_walk` (Programs/MptSet.lean), which descends a key
  and jumps to a single `not_found` exit at every divergence. mpt_insert_walk
  instead CLASSIFIES the divergence and records the context a later restructure +
  bubble-up pass (mpt_insert, bead .2.4.2.6.2) needs:

    case 0 BRANCH_EMPTY_SLOT : path reaches a branch whose child slot for the
                               next nibble is empty. The branch is the terminal
                               (un-pushed from the ancestor stack); the new leaf
                               goes at slot path[consumed], key path[consumed+1..].
    case 1 LEAF_SPLIT        : path reaches a leaf whose key diverges. match_len
                               = shared-prefix nibbles; split into branch (+ an
                               extension for the shared prefix).
    case 2 EXTENSION_SPLIT   : path diverges inside an extension's key segment.
                               match_len = matched ext nibbles.
    case 3 EMPTY_TRIE        : root == EMPTY_TRIE_ROOT; the whole trie is a single
                               new leaf.
    case 4 EXISTS            : the key is already present (a value-update, not an
                               insert). Does not occur in the withdrawal path
                               (the caller mpt_walks first), reported defensively.
    case 5 BRANCH_VALUE      : path is exhausted exactly at a branch (value slot
                               16). Does not occur for fixed-length 64-nibble
                               account paths, reported defensively.

  The ancestor stack (`stack_out`, 32 B per branch/extension above the terminal,
  root->leaf order) is recorded identically to mpt_set_record_walk so the same
  bubble-up pass re-roots after the terminal is restructured.

  Reuses mpt_walk's scratch labels (mw_*) from `ziskMptWalkDataSection`; adds
  `iw_empty_trie_root` (the 32-byte EMPTY_TRIE_ROOT = keccak256(rlp(b''))).
  All multi-byte work is on 8-aligned scratch; path/key nibbles are read
  byte-wise (no-misaligned invariant).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Mpt

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_insert_walk -- classify where an ABSENT key diverges from the trie

    Calling convention (identical inputs to mpt_set_record_walk):
      a0 (input)  : root_hash ptr (32 bytes)
      a1 (input)  : witness section ptr
      a2 (input)  : witness section_len
      a3 (input)  : path_nibbles ptr (one byte per nibble)
      a4 (input)  : path_nibbles_len
      a5 (input)  : stack_out ptr (32 bytes per ancestor node)
      a6 (input)  : meta_out ptr (48 bytes)
      ra (input)  : return
      a0 (output) : 0 (diverged + classified, see case) / 1 (incomplete witness,
                    lookup miss) / 2 (parse error)

    `stack_out` entry layout (32 bytes, one per ancestor BRANCH/EXTENSION on the
    root->terminal path, in root->leaf order) -- same as mpt_set_record_walk:
      +0 node_offset : u64   byte offset within the witness section
      +8 node_len    : u64
      +16 kind       : u64   0 = branch, 1 = extension
      +24 nibble     : u64   branch: child index taken; extension: 0

    `meta_out` layout (48 bytes):
      +0  depth           : u64  number of ancestor stack_out entries
      +8  consumed        : u64  path nibbles consumed by ancestors (NOT incl.
                                 the terminal's own divergence)
      +16 case            : u64  0..5 (see file header)
      +24 terminal_offset : u64  byte offset of the terminal node's RLP (0 if
                                 EMPTY_TRIE)
      +32 terminal_len    : u64  full RLP length of the terminal node
      +40 match_len       : u64  case 1/2: shared-prefix nibbles at the terminal;
                                 else 0 -/
def mptInsertWalkFunction : String :=
  "mpt_insert_walk:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a1                   # s0 = witness ptr\n" ++
  "  mv s1, a2                   # s1 = witness_len\n" ++
  "  mv s2, a3                   # s2 = path_nibbles ptr\n" ++
  "  mv s3, a4                   # s3 = path_nibbles_len\n" ++
  "  mv s4, a5                   # s4 = stack_out cursor\n" ++
  "  mv s5, a6                   # s5 = meta_out ptr\n" ++
  "  li s9, 0                    # s9 = depth\n" ++
  "  # Copy root_hash to mw_lookup_hash for the first lookup.\n" ++
  "  la t0, mw_lookup_hash\n" ++
  "  ld t1,  0(a0); sd t1,  0(t0)\n" ++
  "  ld t1,  8(a0); sd t1,  8(t0)\n" ++
  "  ld t1, 16(a0); sd t1, 16(t0)\n" ++
  "  ld t1, 24(a0); sd t1, 24(t0)\n" ++
  "  # EMPTY_TRIE_ROOT? -> case 3 (whole trie is a single new leaf).\n" ++
  "  la t2, iw_empty_trie_root\n" ++
  "  ld t3, 0(t0); ld t4, 0(t2); bne t3, t4, .Liw_lookup_root\n" ++
  "  ld t3, 8(t0); ld t4, 8(t2); bne t3, t4, .Liw_lookup_root\n" ++
  "  ld t3, 16(t0); ld t4, 16(t2); bne t3, t4, .Liw_lookup_root\n" ++
  "  ld t3, 24(t0); ld t4, 24(t2); bne t3, t4, .Liw_lookup_root\n" ++
  "  li t5, 3; j .Liw_empty\n" ++
  ".Liw_lookup_root:\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, mw_lookup_hash\n" ++
  "  la a3, mw_lookup_offset\n" ++
  "  la a4, mw_lookup_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Liw_miss\n" ++
  "  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1\n" ++
  "  la t0, mw_lookup_length; ld s8, 0(t0)\n" ++
  "  li s6, 0\n" ++
  ".Liw_loop:\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  beqz a0, .Liw_branch\n" ++
  "  li t0, 1; beq a0, t0, .Liw_extension\n" ++
  "  li t0, 2; beq a0, t0, .Liw_leaf\n" ++
  "  j .Liw_parse_fail\n" ++
  ".Liw_branch:\n" ++
  "  beq s6, s3, .Liw_branch_value\n" ++
  "  add t0, s2, s6              # &path[consumed]\n" ++
  "  lbu t1, 0(t0)               # nibble (item index)\n" ++
  "  # push record (node_offset, node_len, kind=0 branch, nibble)\n" ++
  "  sub t2, s7, s0              # node_offset within witness\n" ++
  "  sd t2,  0(s4)\n" ++
  "  sd s8,  8(s4)\n" ++
  "  sd zero, 16(s4)            # kind = 0 (branch)\n" ++
  "  sd t1, 24(s4)\n" ++
  "  addi s4, s4, 32\n" ++
  "  addi s9, s9, 1\n" ++
  "  # descend into child slot via rlp_list_nth_item.\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  mv a2, t1                   # nibble\n" ++
  "  la a3, mw_child_offset\n" ++
  "  la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  addi s6, s6, 1\n" ++
  "  bnez a0, .Liw_parse_fail\n" ++
  "  la t0, mw_child_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Liw_branch_empty  # empty slot -> insert point\n" ++
  "  li t2, 32\n" ++
  "  beq t1, t2, .Liw_branch_hash\n" ++
  "  # Inlined (length 1..31): node = (s7 + child_offset, child_length).\n" ++
  "  la t0, mw_child_offset; ld t2, 0(t0)\n" ++
  "  add s7, s7, t2\n" ++
  "  mv s8, t1\n" ++
  "  j .Liw_loop\n" ++
  ".Liw_branch_hash:\n" ++
  "  la t0, mw_child_offset; ld t1, 0(t0)\n" ++
  "  add t2, s7, t1\n" ++
  "  la t3, mw_lookup_hash\n" ++
  "  ld t4,  0(t2); sd t4,  0(t3)\n" ++
  "  ld t4,  8(t2); sd t4,  8(t3)\n" ++
  "  ld t4, 16(t2); sd t4, 16(t3)\n" ++
  "  ld t4, 24(t2); sd t4, 24(t3)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, mw_lookup_hash\n" ++
  "  la a3, mw_lookup_offset\n" ++
  "  la a4, mw_lookup_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Liw_miss\n" ++
  "  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1\n" ++
  "  la t0, mw_lookup_length; ld s8, 0(t0)\n" ++
  "  j .Liw_loop\n" ++
  ".Liw_branch_empty:\n" ++
  "  # The branch (just pushed) is the terminal: un-push it; ancestors = s9-1.\n" ++
  "  addi s4, s4, -32\n" ++
  "  addi s9, s9, -1\n" ++
  "  li t5, 0                    # case 0 BRANCH_EMPTY_SLOT\n" ++
  "  addi s6, s6, -1             # consumed = ancestors' nibbles (drop branch nibble)\n" ++
  "  li t6, 0                    # match_len = 0\n" ++
  "  j .Liw_record\n" ++
  ".Liw_branch_value:\n" ++
  "  # Path exhausted at a branch (value slot 16). Defensive (not for 64-nibble\n" ++
  "  # account paths). The branch is the terminal; it is NOT on the stack.\n" ++
  "  li t5, 5                    # case 5 BRANCH_VALUE\n" ++
  "  li t6, 0\n" ++
  "  j .Liw_record\n" ++
  ".Liw_extension:\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  li a2, 0\n" ++
  "  la a3, mw_path_offset\n" ++
  "  la a4, mw_path_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Liw_parse_fail\n" ++
  "  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1\n" ++
  "  la t0, mw_path_length; ld a1, 0(t0)\n" ++
  "  la a2, mw_nibble_buf\n" ++
  "  la a3, mw_nibble_count\n" ++
  "  la a4, mw_is_leaf\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  bnez a0, .Liw_parse_fail\n" ++
  "  la t0, mw_is_leaf; ld t1, 0(t0)\n" ++
  "  bnez t1, .Liw_parse_fail    # node kind said extension; HP says leaf\n" ++
  "  la t0, mw_nibble_count; ld t1, 0(t0)    # t1 = ext nibble count\n" ++
  "  # common prefix of ext nibbles (mw_nibble_buf) vs path[consumed..].\n" ++
  "  sub t2, s3, s6              # remaining path nibbles\n" ++
  "  mv t3, t1                   # cmp_limit = min(ext_count, remaining)\n" ++
  "  bgeu t2, t1, .Liw_ext_lim_ok\n" ++
  "  mv t3, t2\n" ++
  ".Liw_ext_lim_ok:\n" ++
  "  la t4, mw_nibble_buf\n" ++
  "  add t5, s2, s6              # &path[consumed]\n" ++
  "  li t6, 0                    # match counter\n" ++
  ".Liw_ext_cmp:\n" ++
  "  beq t6, t3, .Liw_ext_cmp_done\n" ++
  "  add a0, t4, t6; lbu a1, 0(a0)\n" ++
  "  add a0, t5, t6; lbu a2, 0(a0)\n" ++
  "  bne a1, a2, .Liw_ext_cmp_done\n" ++
  "  addi t6, t6, 1\n" ++
  "  j .Liw_ext_cmp\n" ++
  ".Liw_ext_cmp_done:\n" ++
  "  # full match iff matched all ext nibbles AND ext fits in remaining path.\n" ++
  "  bne t6, t1, .Liw_ext_split\n" ++
  "  bgtu t1, t2, .Liw_ext_split # ext longer than remaining -> split\n" ++
  "  # full extension match: push it and descend into its child (item 1).\n" ++
  "  sub a0, s7, s0\n" ++
  "  sd a0,  0(s4)\n" ++
  "  sd s8,  8(s4)\n" ++
  "  li a1, 1; sd a1, 16(s4)     # kind = 1 (extension)\n" ++
  "  sd zero, 24(s4)\n" ++
  "  addi s4, s4, 32\n" ++
  "  addi s9, s9, 1\n" ++
  "  add s6, s6, t1              # consume the ext nibbles\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  li a2, 1\n" ++
  "  la a3, mw_child_offset\n" ++
  "  la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Liw_parse_fail\n" ++
  "  la t0, mw_child_length; ld t1, 0(t0)\n" ++
  "  la t0, mw_child_offset; ld t2, 0(t0)\n" ++
  "  add t3, s7, t2\n" ++
  "  li t4, 32\n" ++
  "  beq t1, t4, .Liw_ext_hash\n" ++
  "  mv s7, t3\n" ++
  "  mv s8, t1\n" ++
  "  j .Liw_loop\n" ++
  ".Liw_ext_hash:\n" ++
  "  la t4, mw_lookup_hash\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, mw_lookup_hash\n" ++
  "  la a3, mw_lookup_offset\n" ++
  "  la a4, mw_lookup_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Liw_miss\n" ++
  "  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1\n" ++
  "  la t0, mw_lookup_length; ld s8, 0(t0)\n" ++
  "  j .Liw_loop\n" ++
  ".Liw_ext_split:\n" ++
  "  # t6 = match_len; the extension is the terminal (not pushed).\n" ++
  "  li t5, 2                    # case 2 EXTENSION_SPLIT (t6 already = match_len)\n" ++
  "  j .Liw_record\n" ++
  ".Liw_leaf:\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  li a2, 0\n" ++
  "  la a3, mw_path_offset\n" ++
  "  la a4, mw_path_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Liw_parse_fail\n" ++
  "  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1\n" ++
  "  la t0, mw_path_length; ld a1, 0(t0)\n" ++
  "  la a2, mw_nibble_buf\n" ++
  "  la a3, mw_nibble_count\n" ++
  "  la a4, mw_is_leaf\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  bnez a0, .Liw_parse_fail\n" ++
  "  la t0, mw_is_leaf; ld t1, 0(t0)\n" ++
  "  li t2, 1\n" ++
  "  bne t1, t2, .Liw_parse_fail # node kind said leaf; HP says extension\n" ++
  "  la t0, mw_nibble_count; ld t1, 0(t0)    # t1 = leaf key nibble count\n" ++
  "  sub t2, s3, s6              # remaining path nibbles\n" ++
  "  mv t3, t1                   # cmp_limit = min(leaf_count, remaining)\n" ++
  "  bgeu t2, t1, .Liw_leaf_lim_ok\n" ++
  "  mv t3, t2\n" ++
  ".Liw_leaf_lim_ok:\n" ++
  "  la t4, mw_nibble_buf\n" ++
  "  add t5, s2, s6              # &path[consumed]\n" ++
  "  li t6, 0                    # match counter\n" ++
  ".Liw_leaf_cmp:\n" ++
  "  beq t6, t3, .Liw_leaf_cmp_done\n" ++
  "  add a0, t4, t6; lbu a1, 0(a0)\n" ++
  "  add a0, t5, t6; lbu a2, 0(a0)\n" ++
  "  bne a1, a2, .Liw_leaf_cmp_done\n" ++
  "  addi t6, t6, 1\n" ++
  "  j .Liw_leaf_cmp\n" ++
  ".Liw_leaf_cmp_done:\n" ++
  "  # EXISTS iff matched all leaf nibbles AND leaf key length == remaining.\n" ++
  "  bne t6, t1, .Liw_leaf_split\n" ++
  "  bne t1, t2, .Liw_leaf_split\n" ++
  "  li t5, 4                    # case 4 EXISTS (t6 already = match_len)\n" ++
  "  j .Liw_record\n" ++
  ".Liw_leaf_split:\n" ++
  "  li t5, 1                    # case 1 LEAF_SPLIT (t6 already = match_len)\n" ++
  "  j .Liw_record\n" ++
  ".Liw_record:\n" ++
  "  # t5 = case, t6 = match_len; terminal = (s7,s8); ancestors depth = s9.\n" ++
  "  sd s9, 0(s5)               # depth\n" ++
  "  sd s6, 8(s5)               # consumed\n" ++
  "  sd t5, 16(s5)              # case\n" ++
  "  sub t0, s7, s0; sd t0, 24(s5)  # terminal_offset\n" ++
  "  sd s8, 32(s5)              # terminal_len\n" ++
  "  sd t6, 40(s5)              # match_len\n" ++
  "  li a0, 0\n" ++
  "  j .Liw_ret\n" ++
  ".Liw_empty:\n" ++
  "  # case 3 EMPTY_TRIE: no ancestors, no terminal node.\n" ++
  "  sd zero, 0(s5)             # depth = 0\n" ++
  "  sd zero, 8(s5)             # consumed = 0\n" ++
  "  sd t5, 16(s5)              # case = 3\n" ++
  "  sd zero, 24(s5)            # terminal_offset = 0\n" ++
  "  sd zero, 32(s5)            # terminal_len = 0\n" ++
  "  sd zero, 40(s5)            # match_len = 0\n" ++
  "  li a0, 0\n" ++
  "  j .Liw_ret\n" ++
  ".Liw_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Liw_ret\n" ++
  ".Liw_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Liw_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-! ## iw_empty_trie_root data + probe data section.
    EMPTY_TRIE_ROOT = keccak256(rlp(b'')) =
      0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421 -/
def iwEmptyTrieRootData : String :=
  "iw_empty_trie_root:\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21"

/-- `zisk_mpt_insert_walk`: probe BuildUnit. Reuses the mpt_set probe input
    layout (scripts/mpt_ref.py `build_probe_input`); the new_value field is
    present but ignored by the walk.
    Input layout (file maps to INPUT+8 at 0x40000000):
      INPUT+8  : witness_len (u64)
      INPUT+16 : path_len (u64)
      INPUT+24 : new_value_len (u64)         [ignored]
      INPUT+32 : root_hash (32 bytes)
      INPUT+64 : path_nibbles (1B each)
      INPUT+64+path_len : new_value
      8-aligned : witness section
    Output layout:
      OUTPUT+0   : status (0 ok / 1 miss / 2 fail)
      OUTPUT+8   : meta (depth, consumed, case, terminal_offset, terminal_len,
                   match_len) -- 48 B
      OUTPUT+128 : ancestor stack records, 32 B each -/
def ziskMptInsertWalkPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # path_len\n" ++
  "  ld t4, 24(a7)               # new_value_len\n" ++
  "  addi a0, a7, 32             # root_hash ptr (INPUT+32)\n" ++
  "  addi a3, a7, 64             # path_nibbles ptr (INPUT+64)\n" ++
  "  # witness ptr = path_ptr + roundup8(path_len + new_value_len).\n" ++
  "  add t3, t5, t4\n" ++
  "  addi t3, t3, 7\n" ++
  "  andi t3, t3, -8\n" ++
  "  add a1, a3, t3              # witness ptr\n" ++
  "  mv a2, t6                   # witness_len\n" ++
  "  mv a4, t5                   # path_len\n" ++
  "  li a5, 0xa0010080           # stack_out at OUTPUT + 128\n" ++
  "  li a6, 0xa0010008           # meta_out at OUTPUT + 8\n" ++
  "  jal ra, mpt_insert_walk\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Liw_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptInsertWalkFunction ++ "\n" ++
  ".Liw_pdone:"

def ziskMptInsertWalkDataSection : String :=
  ziskMptWalkDataSection ++ "\n" ++
  ".balign 8\n" ++
  iwEmptyTrieRootData

def ziskMptInsertWalkProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptInsertWalkPrologue
  dataAsm     := ziskMptInsertWalkDataSection
}

end EvmAsm.Codegen
