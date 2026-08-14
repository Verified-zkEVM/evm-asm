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
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
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
def singleLeafTrieRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
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
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.sltr_nibbles (GuestAddrs.single_leaf_trie_root + 60)),
    .ADDI .x12 .x12 (laLo GuestAddrs.sltr_nibbles (GuestAddrs.single_leaf_trie_root + 60)),
    .JAL .x1 (jalOff GuestAddrs.bytes_to_nibbles (GuestAddrs.single_leaf_trie_root + 68)),
    .AUIPC .x5 (laHi GuestAddrs.sltr_nibble_count (GuestAddrs.single_leaf_trie_root + 72)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sltr_nibble_count (GuestAddrs.single_leaf_trie_root + 72)),
    .SD .x5 .x10 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.sltr_nibbles (GuestAddrs.single_leaf_trie_root + 84)),
    .ADDI .x10 .x10 (laLo GuestAddrs.sltr_nibbles (GuestAddrs.single_leaf_trie_root + 84)),
    .AUIPC .x5 (laHi GuestAddrs.sltr_nibble_count (GuestAddrs.single_leaf_trie_root + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sltr_nibble_count (GuestAddrs.single_leaf_trie_root + 92)),
    .LD .x11 .x5 (0 : BitVec 12),
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.sltr_hp_buf (GuestAddrs.single_leaf_trie_root + 108)),
    .ADDI .x13 .x13 (laLo GuestAddrs.sltr_hp_buf (GuestAddrs.single_leaf_trie_root + 108)),
    .JAL .x1 (jalOff GuestAddrs.hp_encode_nibbles (GuestAddrs.single_leaf_trie_root + 116)),
    .AUIPC .x5 (laHi GuestAddrs.sltr_hp_len (GuestAddrs.single_leaf_trie_root + 120)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sltr_hp_len (GuestAddrs.single_leaf_trie_root + 120)),
    .SD .x5 .x10 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.sltr_hp_buf (GuestAddrs.single_leaf_trie_root + 132)),
    .ADDI .x10 .x10 (laLo GuestAddrs.sltr_hp_buf (GuestAddrs.single_leaf_trie_root + 132)),
    .AUIPC .x5 (laHi GuestAddrs.sltr_hp_len (GuestAddrs.single_leaf_trie_root + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sltr_hp_len (GuestAddrs.single_leaf_trie_root + 140)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.sltr_payload_buf (GuestAddrs.single_leaf_trie_root + 152)),
    .ADDI .x12 .x12 (laLo GuestAddrs.sltr_payload_buf (GuestAddrs.single_leaf_trie_root + 152)),
    .AUIPC .x13 (laHi GuestAddrs.sltr_field_len (GuestAddrs.single_leaf_trie_root + 160)),
    .ADDI .x13 .x13 (laLo GuestAddrs.sltr_field_len (GuestAddrs.single_leaf_trie_root + 160)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.single_leaf_trie_root + 168)),
    .AUIPC .x5 (laHi GuestAddrs.sltr_field_len (GuestAddrs.single_leaf_trie_root + 172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sltr_field_len (GuestAddrs.single_leaf_trie_root + 172)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sltr_cursor (GuestAddrs.single_leaf_trie_root + 184)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sltr_cursor (GuestAddrs.single_leaf_trie_root + 184)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sltr_cursor (GuestAddrs.single_leaf_trie_root + 196)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sltr_cursor (GuestAddrs.single_leaf_trie_root + 196)),
    .LD .x6 .x5 (0 : BitVec 12),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .AUIPC .x12 (laHi GuestAddrs.sltr_payload_buf (GuestAddrs.single_leaf_trie_root + 216)),
    .ADDI .x12 .x12 (laLo GuestAddrs.sltr_payload_buf (GuestAddrs.single_leaf_trie_root + 216)),
    .ADD .x12 .x12 .x6,
    .AUIPC .x13 (laHi GuestAddrs.sltr_field_len (GuestAddrs.single_leaf_trie_root + 228)),
    .ADDI .x13 .x13 (laLo GuestAddrs.sltr_field_len (GuestAddrs.single_leaf_trie_root + 228)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.single_leaf_trie_root + 236)),
    .AUIPC .x5 (laHi GuestAddrs.sltr_field_len (GuestAddrs.single_leaf_trie_root + 240)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sltr_field_len (GuestAddrs.single_leaf_trie_root + 240)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sltr_cursor (GuestAddrs.single_leaf_trie_root + 252)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sltr_cursor (GuestAddrs.single_leaf_trie_root + 252)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x7 .x7 .x6,
    .AUIPC .x5 (laHi GuestAddrs.sltr_total_payload (GuestAddrs.single_leaf_trie_root + 268)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sltr_total_payload (GuestAddrs.single_leaf_trie_root + 268)),
    .SD .x5 .x7 (0 : BitVec 12),
    .MV .x10 .x7,
    .AUIPC .x11 (laHi GuestAddrs.sltr_node_buf (GuestAddrs.single_leaf_trie_root + 284)),
    .ADDI .x11 .x11 (laLo GuestAddrs.sltr_node_buf (GuestAddrs.single_leaf_trie_root + 284)),
    .AUIPC .x12 (laHi GuestAddrs.sltr_field_len (GuestAddrs.single_leaf_trie_root + 292)),
    .ADDI .x12 .x12 (laLo GuestAddrs.sltr_field_len (GuestAddrs.single_leaf_trie_root + 292)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.single_leaf_trie_root + 300)),
    .AUIPC .x5 (laHi GuestAddrs.sltr_field_len (GuestAddrs.single_leaf_trie_root + 304)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sltr_field_len (GuestAddrs.single_leaf_trie_root + 304)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sltr_total_payload (GuestAddrs.single_leaf_trie_root + 316)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sltr_total_payload (GuestAddrs.single_leaf_trie_root + 316)),
    .LD .x7 .x5 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.sltr_node_buf (GuestAddrs.single_leaf_trie_root + 328)),
    .ADDI .x28 .x28 (laLo GuestAddrs.sltr_node_buf (GuestAddrs.single_leaf_trie_root + 328)),
    .ADD .x28 .x28 .x6,
    .AUIPC .x29 (laHi GuestAddrs.sltr_payload_buf (GuestAddrs.single_leaf_trie_root + 340)),
    .ADDI .x29 .x29 (laLo GuestAddrs.sltr_payload_buf (GuestAddrs.single_leaf_trie_root + 340)),
    .MV .x30 .x7,
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x29 (0 : BitVec 12),
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x6 .x6 .x7,
    .AUIPC .x10 (laHi GuestAddrs.sltr_node_buf (GuestAddrs.single_leaf_trie_root + 384)),
    .ADDI .x10 .x10 (laLo GuestAddrs.sltr_node_buf (GuestAddrs.single_leaf_trie_root + 384)),
    .MV .x11 .x6,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.single_leaf_trie_root + 400)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `singleLeafTrieRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def singleLeafTrieRoot_relocs : RelocTable :=
  [ (15, .la .x12 "sltr_nibbles"),
    (17, .jal .x1 "bytes_to_nibbles"),
    (18, .la .x5 "sltr_nibble_count"),
    (21, .la .x10 "sltr_nibbles"),
    (23, .la .x5 "sltr_nibble_count"),
    (27, .la .x13 "sltr_hp_buf"),
    (29, .jal .x1 "hp_encode_nibbles"),
    (30, .la .x5 "sltr_hp_len"),
    (33, .la .x10 "sltr_hp_buf"),
    (35, .la .x5 "sltr_hp_len"),
    (38, .la .x12 "sltr_payload_buf"),
    (40, .la .x13 "sltr_field_len"),
    (42, .jal .x1 "rlp_encode_bytes"),
    (43, .la .x5 "sltr_field_len"),
    (46, .la .x5 "sltr_cursor"),
    (49, .la .x5 "sltr_cursor"),
    (54, .la .x12 "sltr_payload_buf"),
    (57, .la .x13 "sltr_field_len"),
    (59, .jal .x1 "rlp_encode_bytes"),
    (60, .la .x5 "sltr_field_len"),
    (63, .la .x5 "sltr_cursor"),
    (67, .la .x5 "sltr_total_payload"),
    (71, .la .x11 "sltr_node_buf"),
    (73, .la .x12 "sltr_field_len"),
    (75, .jal .x1 "rlp_encode_list_prefix"),
    (76, .la .x5 "sltr_field_len"),
    (79, .la .x5 "sltr_total_payload"),
    (82, .la .x28 "sltr_node_buf"),
    (85, .la .x29 "sltr_payload_buf"),
    (96, .la .x10 "sltr_node_buf"),
    (100, .jal .x1 "zkvm_keccak256") ]

def singleLeafTrieRootFunction : String :=
  "single_leaf_trie_root:\n" ++ emitProgramR singleLeafTrieRoot_prog singleLeafTrieRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `singleLeafTrieRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem singleLeafTrieRootFunction_eq_prog :
    singleLeafTrieRootFunction = "single_leaf_trie_root:\n" ++ emitProgramR singleLeafTrieRoot_prog singleLeafTrieRoot_relocs := rfl

#guard singleLeafTrieRootFunction.startsWith "single_leaf_trie_root:\n"
#guard singleLeafTrieRoot_prog.length = 111
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
      a0 (output) : 0 on success, 1 on invalid output pointer. -/
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
  "  li t0, 0xa0000000\n" ++
  "  bltu s4, t0, .Lmlne_fail\n" ++
  "  bltu s5, t0, .Lmlne_fail\n" ++
  "  li t0, 0xc0000000\n" ++
  "  bgeu s4, t0, .Lmlne_fail\n" ++
  "  li t0, 0xbffffff8\n" ++
  "  bgtu s5, t0, .Lmlne_fail\n" ++
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
  "  add t6, s4, t1\n" ++
  "  bltu t6, s4, .Lmlne_fail\n" ++
  "  add t6, t6, t2\n" ++
  "  bltu t6, s4, .Lmlne_fail\n" ++
  "  li t0, 0xc0000000\n" ++
  "  bgtu t6, t0, .Lmlne_fail\n" ++
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
  "  ret\n" ++
  ".Lmlne_fail:\n" ++
  "  li a0, 1\n" ++
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
def mptNodeSlotEncode_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x12,
    .MV .x9 .x13,
    .LI .x5 (32 : Word),
    .BLTU .x11 .x5 (40 : BitVec 13),
    .LI .x6 (160 : Word),
    .SB .x8 .x6 (0 : BitVec 12),
    .MV .x18 .x10,
    .ADDI .x12 .x8 (1 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.mpt_node_slot_encode + 52)),
    .LI .x5 (33 : Word),
    .SD .x9 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (52 : BitVec 21),
    .MV .x5 .x10,
    .MV .x6 .x8,
    .MV .x7 .x11,
    .BEQ .x7 .x0 (28 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .SD .x9 .x11 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptNodeSlotEncode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptNodeSlotEncode_relocs : RelocTable :=
  [ (13, .jal .x1 "zkvm_keccak256") ]

def mptNodeSlotEncodeFunction : String :=
  "mpt_node_slot_encode:\n" ++ emitProgramR mptNodeSlotEncode_prog mptNodeSlotEncode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptNodeSlotEncode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptNodeSlotEncodeFunction_eq_prog :
    mptNodeSlotEncodeFunction = "mpt_node_slot_encode:\n" ++ emitProgramR mptNodeSlotEncode_prog mptNodeSlotEncode_relocs := rfl

#guard mptNodeSlotEncodeFunction.startsWith "mpt_node_slot_encode:\n"
#guard mptNodeSlotEncode_prog.length = 36
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
      a0 (output) : 0 on success, 1 on invalid output pointer. -/
def mptExtensionNodeEncode_prog : Program :=
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
    .BLTU .x20 .x5 (388 : BitVec 13),
    .BLTU .x21 .x5 (384 : BitVec 13),
    .ADDIW .x5 .x0 (3 : BitVec 12),
    .SLLI .x5 .x5 (30 : BitVec 6),
    .BGEU .x20 .x5 (372 : BitVec 13),
    .ADDIW .x5 .x0 (3 : BitVec 12),
    .SLLI .x5 .x5 (30 : BitVec 6),
    .ADDI .x5 .x5 (-8 : BitVec 12),
    .BLTU .x5 .x21 (356 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mxne_hp_buf (GuestAddrs.mpt_extension_node_encode + 112)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mxne_hp_buf (GuestAddrs.mpt_extension_node_encode + 112)),
    .JAL .x1 (jalOff GuestAddrs.hp_encode_nibbles (GuestAddrs.mpt_extension_node_encode + 120)),
    .AUIPC .x5 (laHi GuestAddrs.mxne_hp_len (GuestAddrs.mpt_extension_node_encode + 124)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mxne_hp_len (GuestAddrs.mpt_extension_node_encode + 124)),
    .SD .x5 .x10 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.mxne_hp_buf (GuestAddrs.mpt_extension_node_encode + 136)),
    .ADDI .x10 .x10 (laLo GuestAddrs.mxne_hp_buf (GuestAddrs.mpt_extension_node_encode + 136)),
    .AUIPC .x5 (laHi GuestAddrs.mxne_hp_len (GuestAddrs.mpt_extension_node_encode + 144)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mxne_hp_len (GuestAddrs.mpt_extension_node_encode + 144)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.mxne_payload_buf (GuestAddrs.mpt_extension_node_encode + 156)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mxne_payload_buf (GuestAddrs.mpt_extension_node_encode + 156)),
    .AUIPC .x13 (laHi GuestAddrs.mxne_field_len (GuestAddrs.mpt_extension_node_encode + 164)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mxne_field_len (GuestAddrs.mpt_extension_node_encode + 164)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.mpt_extension_node_encode + 172)),
    .AUIPC .x5 (laHi GuestAddrs.mxne_field_len (GuestAddrs.mpt_extension_node_encode + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mxne_field_len (GuestAddrs.mpt_extension_node_encode + 176)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mxne_cursor (GuestAddrs.mpt_extension_node_encode + 188)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mxne_cursor (GuestAddrs.mpt_extension_node_encode + 188)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mxne_cursor (GuestAddrs.mpt_extension_node_encode + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mxne_cursor (GuestAddrs.mpt_extension_node_encode + 200)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.mxne_payload_buf (GuestAddrs.mpt_extension_node_encode + 212)),
    .ADDI .x7 .x7 (laLo GuestAddrs.mxne_payload_buf (GuestAddrs.mpt_extension_node_encode + 212)),
    .ADD .x7 .x7 .x6,
    .MV .x28 .x18,
    .MV .x29 .x19,
    .BEQ .x29 .x0 (28 : BitVec 13),
    .LBU .x30 .x28 (0 : BitVec 12),
    .SB .x7 .x30 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.mxne_cursor (GuestAddrs.mpt_extension_node_encode + 260)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mxne_cursor (GuestAddrs.mpt_extension_node_encode + 260)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x6 .x19,
    .AUIPC .x5 (laHi GuestAddrs.mxne_total_payload (GuestAddrs.mpt_extension_node_encode + 276)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mxne_total_payload (GuestAddrs.mpt_extension_node_encode + 276)),
    .SD .x5 .x7 (0 : BitVec 12),
    .MV .x10 .x7,
    .MV .x11 .x20,
    .AUIPC .x12 (laHi GuestAddrs.mxne_field_len (GuestAddrs.mpt_extension_node_encode + 296)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mxne_field_len (GuestAddrs.mpt_extension_node_encode + 296)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.mpt_extension_node_encode + 304)),
    .AUIPC .x5 (laHi GuestAddrs.mxne_field_len (GuestAddrs.mpt_extension_node_encode + 308)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mxne_field_len (GuestAddrs.mpt_extension_node_encode + 308)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mxne_total_payload (GuestAddrs.mpt_extension_node_encode + 320)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mxne_total_payload (GuestAddrs.mpt_extension_node_encode + 320)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x31 .x20 .x6,
    .BLTU .x31 .x20 (116 : BitVec 13),
    .ADD .x31 .x31 .x7,
    .BLTU .x31 .x20 (108 : BitVec 13),
    .ADDIW .x5 .x0 (3 : BitVec 12),
    .SLLI .x5 .x5 (30 : BitVec 6),
    .BLTU .x5 .x31 (96 : BitVec 13),
    .ADD .x28 .x20 .x6,
    .AUIPC .x29 (laHi GuestAddrs.mxne_payload_buf (GuestAddrs.mpt_extension_node_encode + 364)),
    .ADDI .x29 .x29 (laLo GuestAddrs.mxne_payload_buf (GuestAddrs.mpt_extension_node_encode + 364)),
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

/-- Reloc side-table for `mptExtensionNodeEncode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptExtensionNodeEncode_relocs : RelocTable :=
  [ (28, .la .x13 "mxne_hp_buf"),
    (30, .jal .x1 "hp_encode_nibbles"),
    (31, .la .x5 "mxne_hp_len"),
    (34, .la .x10 "mxne_hp_buf"),
    (36, .la .x5 "mxne_hp_len"),
    (39, .la .x12 "mxne_payload_buf"),
    (41, .la .x13 "mxne_field_len"),
    (43, .jal .x1 "rlp_encode_bytes"),
    (44, .la .x5 "mxne_field_len"),
    (47, .la .x5 "mxne_cursor"),
    (50, .la .x5 "mxne_cursor"),
    (53, .la .x7 "mxne_payload_buf"),
    (65, .la .x5 "mxne_cursor"),
    (69, .la .x5 "mxne_total_payload"),
    (74, .la .x12 "mxne_field_len"),
    (76, .jal .x1 "rlp_encode_list_prefix"),
    (77, .la .x5 "mxne_field_len"),
    (80, .la .x5 "mxne_total_payload"),
    (91, .la .x29 "mxne_payload_buf") ]

def mptExtensionNodeEncodeFunction : String :=
  "mpt_extension_node_encode:\n" ++ emitProgramR mptExtensionNodeEncode_prog mptExtensionNodeEncode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptExtensionNodeEncode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptExtensionNodeEncodeFunction_eq_prog :
    mptExtensionNodeEncodeFunction = "mpt_extension_node_encode:\n" ++ emitProgramR mptExtensionNodeEncode_prog mptExtensionNodeEncode_relocs := rfl

#guard mptExtensionNodeEncodeFunction.startsWith "mpt_extension_node_encode:\n"
#guard mptExtensionNodeEncode_prog.length = 123
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
      a0 (output) : 0 on success, 1 on invalid output pointer. -/
def mptBranchNodeEncodeFunction : String :=
  "mpt_branch_node_encode:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # slot_payload ptr\n" ++
  "  mv s1, a1                   # slot_payload len\n" ++
  "  mv s2, a2                   # output ptr\n" ++
  "  mv s3, a3                   # out_length ptr\n" ++
  "  li t0, 0xa0000000\n" ++
  "  bltu s2, t0, .Lmbne_fail\n" ++
  "  bltu s3, t0, .Lmbne_fail\n" ++
  "  li t0, 0xc0000000\n" ++
  "  bgeu s2, t0, .Lmbne_fail\n" ++
  "  li t0, 0xbffffff8\n" ++
  "  bgtu s3, t0, .Lmbne_fail\n" ++
  "  # ---- Write outer list prefix at output[0..] ----\n" ++
  "  mv a0, s1; mv a1, s2\n" ++
  "  la a2, mbne_field_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, mbne_field_len; ld t1, 0(t0)         # prefix_len\n" ++
  "  add t6, s2, t1\n" ++
  "  bltu t6, s2, .Lmbne_fail\n" ++
  "  add t6, t6, s1\n" ++
  "  bltu t6, s2, .Lmbne_fail\n" ++
  "  li t0, 0xc0000000\n" ++
  "  bgtu t6, t0, .Lmbne_fail\n" ++
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
  "  ret\n" ++
  ".Lmbne_fail:\n" ++
  "  li a0, 1\n" ++
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
def nibblesCommonPrefixLen_prog : Program :=
  [ .BLTU .x11 .x13 (8 : BitVec 13),
    .MV .x11 .x13,
    .LI .x5 (0 : Word),
    .MV .x6 .x10,
    .MV .x7 .x12,
    .BGE .x5 .x11 (32 : BitVec 13),
    .LBU .x28 .x6 (0 : BitVec 12),
    .LBU .x29 .x7 (0 : BitVec 12),
    .BNE .x28 .x29 (20 : BitVec 13),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .SD .x14 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def nibblesCommonPrefixLenFunction : String :=
  "nibbles_common_prefix_len:\n" ++ emitProgram nibblesCommonPrefixLen_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `nibblesCommonPrefixLen_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem nibblesCommonPrefixLenFunction_eq_prog :
    nibblesCommonPrefixLenFunction = "nibbles_common_prefix_len:\n" ++ emitProgram nibblesCommonPrefixLen_prog := rfl

#guard nibblesCommonPrefixLenFunction.startsWith "nibbles_common_prefix_len:\n"
#guard nibblesCommonPrefixLen_prog.length = 16
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
def mptBranchPayloadTwoSlots_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
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
    .LI .x5 (17 : Word),
    .BGEU .x8 .x5 (148 : BitVec 13),
    .BGEU .x19 .x5 (144 : BitVec 13),
    .BEQ .x8 .x19 (140 : BitVec 13),
    .MV .x6 .x16,
    .LI .x7 (0 : Word),
    .LI .x5 (17 : Word),
    .BGE .x7 .x5 (108 : BitVec 13),
    .BEQ .x7 .x8 (24 : BitVec 13),
    .BEQ .x7 .x19 (56 : BitVec 13),
    .LI .x28 (128 : Word),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (76 : BitVec 21),
    .MV .x28 .x9,
    .MV .x29 .x18,
    .BEQ .x29 .x0 (64 : BitVec 13),
    .LBU .x30 .x28 (0 : BitVec 12),
    .SB .x6 .x30 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .MV .x28 .x20,
    .MV .x29 .x21,
    .BEQ .x29 .x0 (28 : BitVec 13),
    .LBU .x30 .x28 (0 : BitVec 12),
    .SB .x6 .x30 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-108 : BitVec 21),
    .SUB .x6 .x6 .x16,
    .SD .x17 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (12 : BitVec 21),
    .SD .x17 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def mptBranchPayloadTwoSlotsFunction : String :=
  "mpt_branch_payload_two_slots:\n" ++ emitProgram mptBranchPayloadTwoSlots_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `mptBranchPayloadTwoSlots_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem mptBranchPayloadTwoSlotsFunction_eq_prog :
    mptBranchPayloadTwoSlotsFunction = "mpt_branch_payload_two_slots:\n" ++ emitProgram mptBranchPayloadTwoSlots_prog := rfl

#guard mptBranchPayloadTwoSlotsFunction.startsWith "mpt_branch_payload_two_slots:\n"
#guard mptBranchPayloadTwoSlots_prog.length = 63
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


end EvmAsm.Codegen
