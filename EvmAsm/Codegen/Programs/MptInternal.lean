/-
  EvmAsm.Codegen.Programs.MptInternal

  Per-node MPT primitives carved out of
  `EvmAsm.Codegen.Programs.Mpt` per the file-size hard cap. Hosts:

    K109  mpt_nibbles_to_compact
    K110  mpt_compact_to_nibbles
    K111  mpt_node_classify
    K112  mpt_encode_internal_node
    K113  mpt_leaf_extract
    K114  mpt_extension_extract
    K115  mpt_branch_get_child
    K116  mpt_branch_get_value
    K117  mpt_branch_used_count
    K118  mpt_branch_first_used_index

  All operate on a single (already-decoded) MPT node — leaf,
  extension, or branch — distinct from the walk-level primitives
  (K21..K26 + K100) that traverse the trie. Depend on
  RlpRead, RlpWalk, and HashBridge.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## mpt_node_classify -- PR-K111

    Classify an MPT node from its RLP-encoded bytes.

    An MPT node is one of three shapes:
    - 17-item list → **branch** (16 children + value)
    - 2-item list with leaf-flagged compact path → **leaf**
    - 2-item list with extension-flagged compact path → **extension**

    PR-K23/K24 already walk MPT trees; this primitive lets callers
    introspect a single node's kind cheaply without a full decode,
    so dispatch tables (`branch_get_child` vs `leaf_decode` vs
    `extension_skip`) can pick the right path.

    Composes:
      - PR-K47 `rlp_list_count_items` — top-level item count
      - PR-K20 `rlp_list_nth_item`    — field 0 bounds (for 2-item)

    The MPT compact-encoded path's first byte high nibble carries
    `(is_leaf, parity)` flags (see PR-K109/K110): bit 1 → is_leaf.

    Calling convention:
      a0 (input)  : node_rlp ptr
      a1 (input)  : node_rlp byte length
      a2 (input)  : u64 out ptr (kind)
      ra (input)  : return
      a0 (output) :
        0 : success — kind in {0,1,2}
        1 : invalid (not a 2- or 17-item list, or path missing)

    Kind encoding:
      0 : branch (17 items)
      1 : extension (2 items, compact prefix indicates not-leaf)
      2 : leaf (2 items, compact prefix indicates leaf) -/
def mptNodeClassifyFunction : String :=
  "mpt_node_classify:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # node ptr\n" ++
  "  mv s1, a1                   # node len\n" ++
  "  mv s2, a2                   # kind out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Count items.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mnodc_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lmnodc_fail\n" ++
  "  la t0, mnodc_count; ld t1, 0(t0)\n" ++
  "  li t2, 17\n" ++
  "  beq t1, t2, .Lmnodc_branch\n" ++
  "  li t2, 2\n" ++
  "  bne t1, t2, .Lmnodc_fail\n" ++
  "  # 2-item: read first byte of compact-encoded path.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, mnodc_path_off; la a4, mnodc_path_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmnodc_fail\n" ++
  "  la t0, mnodc_path_len; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmnodc_fail\n" ++
  "  la t0, mnodc_path_off; ld t2, 0(t0)\n" ++
  "  add t3, s0, t2\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  srli t5, t4, 5\n" ++
  "  andi t5, t5, 1\n" ++
  "  addi t5, t5, 1              # 1 = ext, 2 = leaf\n" ++
  "  sd t5, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmnodc_ret\n" ++
  ".Lmnodc_branch:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmnodc_ret\n" ++
  ".Lmnodc_fail:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 1\n" ++
  ".Lmnodc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_mpt_node_classify`: probe BuildUnit. Reads
    (node_len, node_bytes) from host input, writes (status, kind)
    to OUTPUT (16 bytes total). -/
def ziskMptNodeClassifyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # node_len\n" ++
  "  addi a0, a3, 16             # node ptr\n" ++
  "  li a2, 0xa0010008           # kind out\n" ++
  "  jal ra, mpt_node_classify\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmnodc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  mptNodeClassifyFunction ++ "\n" ++
  ".Lmnodc_pdone:"

def ziskMptNodeClassifyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mnodc_count:\n" ++
  "  .zero 8\n" ++
  "mnodc_path_off:\n" ++
  "  .zero 8\n" ++
  "mnodc_path_len:\n" ++
  "  .zero 8"


/-! ## mpt_encode_internal_node -- PR-K112

    Compute the canonical MPT "node reference" used by parent
    nodes to point at this node. Matches
    `encode_internal_node(node)` in `forks/amsterdam/trie.py`:

      encoded = rlp.encode(node)
      if len(encoded) < 32:
          return encoded            # embedded RLP (in-place ref)
      else:
          return keccak256(encoded) # 32-byte hash ref

    Callers pass in the already-RLP-encoded node bytes. The helper
    returns either the same bytes verbatim (when short enough to
    embed) or their keccak256 digest (when ≥ 32 bytes).

    Used by:
    - MPT walk when descending into a branch's child: the slot's
      stored bytes are this encoding, and the walker decides
      whether to dereference via the node DB hash table or to
      recurse on the embedded RLP directly.
    - MPT root recomputation, which propagates this encoding up
      the tree.

    Composes PR-K3 `zkvm_keccak256`. Uses 200 bytes of `.data`
    scratch (`zk3_state`, the keccak sponge state).

    Calling convention:
      a0 (input)  : node_rlp ptr
      a1 (input)  : node_rlp byte length
      a2 (input)  : output bytes ptr (caller supplies max(32, len) B)
      a3 (input)  : u64 out ptr (output length: 32 hashed, len embedded)
      a4 (input)  : u64 out ptr (is_hashed flag: 1 hashed, 0 embedded)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function). -/
/-! Probe-only local PC placeholder. -/
def mptEncodeInternalNodePc : Nat := 0x80000000

def mptEncodeInternalNode_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x12,
    .MV .x9 .x13,
    .MV .x18 .x14,
    .LI .x5 (32 : Word),
    .BLTU .x11 .x5 (36 : BitVec 13),
    .MV .x12 .x8,
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (mptEncodeInternalNodePc + 44)),
    .LI .x5 (32 : Word),
    .SD .x9 .x5 (0 : BitVec 12),
    .LI .x5 (1 : Word),
    .SD .x18 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (56 : BitVec 21),
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
    .SD .x18 .x0 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptEncodeInternalNode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptEncodeInternalNode_relocs : RelocTable :=
  [ (11, .jal .x1 "zkvm_keccak256") ]

def mptEncodeInternalNodeFunction : String :=
  "mpt_encode_internal_node:\n" ++ emitProgramR mptEncodeInternalNode_prog mptEncodeInternalNode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptEncodeInternalNode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptEncodeInternalNodeFunction_eq_prog :
    mptEncodeInternalNodeFunction = "mpt_encode_internal_node:\n" ++ emitProgramR mptEncodeInternalNode_prog mptEncodeInternalNode_relocs := rfl

#guard mptEncodeInternalNodeFunction.startsWith "mpt_encode_internal_node:\n"
/-- `zisk_mpt_encode_internal_node`: probe BuildUnit. Reads
    (node_len, node_bytes), writes (status, output_len, is_hashed,
    output_bytes...) to OUTPUT.
    Input layout:
      bytes  0.. 8 : node byte length
      bytes  8..   : node RLP bytes
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : output_len
      bytes 16..24 : is_hashed flag
      bytes 24..   : output bytes (32 if hashed, node_len if embedded) -/
def ziskMptEncodeInternalNodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # node length\n" ++
  "  addi a0, a5, 16             # node ptr\n" ++
  "  li a2, 0xa0010018           # output bytes\n" ++
  "  li a3, 0xa0010008           # output_len out\n" ++
  "  li a4, 0xa0010010           # is_hashed out\n" ++
  "  jal ra, mpt_encode_internal_node\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmein_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptEncodeInternalNodeFunction ++ "\n" ++
  ".Lmein_pdone:"

def ziskMptEncodeInternalNodeDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"


/-! ## mpt_branch_get_child -- PR-K115

    Extract the i-th child reference of an MPT branch node.

    A branch node is a 17-item RLP list: `[c0, c1, …, c15, value]`.
    Each child slot `ci` (i in 0..15) holds the i-th child's node
    reference — either a 32-byte keccak digest or an embedded RLP
    blob (see PR-K112 `encode_internal_node`). An empty child slot
    is encoded as the empty RLP string (length 0).

    Pairs with PR-K113 `mpt_leaf_extract` and PR-K114
    `mpt_extension_extract` to cover the three MPT node shapes
    (leaf / extension / branch). Used by the MPT walker
    (PR-K24 `mpt_walk`) every time it descends through a branch
    along the path's current nibble.

    Composes:
      - PR-K47 `rlp_list_count_items` — sanity-check 17 items
      - PR-K20 `rlp_list_nth_item`    — i-th field bounds

    Calling convention:
      a0 (input)  : branch_rlp ptr
      a1 (input)  : branch_rlp byte length
      a2 (input)  : nibble index (0..15)
      a3 (input)  : u64 out ptr (child_ptr — absolute)
      a4 (input)  : u64 out ptr (child_len)
      ra (input)  : return
      a0 (output) :
        0 : success — child slot extracted (may be empty / 32 B / embedded)
        1 : not a 17-item list (or RLP parse failure)
        2 : invalid index (> 15)
        3 : i-th field extraction failed (mid-list parse error)

    Uses two 8-byte `.data` scratch slots
    (`mbc_count`, `mbc_off` + `mbc_len`). -/
def mptBranchGetChildFunction : String :=
  "mpt_branch_get_child:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # branch ptr\n" ++
  "  mv s1, a1                   # branch len\n" ++
  "  mv s2, a2                   # index\n" ++
  "  mv s3, a3                   # child_ptr out\n" ++
  "  mv s4, a4                   # child_len out\n" ++
  "  sd zero, 0(s3); sd zero, 0(s4)\n" ++
  "  # Bounds-check index.\n" ++
  "  li t0, 16\n" ++
  "  bgeu s2, t0, .Lmbc_bad_idx\n" ++
  "  # Verify 17-item list.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mbc_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lmbc_not_branch\n" ++
  "  la t0, mbc_count; ld t1, 0(t0)\n" ++
  "  li t2, 17\n" ++
  "  bne t1, t2, .Lmbc_not_branch\n" ++
  "  # Extract i-th field.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s2\n" ++
  "  la a3, mbc_off; la a4, mbc_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmbc_nth_fail\n" ++
  "  la t0, mbc_off; ld t1, 0(t0)\n" ++
  "  add t2, s0, t1\n" ++
  "  sd t2, 0(s3)\n" ++
  "  la t0, mbc_len; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbc_ret\n" ++
  ".Lmbc_bad_idx:\n" ++
  "  li a0, 2\n" ++
  "  j .Lmbc_ret\n" ++
  ".Lmbc_not_branch:\n" ++
  "  li a0, 1\n" ++
  "  j .Lmbc_ret\n" ++
  ".Lmbc_nth_fail:\n" ++
  "  li a0, 3\n" ++
  ".Lmbc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_mpt_branch_get_child`: probe BuildUnit. Reads
    (branch_len, index, branch_bytes), writes
    (status, child_offset, child_len, child_bytes...) to OUTPUT.
    Probe converts the absolute `child_ptr` to a relative offset
    within `branch_rlp` so the test harness can rehydrate. -/
def ziskMptBranchGetChildPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # branch length\n" ++
  "  ld a2, 16(a5)               # index\n" ++
  "  addi a0, a5, 24             # branch ptr\n" ++
  "  li a3, 0xa0010008           # child_ptr (absolute) out\n" ++
  "  li a4, 0xa0010010           # child_len out\n" ++
  "  jal ra, mpt_branch_get_child\n" ++
  "  li t0, 0xa0010008\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmbc_skip_rel\n" ++
  "  addi t2, a5, 24\n" ++
  "  sub t1, t1, t2\n" ++
  "  sd t1, 0(t0)\n" ++
  ".Lmbc_skip_rel:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmbc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  mptBranchGetChildFunction ++ "\n" ++
  ".Lmbc_pdone:"

def ziskMptBranchGetChildDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbc_count:\n" ++
  "  .zero 8\n" ++
  "mbc_off:\n" ++
  "  .zero 8\n" ++
  "mbc_len:\n" ++
  "  .zero 8"


/-! ## mpt_branch_get_value -- PR-K116

    Extract the value field (item 16) of an MPT branch node.

    A branch node is a 17-item RLP list: `[c0, c1, …, c15, value]`.
    The trailing `value` slot holds the leaf payload when the
    walked key terminates exactly at this branch level (i.e., when
    the path's remaining nibble count equals zero on arrival). It
    is the empty RLP string when no key terminates at this branch.

    Sister to PR-K115 `mpt_branch_get_child` — same node, different
    field. Pairs cleanly with the leaf/extension/branch decode
    trio (K113/K114/K115) for full MPT walking.

    Composes:
      - PR-K47 `rlp_list_count_items` — sanity-check 17 items
      - PR-K20 `rlp_list_nth_item`    — field 16 bounds

    Calling convention:
      a0 (input)  : branch_rlp ptr
      a1 (input)  : branch_rlp byte length
      a2 (input)  : u64 out ptr (value_ptr — absolute)
      a3 (input)  : u64 out ptr (value_len)
      ra (input)  : return
      a0 (output) :
        0 : success — value slot extracted (may be empty)
        1 : not a 17-item list (or RLP parse failure)
        2 : field 16 extraction failed (parse error)

    Uses three 8-byte `.data` scratch slots
    (`mbv_count`, `mbv_off`, `mbv_len`). -/
def mptBranchGetValueFunction : String :=
  "mpt_branch_get_value:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # branch ptr\n" ++
  "  mv s1, a1                   # branch len\n" ++
  "  mv s2, a2                   # value_ptr out\n" ++
  "  mv s3, a3                   # value_len out\n" ++
  "  sd zero, 0(s2); sd zero, 0(s3)\n" ++
  "  # Verify 17-item list.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mbv_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lmbv_not_branch\n" ++
  "  la t0, mbv_count; ld t1, 0(t0)\n" ++
  "  li t2, 17\n" ++
  "  bne t1, t2, .Lmbv_not_branch\n" ++
  "  # Extract field 16 (value).\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  li a2, 16\n" ++
  "  la a3, mbv_off; la a4, mbv_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmbv_nth_fail\n" ++
  "  la t0, mbv_off; ld t1, 0(t0)\n" ++
  "  add t2, s0, t1\n" ++
  "  sd t2, 0(s2)\n" ++
  "  la t0, mbv_len; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbv_ret\n" ++
  ".Lmbv_not_branch:\n" ++
  "  li a0, 1\n" ++
  "  j .Lmbv_ret\n" ++
  ".Lmbv_nth_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lmbv_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_mpt_branch_get_value`: probe BuildUnit. Reads
    (branch_len, branch_bytes), writes (status, value_offset,
    value_len, value_bytes...) to OUTPUT. The probe rewrites the
    absolute `value_ptr` to a relative offset within `branch_rlp`. -/
def ziskMptBranchGetValuePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # branch length\n" ++
  "  addi a0, a4, 16             # branch ptr\n" ++
  "  li a2, 0xa0010008           # value_ptr (absolute) out\n" ++
  "  li a3, 0xa0010010           # value_len out\n" ++
  "  jal ra, mpt_branch_get_value\n" ++
  "  li t0, 0xa0010008\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmbv_skip_rel\n" ++
  "  li t2, 0x40000010           # branch_rlp ptr (INPUT_ADDR + 16)\n" ++
  "  sub t1, t1, t2\n" ++
  "  sd t1, 0(t0)\n" ++
  ".Lmbv_skip_rel:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmbv_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  mptBranchGetValueFunction ++ "\n" ++
  ".Lmbv_pdone:"

def ziskMptBranchGetValueDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbv_count:\n" ++
  "  .zero 8\n" ++
  "mbv_off:\n" ++
  "  .zero 8\n" ++
  "mbv_len:\n" ++
  "  .zero 8"


/-! ## mpt_leaf_extract -- PR-K113

    Fully decode an MPT leaf node RLP:

      node = [compact_path, value]

    into:
    - path nibbles (decompressed from compact form)
    - absolute pointer to the value bytes (inside `node_rlp`)
    - value byte length

    Rejects branch (17-item), extension (2-item with non-leaf
    prefix), and malformed RLP inputs.

    Composes:
      - PR-K20 `rlp_list_nth_item` — field extractor
      - PR-K110 (compact_to_nibbles, inlined here) — path decode

    Callers chain this with PR-K27 `account_decode` to walk the
    state trie's leaves into structured account fields, or with
    storage-slot decoders to read slot values straight out of
    leaves.

    Calling convention:
      a0 (input)  : node_rlp ptr
      a1 (input)  : node_rlp byte length
      a2 (input)  : 64-byte nibbles output ptr
      a3 (input)  : u64 out ptr (nibble count)
      a4 (input)  : u64 out ptr (value_ptr — absolute)
      a5 (input)  : u64 out ptr (value_len)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse / not 2-item list / missing path
        2 : compact prefix says extension, not leaf

    Uses two 8-byte `.data` scratch slots (`mle_path_off`,
    `mle_path_len`). -/
def mptLeafExtract_prog : Program :=
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
    .MV .x21 .x15,
    .SD .x19 .x0 (0 : BitVec 12),
    .SD .x20 .x0 (0 : BitVec 12),
    .SD .x21 .x0 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mle_path_off (GuestAddrs.mpt_leaf_extract + 84)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mle_path_off (GuestAddrs.mpt_leaf_extract + 84)),
    .AUIPC .x14 (laHi GuestAddrs.mle_path_len (GuestAddrs.mpt_leaf_extract + 92)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mle_path_len (GuestAddrs.mpt_leaf_extract + 92)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_leaf_extract + 100)),
    .BNE .x10 .x0 (240 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mle_path_len (GuestAddrs.mpt_leaf_extract + 108)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mle_path_len (GuestAddrs.mpt_leaf_extract + 108)),
    .LD .x31 .x5 (0 : BitVec 12),
    .BEQ .x31 .x0 (224 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mle_path_off (GuestAddrs.mpt_leaf_extract + 124)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mle_path_off (GuestAddrs.mpt_leaf_extract + 124)),
    .LD .x30 .x5 (0 : BitVec 12),
    .ADD .x22 .x8 .x30,
    .LBU .x5 .x22 (0 : BitVec 12),
    .SRLI .x6 .x5 (4 : BitVec 6),
    .ANDI .x7 .x6 (2 : BitVec 12),
    .BEQ .x7 .x0 (184 : BitVec 13),
    .ANDI .x28 .x6 (1 : BitVec 12),
    .MV .x29 .x18,
    .LI .x30 (0 : Word),
    .BEQ .x28 .x0 (20 : BitVec 13),
    .ANDI .x31 .x5 (15 : BitVec 12),
    .SB .x29 .x31 (0 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mle_path_len (GuestAddrs.mpt_leaf_extract + 188)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mle_path_len (GuestAddrs.mpt_leaf_extract + 188)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .ADDI .x31 .x22 (1 : BitVec 12),
    .BEQ .x6 .x0 (44 : BitVec 13),
    .LBU .x5 .x31 (0 : BitVec 12),
    .SRLI .x7 .x5 (4 : BitVec 6),
    .ANDI .x28 .x5 (15 : BitVec 12),
    .SB .x29 .x7 (0 : BitVec 12),
    .SB .x29 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (2 : BitVec 12),
    .ADDI .x30 .x30 (2 : BitVec 12),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-40 : BitVec 21),
    .SD .x19 .x30 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mle_path_off (GuestAddrs.mpt_leaf_extract + 268)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mle_path_off (GuestAddrs.mpt_leaf_extract + 268)),
    .AUIPC .x14 (laHi GuestAddrs.mle_path_len (GuestAddrs.mpt_leaf_extract + 276)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mle_path_len (GuestAddrs.mpt_leaf_extract + 276)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_leaf_extract + 284)),
    .BNE .x10 .x0 (56 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mle_path_off (GuestAddrs.mpt_leaf_extract + 292)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mle_path_off (GuestAddrs.mpt_leaf_extract + 292)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x8 .x6,
    .SD .x20 .x7 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mle_path_len (GuestAddrs.mpt_leaf_extract + 312)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mle_path_len (GuestAddrs.mpt_leaf_extract + 312)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x21 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (8 : BitVec 21),
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

/-- Reloc side-table for `mptLeafExtract_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptLeafExtract_relocs : RelocTable :=
  [ (21, .la .x13 "mle_path_off"),
    (23, .la .x14 "mle_path_len"),
    (25, .jal .x1 "rlp_list_nth_item"),
    (27, .la .x5 "mle_path_len"),
    (31, .la .x5 "mle_path_off"),
    (47, .la .x5 "mle_path_len"),
    (67, .la .x13 "mle_path_off"),
    (69, .la .x14 "mle_path_len"),
    (71, .jal .x1 "rlp_list_nth_item"),
    (73, .la .x5 "mle_path_off"),
    (78, .la .x5 "mle_path_len") ]

def mptLeafExtractFunction : String :=
  "mpt_leaf_extract:\n" ++ emitProgramR mptLeafExtract_prog mptLeafExtract_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptLeafExtract_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptLeafExtractFunction_eq_prog :
    mptLeafExtractFunction = "mpt_leaf_extract:\n" ++ emitProgramR mptLeafExtract_prog mptLeafExtract_relocs := rfl

#guard mptLeafExtractFunction.startsWith "mpt_leaf_extract:\n"
/-- `zisk_mpt_leaf_extract`: probe BuildUnit. Reads
    (node_len, node_bytes), writes (status, nibble_count,
    value_offset_in_node, value_len, nibbles...) to OUTPUT.
    The probe rewrites the returned absolute `value_ptr` to a
    relative offset within `node_rlp` so the test harness can
    rehydrate the value from the host `-i` file. -/
def ziskMptLeafExtractPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # node length\n" ++
  "  addi a0, a6, 16             # node ptr\n" ++
  "  li a2, 0xa0010020           # nibbles output\n" ++
  "  li a3, 0xa0010008           # nibble_count out\n" ++
  "  li a4, 0xa0010010           # value_ptr (absolute) out\n" ++
  "  li a5, 0xa0010018           # value_len out\n" ++
  "  jal ra, mpt_leaf_extract\n" ++
  "  # Convert absolute value_ptr to relative offset within node_rlp.\n" ++
  "  li t0, 0xa0010010\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmle_skip_rel\n" ++
  "  addi t2, a6, 16\n" ++
  "  sub t1, t1, t2\n" ++
  "  sd t1, 0(t0)\n" ++
  ".Lmle_skip_rel:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmle_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptLeafExtractFunction ++ "\n" ++
  ".Lmle_pdone:"

def ziskMptLeafExtractDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mle_path_off:\n" ++
  "  .zero 8\n" ++
  "mle_path_len:\n" ++
  "  .zero 8"


/-! ## mpt_extension_extract -- PR-K114

    Fully decode an MPT extension node RLP:

      node = [compact_path, child_ref]

    into:
    - path nibbles (decompressed from compact form)
    - absolute pointer to the child reference bytes (inside `node_rlp`)
    - child reference byte length

    The child reference is either a 32-byte keccak digest (when the
    referenced node's RLP encoding is ≥ 32 B) or an embedded RLP
    blob (when shorter); see PR-K112 `encode_internal_node`.

    Rejects leaf (2-item with leaf-flagged prefix), branch
    (17-item), and malformed RLP inputs.

    Sister to PR-K113 `mpt_leaf_extract`. Same shape and field
    layout; the only behavioural difference is the prefix-bit
    polarity (rejects when `is_leaf` is set rather than when
    cleared).

    Composes:
      - PR-K20 replacement `rlp_walk_init`/`rlp_walk_next` — one-pass field walk
      - PR-K110 `compact_to_nibbles` (inlined) — path decode

    Calling convention:
      a0 (input)  : node_rlp ptr
      a1 (input)  : node_rlp byte length
      a2 (input)  : 64-byte nibbles output ptr
      a3 (input)  : u64 out ptr (nibble count)
      a4 (input)  : u64 out ptr (child_ref_ptr — absolute)
      a5 (input)  : u64 out ptr (child_ref_len)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse / not 2-item list / missing path
        2 : compact prefix says leaf, not extension

    Uses the saved frame for the walk cursor/end and two 8-byte `.data`
    scratch slots (`mee_path_off`, `mee_path_len`). -/
def mptExtensionExtract_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
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
    .MV .x21 .x15,
    .SD .x19 .x0 (0 : BitVec 12),
    .SD .x20 .x0 (0 : BitVec 12),
    .SD .x21 .x0 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.mpt_extension_extract + 80)),
    .BNE .x12 .x0 (brOff (GuestAddrs.mpt_extension_extract + 340) (GuestAddrs.mpt_extension_extract + 84)),
    .SD .x2 .x10 (64 : BitVec 12),
    .SD .x2 .x11 (72 : BitVec 12),
    .LD .x10 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.mpt_extension_extract + 104)),
    .BNE .x11 .x0 (brOff (GuestAddrs.mpt_extension_extract + 340) (GuestAddrs.mpt_extension_extract + 108)),
    .SUB .x6 .x10 .x12,
    .SUB .x6 .x6 .x8,
    .AUIPC .x5 (laHi GuestAddrs.mee_path_off (GuestAddrs.mpt_extension_extract + 120)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mee_path_off (GuestAddrs.mpt_extension_extract + 120)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mee_path_len (GuestAddrs.mpt_extension_extract + 132)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mee_path_len (GuestAddrs.mpt_extension_extract + 132)),
    .SD .x5 .x12 (0 : BitVec 12),
    .SD .x2 .x10 (64 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mee_path_len (GuestAddrs.mpt_extension_extract + 148)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mee_path_len (GuestAddrs.mpt_extension_extract + 148)),
    .LD .x31 .x5 (0 : BitVec 12),
    .BEQ .x31 .x0 (brOff (GuestAddrs.mpt_extension_extract + 340) (GuestAddrs.mpt_extension_extract + 160)),
    .AUIPC .x5 (laHi GuestAddrs.mee_path_off (GuestAddrs.mpt_extension_extract + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mee_path_off (GuestAddrs.mpt_extension_extract + 164)),
    .LD .x30 .x5 (0 : BitVec 12),
    .ADD .x22 .x8 .x30,
    .LBU .x5 .x22 (0 : BitVec 12),
    .SRLI .x6 .x5 (4 : BitVec 6),
    .ANDI .x7 .x6 (2 : BitVec 12),
    .BNE .x7 .x0 (brOff (GuestAddrs.mpt_extension_extract + 332) (GuestAddrs.mpt_extension_extract + 192)),
    .ANDI .x28 .x6 (1 : BitVec 12),
    .MV .x29 .x18,
    .LI .x30 (0 : Word),
    .BEQ .x28 .x0 (20 : BitVec 13),
    .ANDI .x31 .x5 (15 : BitVec 12),
    .SB .x29 .x31 (0 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mee_path_len (GuestAddrs.mpt_extension_extract + 228)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mee_path_len (GuestAddrs.mpt_extension_extract + 228)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .ADDI .x31 .x22 (1 : BitVec 12),
    .BEQ .x6 .x0 (44 : BitVec 13),
    .LBU .x5 .x31 (0 : BitVec 12),
    .SRLI .x7 .x5 (4 : BitVec 6),
    .ANDI .x28 .x5 (15 : BitVec 12),
    .SB .x29 .x7 (0 : BitVec 12),
    .SB .x29 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (2 : BitVec 12),
    .ADDI .x30 .x30 (2 : BitVec 12),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-36 : BitVec 13),
    .SD .x19 .x30 (0 : BitVec 12),
    .LD .x10 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.mpt_extension_extract + 304)),
    .BNE .x11 .x0 (32 : BitVec 13),
    .SUB .x6 .x10 .x12,
    .SD .x20 .x6 (0 : BitVec 12),
    .SD .x21 .x12 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptExtensionExtract_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptExtensionExtract_relocs : RelocTable :=
  [ (20, .jal .x1 "rlp_walk_init"),
    (26, .jal .x1 "rlp_walk_next"),
    (30, .la .x5 "mee_path_off"),
    (33, .la .x5 "mee_path_len"),
    (37, .la .x5 "mee_path_len"),
    (41, .la .x5 "mee_path_off"),
    (57, .la .x5 "mee_path_len"),
    (76, .jal .x1 "rlp_walk_next") ]

def mptExtensionExtractFunction : String :=
  "mpt_extension_extract:\n" ++ emitProgramR mptExtensionExtract_prog mptExtensionExtract_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptExtensionExtract_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptExtensionExtractFunction_eq_prog :
    mptExtensionExtractFunction = "mpt_extension_extract:\n" ++ emitProgramR mptExtensionExtract_prog mptExtensionExtract_relocs := rfl

#guard mptExtensionExtractFunction.startsWith "mpt_extension_extract:\n"
/-- `zisk_mpt_extension_extract`: probe BuildUnit. Reads
    (node_len, node_bytes), writes (status, nibble_count,
    child_ref_offset_in_node, child_ref_len, nibbles...) to OUTPUT.
    The probe rewrites the absolute `child_ref_ptr` to a relative
    offset within `node_rlp` so the test harness can rehydrate the
    bytes from the host `-i` file. -/
def ziskMptExtensionExtractPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # node length\n" ++
  "  addi a0, a6, 16             # node ptr\n" ++
  "  li a2, 0xa0010020           # nibbles output\n" ++
  "  li a3, 0xa0010008           # nibble_count out\n" ++
  "  li a4, 0xa0010010           # child_ref_ptr (absolute) out\n" ++
  "  li a5, 0xa0010018           # child_ref_len out\n" ++
  "  jal ra, mpt_extension_extract\n" ++
  "  li t0, 0xa0010010\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmee_skip_rel\n" ++
  "  addi t2, a6, 16\n" ++
  "  sub t1, t1, t2\n" ++
  "  sd t1, 0(t0)\n" ++
  ".Lmee_skip_rel:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmee_pdone\n" ++
  rlpWalkInitFunction ++ "\n" ++
  rlpWalkNextFunction ++ "\n" ++
  mptExtensionExtractFunction ++ "\n" ++
  ".Lmee_pdone:"

def ziskMptExtensionExtractDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mee_path_off:\n" ++
  "  .zero 8\n" ++
  "mee_path_len:\n" ++
  "  .zero 8"



/-! ## mpt_branch_used_count -- PR-K117

    Count the number of non-empty child slots in an MPT branch
    node's `[c0, c1, …, c15, value]` head. A child slot is
    "non-empty" iff its RLP byte-length is > 0 (empty children
    serialise as the empty RLP string `0x80`, len 0).

    Used by state-root recomputation to detect *single-child*
    branches that can collapse into an extension after a delete
    operation: the trie invariant says a branch must always have
    ≥ 2 children or be replaced by an extension/leaf.

    The `value` field (item 16) is **not** counted; only the 16
    nibble-indexed children. A branch where the value slot is the
    only non-empty entry still returns 0 here (and is itself a
    consensus violation under the standard trie invariants).
-/
/-! ## mpt_branch_first_used_index -- PR-K118

    Find the lowest-indexed non-empty child slot in an MPT branch
    node's `[c0, c1, …, c15, value]` head. Returns the index in
    `[0, 15]` of the first child whose RLP byte-length is > 0, or
    `16` (sentinel "none") when every child slot is empty.

    Used by state-root recomputation in the *trie-collapse* path:
    when PR-K117 `mpt_branch_used_count` reports exactly one
    surviving child, this helper tells the rewriter *which* child
    to inline into the parent's path.

    The `value` field (item 16) is **not** scanned. A branch where
    the value slot is the only non-empty entry still returns the
    `16` sentinel.

    Composes:
      - PR-K47 `rlp_list_count_items` — sanity-check 17 items
      - PR-K20 `rlp_list_nth_item`    — per-child length probe

    Calling convention:
      a0 (input)  : branch_rlp ptr
      a1 (input)  : branch_rlp byte length
      a2 (input)  : u64 out ptr (used_count, 0..16)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : not a 17-item list (or RLP parse failure)
        2 : mid-list nth_item failure -/
def mptBranchUsedCountFunction : String :=
  "mpt_branch_used_count:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # branch ptr\n" ++
  "  mv s1, a1                   # branch len\n" ++
  "  mv s2, a2                   # used_count out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Verify 17-item list.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mbuc_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lmbuc_not_branch\n" ++
  "  la t0, mbuc_count; ld t1, 0(t0)\n" ++
  "  li t2, 17\n" ++
  "  bne t1, t2, .Lmbuc_not_branch\n" ++
  "  li s3, 0                    # i = 0\n" ++
  "  li s4, 0                    # used = 0\n" ++
  ".Lmbuc_loop:\n" ++
  "  li t0, 16\n" ++
  "  beq s3, t0, .Lmbuc_done\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s3\n" ++
  "  la a3, mbuc_off; la a4, mbuc_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmbuc_nth_fail\n" ++
  "  la t0, mbuc_len; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmbuc_step\n" ++
  "  addi s4, s4, 1\n" ++
  ".Lmbuc_step:\n" ++
  "  addi s3, s3, 1\n" ++
  "  j .Lmbuc_loop\n" ++
  ".Lmbuc_done:\n" ++
  "  sd s4, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbuc_ret\n" ++
  ".Lmbuc_not_branch:\n" ++
  "  li a0, 1\n" ++
  "  j .Lmbuc_ret\n" ++
  ".Lmbuc_nth_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lmbuc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"
def mptBranchFirstUsedIndexFunction : String :=
  "mpt_branch_first_used_index:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # branch ptr\n" ++
  "  mv s1, a1                   # branch len\n" ++
  "  mv s2, a2                   # used_count out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Verify 17-item list.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mbuc_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lmbuc_not_branch\n" ++
  "  la t0, mbuc_count; ld t1, 0(t0)\n" ++
  "  li t2, 17\n" ++
  "  bne t1, t2, .Lmbuc_not_branch\n" ++
  "  li s3, 0                    # i = 0\n" ++
  "  li s4, 0                    # used = 0\n" ++
  ".Lmbuc_loop:\n" ++
  "  li t0, 16\n" ++
  "  beq s3, t0, .Lmbuc_done\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s3\n" ++
  "  la a3, mbuc_off; la a4, mbuc_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmbuc_nth_fail\n" ++
  "  la t0, mbuc_len; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmbuc_step\n" ++
  "  addi s4, s4, 1\n" ++
  ".Lmbuc_step:\n" ++
  "  addi s3, s3, 1\n" ++
  "  j .Lmbuc_loop\n" ++
  ".Lmbuc_done:\n" ++
  "  sd s4, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbuc_ret\n" ++
  ".Lmbuc_not_branch:\n" ++
  "  li a0, 1\n" ++
  "  j .Lmbuc_ret\n" ++
  ".Lmbuc_nth_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lmbuc_ret:\n" ++
  "  mv s2, a2                   # first_index out\n" ++
  "  li t0, 16\n" ++
  "  sd t0, 0(s2)                # default = 16 (none)\n" ++
  "  # Verify 17-item list.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mbfui_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lmbfui_not_branch\n" ++
  "  la t0, mbfui_count; ld t1, 0(t0)\n" ++
  "  li t2, 17\n" ++
  "  bne t1, t2, .Lmbfui_not_branch\n" ++
  "  li s3, 0                    # i = 0\n" ++
  ".Lmbfui_loop:\n" ++
  "  li t0, 16\n" ++
  "  beq s3, t0, .Lmbfui_done\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s3\n" ++
  "  la a3, mbfui_off; la a4, mbfui_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmbfui_nth_fail\n" ++
  "  la t0, mbfui_len; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmbfui_step\n" ++
  "  # Found first non-empty child.\n" ++
  "  sd s3, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbfui_ret\n" ++
  ".Lmbfui_step:\n" ++
  "  addi s3, s3, 1\n" ++
  "  j .Lmbfui_loop\n" ++
  ".Lmbfui_done:\n" ++
  "  # No non-empty children; output stays at sentinel 16.\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbfui_ret\n" ++
  ".Lmbfui_not_branch:\n" ++
  "  li a0, 1\n" ++
  "  j .Lmbfui_ret\n" ++
  ".Lmbfui_nth_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lmbfui_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_mpt_branch_used_count`: probe BuildUnit. Reads
    (branch_len, branch_bytes), writes (status, used_count) to
    OUTPUT (16 bytes). -/
def ziskMptBranchUsedCountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # branch length\n" ++
  "  addi a0, a3, 16             # branch ptr\n" ++
  "  li a2, 0xa0010008           # used_count out\n" ++
  "  jal ra, mpt_branch_used_count\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmbuc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  mptBranchUsedCountFunction ++ "\n" ++
  ".Lmbuc_pdone:"

def ziskMptBranchUsedCountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbuc_count:\n" ++
  "  .zero 8\n" ++
  "mbuc_off:\n" ++
  "  .zero 8\n" ++
  "mbuc_len:\n" ++
  "  .zero 8"


/-- `zisk_mpt_branch_first_used_index`: probe BuildUnit. Reads
    (branch_len, branch_bytes), writes (status, first_index) to
    OUTPUT (16 bytes). -/
def ziskMptBranchFirstUsedIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # branch length\n" ++
  "  addi a0, a3, 16             # branch ptr\n" ++
  "  li a2, 0xa0010008           # first_index out\n" ++
  "  jal ra, mpt_branch_first_used_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmbfui_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  mptBranchFirstUsedIndexFunction ++ "\n" ++
  ".Lmbfui_pdone:"

def ziskMptBranchFirstUsedIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbfui_count:\n" ++
  "  .zero 8\n" ++
  "mbfui_off:\n" ++
  "  .zero 8\n" ++
  "mbfui_len:\n" ++
  "  .zero 8"






/-- `zisk_rlp_list_nth_item`: probe BuildUnit. Reads
    (list_len, N, list_bytes) from host input, writes
    (status, offset, length) to OUTPUT.
    Input layout:
      bytes  0.. 8 : list_len (u64)
      bytes  8..16 : N (u64)
      bytes 16..   : RLP list bytes
    Output layout:
      bytes  0.. 8 : status (0 hit / 1 miss)
      bytes  8..16 : content offset (u64)
      bytes 16..24 : content length (u64) -/
def ziskRlpListNthItemPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # list_len\n" ++
  "  ld a2, 16(a5)               # N\n" ++
  "  addi a0, a5, 24             # list ptr\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  sd zero, 0(a3); sd zero, 0(a4)\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lrln_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  ".Lrln_pdone:"

def ziskRlpListNthItemDataSection : String :=
  ".section .data\n" ++
  "rln_scratch:\n" ++
  "  .zero 8"





end EvmAsm.Codegen
