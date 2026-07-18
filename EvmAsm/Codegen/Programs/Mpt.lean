/-
  EvmAsm.Codegen.Programs.Mpt

  MPT codec primitives (PR-K109..K116):
  - K109 `mpt_nibbles_to_compact`     — encoder side of HP
  - K110 `mpt_compact_to_nibbles`     — decoder side of HP
  - K111 `mpt_node_classify`          — branch / leaf / extension
  - K112 `mpt_encode_internal_node`   — embed-or-hash node reference
  - K113 `mpt_leaf_extract`           — leaf node → (nibbles, value)
  - K114 `mpt_extension_extract`      — ext node → (nibbles, child_ref)
  - K115 `mpt_branch_get_child`       — i-th child of a branch
  - K116 `mpt_branch_get_value`       — field 16 of a branch

  Lifted out of `EvmAsm.Codegen.Programs` to keep the registry hub
  manageable.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.MptWitnessLookup
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_account_path_nibbles -- PR-K100

    Compute the state trie's path for a given 20-byte address:

      digest   = keccak256(address)         # 32 bytes
      nibbles  = unpack_high_low(digest)    # 64 nibbles

    The MPT walks paths in nibble units (each byte = two
    consecutive nibbles, high first). Account lookups in the state
    trie use `keccak256(address)` as the path key, expressed as 64
    nibbles. PR-K24 `mpt_walk` consumes such a nibble array; this
    helper produces it from an address in one call.

    Storage slots use the analogous `keccak256(slot_key_BE)` path;
    K100 also handles that case directly when callers feed in a
    32-byte slot key (see calling convention).

    Composes PR-K3 `zkvm_keccak256`. Uses 32 bytes of `.data`
    scratch (`mapn_digest`).

    Calling convention:
      a0 (input)  : address (or slot key) ptr
      a1 (input)  : input length (20 for address, 32 for slot key)
      a2 (input)  : 64-byte nibble output ptr
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def mptAccountPathNibblesFunction : String :=
  "mpt_account_path_nibbles:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a2                   # nibble output ptr (stash)\n" ++
  "  # keccak256(input, len) → mapn_digest\n" ++
  "  la a2, mapn_digest\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Unpack 32 bytes → 64 nibbles.\n" ++
  "  la t0, mapn_digest\n" ++
  "  mv t1, s0                   # cursor over output\n" ++
  "  li t2, 32                   # remaining bytes\n" ++
  ".Lmapn_loop:\n" ++
  "  beqz t2, .Lmapn_done\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  srli t4, t3, 4              # high nibble\n" ++
  "  andi t5, t3, 15             # low nibble\n" ++
  "  sb t4, 0(t1)\n" ++
  "  sb t5, 1(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 2\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lmapn_loop\n" ++
  ".Lmapn_done:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_mpt_account_path_nibbles`: probe BuildUnit. Reads
    (input_len, input_bytes) from host input, writes (status, 64
    nibbles) to OUTPUT (72 bytes total). -/
def ziskMptAccountPathNibblesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # input length\n" ++
  "  addi a0, a3, 16             # input ptr\n" ++
  "  li a2, 0xa0010008           # 64-byte nibble output\n" ++
  "  jal ra, mpt_account_path_nibbles\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmapn_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptAccountPathNibblesFunction ++ "\n" ++
  ".Lmapn_pdone:"

def ziskMptAccountPathNibblesDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "mapn_digest:\n" ++
  "  .zero 32"

def ziskMptAccountPathNibblesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptAccountPathNibblesPrologue
  dataAsm     := ziskMptAccountPathNibblesDataSection
}

/-! ## mpt_node_kind -- PR-K21 classifier

    Determines whether an RLP-encoded MPT node is a leaf,
    extension, or branch by:
      1. Probing whether item 2 exists (presence = 17-item
         branch list).
      2. If absent, reading item 0's first byte and inspecting
         the high nibble (HP encoding flag: 0/1 → extension,
         2/3 → leaf).

    Calling convention:
      a0 (input)  : node bytes ptr
      a1 (input)  : node byte length
      ra (input)  : return
      a0 (output) : 0 branch / 1 extension / 2 leaf / 3 parse fail

    Calls `rlp_list_nth_item` twice. Uses four 8-byte `.data`
    scratches (`mnk_dummy_offset`, `mnk_dummy_length`,
    `mnk_path_offset`, `mnk_path_length`) for the temporary
    returns. -/
def mptNodeKind_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .LI .x12 (2 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mnk_dummy_offset (GuestAddrs.mpt_node_kind + 28)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mnk_dummy_offset (GuestAddrs.mpt_node_kind + 28)),
    .AUIPC .x14 (laHi GuestAddrs.mnk_dummy_length (GuestAddrs.mpt_node_kind + 36)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mnk_dummy_length (GuestAddrs.mpt_node_kind + 36)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_node_kind + 44)),
    .BEQ .x10 .x0 (100 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mnk_path_offset (GuestAddrs.mpt_node_kind + 64)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mnk_path_offset (GuestAddrs.mpt_node_kind + 64)),
    .AUIPC .x14 (laHi GuestAddrs.mnk_path_length (GuestAddrs.mpt_node_kind + 72)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mnk_path_length (GuestAddrs.mpt_node_kind + 72)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_node_kind + 80)),
    .BNE .x10 .x0 (88 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mnk_path_offset (GuestAddrs.mpt_node_kind + 88)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mnk_path_offset (GuestAddrs.mpt_node_kind + 88)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mnk_path_length (GuestAddrs.mpt_node_kind + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mnk_path_length (GuestAddrs.mpt_node_kind + 100)),
    .LD .x7 .x5 (0 : BitVec 12),
    .BEQ .x7 .x0 (60 : BitVec 13),
    .ADD .x28 .x8 .x6,
    .LBU .x29 .x28 (0 : BitVec 12),
    .SRLI .x29 .x29 (4 : BitVec 6),
    .LI .x30 (2 : Word),
    .BLTU .x29 .x30 (24 : BitVec 13),
    .LI .x30 (4 : Word),
    .BLTU .x29 .x30 (24 : BitVec 13),
    .JAL .x0 (28 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (3 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptNodeKind_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptNodeKind_relocs : RelocTable :=
  [ (7, .la .x13 "mnk_dummy_offset"),
    (9, .la .x14 "mnk_dummy_length"),
    (11, .jal .x1 "rlp_list_nth_item"),
    (16, .la .x13 "mnk_path_offset"),
    (18, .la .x14 "mnk_path_length"),
    (20, .jal .x1 "rlp_list_nth_item"),
    (22, .la .x5 "mnk_path_offset"),
    (25, .la .x5 "mnk_path_length") ]

def mptNodeKindFunction : String :=
  "mpt_node_kind:\n" ++ emitProgramR mptNodeKind_prog mptNodeKind_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptNodeKind_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptNodeKindFunction_eq_prog :
    mptNodeKindFunction = "mpt_node_kind:\n" ++ emitProgramR mptNodeKind_prog mptNodeKind_relocs := rfl

#guard mptNodeKindFunction.startsWith "mpt_node_kind:\n"
#guard mptNodeKind_prog.length = 49
/-- `zisk_mpt_node_kind`: probe BuildUnit. Reads
    (node_len, node_bytes) from host input, writes
    classification result to OUTPUT.
    Input layout:
      bytes  0.. 8 : node_len (u64)
      bytes  8..   : node bytes
    Output layout:
      bytes  0.. 8 : kind (u64; 0 branch / 1 ext / 2 leaf / 3 fail) -/
def ziskMptNodeKindPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # node_len\n" ++
  "  addi a0, a3, 16             # node ptr\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # write kind\n" ++
  "  j .Lmnk_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  ".Lmnk_pdone:"

def ziskMptNodeKindDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8"

def ziskMptNodeKindProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptNodeKindPrologue
  dataAsm     := ziskMptNodeKindDataSection
}

/-! ## mpt_branch_child -- PR-K22 extract i-th child of a branch

    Wraps `rlp_list_nth_item` with a branch-shape-aware
    interpretation of the returned content. Ethereum MPT branch
    nodes have items 0..15 each being one of:

      * 32-byte hash       (Bytes32: 0xa0 + 32 raw bytes)
      * empty bytes        (RLP 0x80)
      * inlined RLP node   (variable bytes, < 32 bytes total)

    Calling convention:
      a0 (input)  : branch node bytes ptr
      a1 (input)  : node byte length
      a2 (input)  : nibble (0..15)
      a3 (input)  : 32-byte output buffer ptr
      ra (input)  : return
      a0 (output) :
        0 = hash slot (32 bytes copied to *a3)
        1 = empty slot (output buffer zeroed)
        2 = inlined RLP node (output buffer holds first ≤ 32
            bytes of the inlined form, zero-padded)
        3 = parse failure (nibble out of range or node
            malformed)

    Does NOT verify the caller has actually given a branch
    node; if applied to a 2-item leaf/extension, items 0 and 1
    are returned according to the same length-driven rules but
    the semantics aren't branch-children. -/
def mptBranchChild_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .LI .x5 (16 : Word),
    .BGEU .x18 .x5 (216 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .AUIPC .x13 (laHi GuestAddrs.mbc_offset (GuestAddrs.mpt_branch_child + 60)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mbc_offset (GuestAddrs.mpt_branch_child + 60)),
    .AUIPC .x14 (laHi GuestAddrs.mbc_length (GuestAddrs.mpt_branch_child + 68)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mbc_length (GuestAddrs.mpt_branch_child + 68)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_branch_child + 76)),
    .BNE .x10 .x0 (180 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mbc_length (GuestAddrs.mpt_branch_child + 84)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mbc_length (GuestAddrs.mpt_branch_child + 84)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (68 : BitVec 13),
    .LI .x5 (32 : Word),
    .BNE .x6 .x5 (84 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mbc_offset (GuestAddrs.mpt_branch_child + 108)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mbc_offset (GuestAddrs.mpt_branch_child + 108)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x7 .x8 .x7,
    .LD .x28 .x7 (0 : BitVec 12),
    .SD .x19 .x28 (0 : BitVec 12),
    .LD .x28 .x7 (8 : BitVec 12),
    .SD .x19 .x28 (8 : BitVec 12),
    .LD .x28 .x7 (16 : BitVec 12),
    .SD .x19 .x28 (16 : BitVec 12),
    .LD .x28 .x7 (24 : BitVec 12),
    .SD .x19 .x28 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (120 : BitVec 21),
    .SD .x19 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (8 : BitVec 12),
    .SD .x19 .x0 (16 : BitVec 12),
    .SD .x19 .x0 (24 : BitVec 12),
    .LI .x10 (1 : Word),
    .JAL .x0 (96 : BitVec 21),
    .SD .x19 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (8 : BitVec 12),
    .SD .x19 .x0 (16 : BitVec 12),
    .SD .x19 .x0 (24 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mbc_offset (GuestAddrs.mpt_branch_child + 204)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mbc_offset (GuestAddrs.mpt_branch_child + 204)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x7 .x8 .x7,
    .MV .x28 .x19,
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x29 .x7 (0 : BitVec 12),
    .SB .x28 .x29 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (24 : BitVec 21),
    .SD .x19 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (8 : BitVec 12),
    .SD .x19 .x0 (16 : BitVec 12),
    .SD .x19 .x0 (24 : BitVec 12),
    .LI .x10 (3 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptBranchChild_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptBranchChild_relocs : RelocTable :=
  [ (15, .la .x13 "mbc_offset"),
    (17, .la .x14 "mbc_length"),
    (19, .jal .x1 "rlp_list_nth_item"),
    (21, .la .x5 "mbc_length"),
    (27, .la .x5 "mbc_offset"),
    (51, .la .x5 "mbc_offset") ]

def mptBranchChildFunction : String :=
  "mpt_branch_child:\n" ++ emitProgramR mptBranchChild_prog mptBranchChild_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptBranchChild_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptBranchChildFunction_eq_prog :
    mptBranchChildFunction = "mpt_branch_child:\n" ++ emitProgramR mptBranchChild_prog mptBranchChild_relocs := rfl

#guard mptBranchChildFunction.startsWith "mpt_branch_child:\n"
#guard mptBranchChild_prog.length = 77
/-- `zisk_mpt_branch_child`: probe BuildUnit. Reads
    (node_len, nibble, node_bytes) from host input, writes
    (status, 32-byte content) to OUTPUT.
    Input layout:
      bytes  0.. 8 : node_len (u64)
      bytes  8..16 : nibble (u64)
      bytes 16..   : node bytes
    Output layout:
      bytes  0.. 8 : status (0 hash / 1 empty / 2 inlined / 3 fail)
      bytes  8..40 : 32-byte content (hash, zeros, or inlined bytes) -/
def ziskMptBranchChildPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # node_len\n" ++
  "  ld a2, 16(a4)               # nibble\n" ++
  "  addi a0, a4, 24             # node ptr\n" ++
  "  li a3, 0xa0010008           # 32-byte out at OUTPUT + 8\n" ++
  "  jal ra, mpt_branch_child\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lmbc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  ".Lmbc_pdone:"

def ziskMptBranchChildDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8"

def ziskMptBranchChildProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptBranchChildPrologue
  dataAsm     := ziskMptBranchChildDataSection
}

/-! ## hp_decode_nibbles -- PR-K23 HP-encoded path → nibble array

    Decode the HP-encoded first item of a leaf/extension MPT
    node into an array of one-nibble bytes (each ∈ [0..15]).
    Also returns whether the node is a leaf or extension.

    HP encoding cheat-sheet (input byte 0):
      high nibble  meaning
      ----------   -------
         0         extension, even path length (low nibble ignored)
         1         extension, odd path length (low nibble is first path nibble)
         2         leaf, even path length (low nibble ignored)
         3         leaf, odd path length (low nibble is first path nibble)
      anything else → invalid

    Remaining input bytes hold 2 nibbles each (high, then low),
    contributing to the output starting at the next slot.

    Calling convention:
      a0 (input)  : HP-encoded path bytes ptr
      a1 (input)  : path byte length
      a2 (input)  : output nibble buffer (caller-allocated;
                    holds up to 2 * (a1 - 1) + 1 bytes,
                    one byte per nibble)
      a3 (input)  : u64 out ptr (number of nibbles emitted)
      a4 (input)  : u64 out ptr (is_leaf flag: 0 = ext, 1 = leaf)
      ra (input)  : return
      a0 (output) : 0 success, 1 parse failure (empty input or
                    high nibble ≥ 4). The even-path padding nibble
                    (low nibble of byte 0) is IGNORED, matching
                    execution-specs `compact_to_nibbles`
                    (amsterdam/incremental_mpt.py:878-889, lenient;
                    bead evm-asm-3umhl).

    Each output byte holds one nibble in its low 4 bits; the
    high 4 bits are zero. This is the format consumed by future
    `mpt_walk` (PR-K24) which compares one byte per nibble. -/
def hpDecodeNibbles_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
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
    .MV .x20 .x14,
    .BEQ .x9 .x0 (128 : BitVec 13),
    .LBU .x5 .x8 (0 : BitVec 12),
    .SRLI .x6 .x5 (4 : BitVec 6),
    .ANDI .x7 .x5 (15 : BitVec 12),
    .LI .x28 (4 : Word),
    .BGEU .x6 .x28 (108 : BitVec 13),
    .ANDI .x28 .x6 (2 : BitVec 12),
    .SRLI .x28 .x28 (1 : BitVec 6),
    .SD .x20 .x28 (0 : BitVec 12),
    .ANDI .x6 .x6 (1 : BitVec 12),
    .BEQ .x6 .x0 (20 : BitVec 13),
    .SB .x18 .x7 (0 : BitVec 12),
    .LI .x30 (1 : Word),
    .ADDI .x31 .x18 (1 : BitVec 12),
    .JAL .x0 (12 : BitVec 21),
    .LI .x30 (0 : Word),
    .MV .x31 .x18,
    .LI .x5 (1 : Word),
    .BGEU .x5 .x9 (44 : BitVec 13),
    .ADD .x6 .x8 .x5,
    .LBU .x7 .x6 (0 : BitVec 12),
    .SRLI .x28 .x7 (4 : BitVec 6),
    .ANDI .x29 .x7 (15 : BitVec 12),
    .SB .x31 .x28 (0 : BitVec 12),
    .SB .x31 .x29 (1 : BitVec 12),
    .ADDI .x31 .x31 (2 : BitVec 12),
    .ADDI .x30 .x30 (2 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-40 : BitVec 21),
    .SD .x19 .x30 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def hpDecodeNibblesFunction : String :=
  "hp_decode_nibbles:\n" ++ emitProgram hpDecodeNibbles_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `hpDecodeNibbles_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem hpDecodeNibblesFunction_eq_prog :
    hpDecodeNibblesFunction = "hp_decode_nibbles:\n" ++ emitProgram hpDecodeNibbles_prog := rfl

#guard hpDecodeNibblesFunction.startsWith "hp_decode_nibbles:\n"
#guard hpDecodeNibbles_prog.length = 53
/-- `zisk_hp_decode_nibbles`: probe BuildUnit. Reads
    (path_len, path_bytes) from host input, writes
    (status, count, is_leaf, nibbles...) to OUTPUT.
    Input layout:
      bytes  0.. 8 : path_len (u64)
      bytes  8..   : HP-encoded path bytes
    Output layout:
      bytes  0.. 8 : status (u64; 0 ok, 1 fail)
      bytes  8..16 : nibble count (u64)
      bytes 16..24 : is_leaf (u64)
      bytes 24..   : nibble bytes (count bytes; each in [0..15]) -/
def ziskHpDecodeNibblesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # path_len\n" ++
  "  addi a0, a4, 16             # path bytes ptr\n" ++
  "  li a2, 0xa0010018           # nibble buf at OUTPUT + 24\n" ++
  "  li a3, 0xa0010008           # count ptr at OUTPUT + 8\n" ++
  "  li a4, 0xa0010010           # is_leaf ptr at OUTPUT + 16\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lhp_pdone\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  ".Lhp_pdone:"

def ziskHpDecodeNibblesDataSection : String :=
  ".section .data\n" ++
  "hp_pad:\n" ++
  "  .zero 8"

def ziskHpDecodeNibblesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHpDecodeNibblesPrologue
  dataAsm     := ziskHpDecodeNibblesDataSection
}

/-! ## mpt_walk -- PR-K24 end-to-end MPT lookup

    Compose every K-stack primitive into a single
    `mpt_walk(root, witness, path) → value` entry. Walks the
    branch / extension / leaf chain following nibble path
    elements.

    Calling convention:
      a0 (input)  : root_hash ptr (32 bytes)
      a1 (input)  : witness.state SSZ list section ptr
      a2 (input)  : witness section_len
      a3 (input)  : path_nibbles ptr (one byte per nibble)
      a4 (input)  : path_nibbles_len
      a5 (input)  : value output buffer ptr (256 bytes)
      a6 (input)  : u64 out ptr (matched value byte length)
      ra (input)  : return
      a0 (output) : 0 (found) / 1 (not found) / 2 (parse error)

    Calls itself transitively via PR-K19..K23 primitives.
    Uses a 256-byte mw_value_buf for the output and ~200 B of
    additional scratch state. -/
def mptWalk_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .MV .x8 .x11,
    .MV .x9 .x12,
    .MV .x18 .x13,
    .MV .x19 .x14,
    .MV .x20 .x15,
    .MV .x21 .x16,
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 68)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 68)),
    .LD .x6 .x10 (0 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x6 .x10 (8 : BitVec 12),
    .SD .x5 .x6 (8 : BitVec 12),
    .LD .x6 .x10 (16 : BitVec 12),
    .SD .x5 .x6 (16 : BitVec 12),
    .LD .x6 .x10 (24 : BitVec 12),
    .SD .x5 .x6 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 116)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 116)),
    .AUIPC .x13 (laHi GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 124)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 124)),
    .AUIPC .x14 (laHi GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 132)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 132)),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140)),
    .BNE .x10 .x0 (1044 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 148)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 148)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 164)),
    .LD .x24 .x5 (0 : BitVec 12),
    .LI .x22 (0 : Word),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .JAL .x1 (jalOff GuestAddrs.mpt_node_kind (GuestAddrs.mpt_walk + 188)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (300 : BitVec 13),
    .LI .x5 (2 : Word),
    .BEQ .x10 .x5 (672 : BitVec 13),
    .JAL .x0 (988 : BitVec 21),
    .BEQ .x22 .x19 (228 : BitVec 13),
    .ADD .x5 .x18 .x22,
    .LBU .x6 .x5 (0 : BitVec 12),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .MV .x12 .x6,
    .AUIPC .x13 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 240)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 240)),
    .AUIPC .x14 (laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 248)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 248)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 256)),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .BNE .x10 .x0 (936 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 268)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 268)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (908 : BitVec 13),
    .LI .x7 (32 : Word),
    .BEQ .x6 .x7 (28 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 292)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 292)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x7,
    .MV .x24 .x6,
    .JAL .x0 (-132 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 316)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 316)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x23 .x6,
    .AUIPC .x28 (laHi GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 332)),
    .ADDI .x28 .x28 (laLo GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 332)),
    .LD .x29 .x7 (0 : BitVec 12),
    .SD .x28 .x29 (0 : BitVec 12),
    .LD .x29 .x7 (8 : BitVec 12),
    .SD .x28 .x29 (8 : BitVec 12),
    .LD .x29 .x7 (16 : BitVec 12),
    .SD .x28 .x29 (16 : BitVec 12),
    .LD .x29 .x7 (24 : BitVec 12),
    .SD .x28 .x29 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 380)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 380)),
    .AUIPC .x13 (laHi GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 388)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 388)),
    .AUIPC .x14 (laHi GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 396)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 396)),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404)),
    .BNE .x10 .x0 (792 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 412)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 412)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 428)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 428)),
    .LD .x24 .x5 (0 : BitVec 12),
    .JAL .x0 (-260 : BitVec 21),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (16 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_value_offset (GuestAddrs.mpt_walk + 456)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_value_offset (GuestAddrs.mpt_walk + 456)),
    .AUIPC .x14 (laHi GuestAddrs.mw_value_length (GuestAddrs.mpt_walk + 464)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_value_length (GuestAddrs.mpt_walk + 464)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 472)),
    .BNE .x10 .x0 (724 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_value_length (GuestAddrs.mpt_walk + 480)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_value_length (GuestAddrs.mpt_walk + 480)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (696 : BitVec 13),
    .JAL .x0 (604 : BitVec 21),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 512)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 512)),
    .AUIPC .x14 (laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 520)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 520)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 528)),
    .BNE .x10 .x0 (668 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 536)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 536)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x10 .x23 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 552)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 552)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 564)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 564)),
    .AUIPC .x13 (laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 572)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 572)),
    .AUIPC .x14 (laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 580)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 580)),
    .JAL .x1 (jalOff GuestAddrs.hp_decode_nibbles (GuestAddrs.mpt_walk + 588)),
    .BNE .x10 .x0 (608 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 596)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 596)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (592 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 612)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 612)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x22 .x6,
    .BLTU .x19 .x7 (560 : BitVec 13),
    .AUIPC .x7 (laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 632)),
    .ADDI .x7 .x7 (laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 632)),
    .ADD .x28 .x18 .x22,
    .MV .x29 .x6,
    .BEQ .x29 .x0 (32 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .BNE .x30 .x31 (528 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADD .x22 .x22 .x6,
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 696)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 696)),
    .AUIPC .x14 (laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 704)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 704)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 712)),
    .BNE .x10 .x0 (484 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 720)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 720)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 732)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 732)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x28 .x23 .x7,
    .LI .x29 (32 : Word),
    .BEQ .x6 .x29 (16 : BitVec 13),
    .MV .x23 .x28,
    .MV .x24 .x6,
    .JAL .x0 (-584 : BitVec 21),
    .AUIPC .x29 (laHi GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 768)),
    .ADDI .x29 .x29 (laLo GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 768)),
    .LD .x30 .x28 (0 : BitVec 12),
    .SD .x29 .x30 (0 : BitVec 12),
    .LD .x30 .x28 (8 : BitVec 12),
    .SD .x29 .x30 (8 : BitVec 12),
    .LD .x30 .x28 (16 : BitVec 12),
    .SD .x29 .x30 (16 : BitVec 12),
    .LD .x30 .x28 (24 : BitVec 12),
    .SD .x29 .x30 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 816)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_lookup_hash (GuestAddrs.mpt_walk + 816)),
    .AUIPC .x13 (laHi GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 824)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 824)),
    .AUIPC .x14 (laHi GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 832)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 832)),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840)),
    .BNE .x10 .x0 (356 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 848)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 848)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 864)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 864)),
    .LD .x24 .x5 (0 : BitVec 12),
    .JAL .x0 (-696 : BitVec 21),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 892)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 892)),
    .AUIPC .x14 (laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 900)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 900)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 908)),
    .BNE .x10 .x0 (288 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 916)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 916)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x10 .x23 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 932)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 932)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 944)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 944)),
    .AUIPC .x13 (laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 952)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 952)),
    .AUIPC .x14 (laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 960)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 960)),
    .JAL .x1 (jalOff GuestAddrs.hp_decode_nibbles (GuestAddrs.mpt_walk + 968)),
    .BNE .x10 .x0 (228 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 976)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 976)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (208 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 996)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 996)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SUB .x7 .x19 .x22,
    .BNE .x6 .x7 (176 : BitVec 13),
    .AUIPC .x7 (laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 1016)),
    .ADDI .x7 .x7 (laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 1016)),
    .ADD .x28 .x18 .x22,
    .MV .x29 .x6,
    .BEQ .x29 .x0 (32 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .BNE .x30 .x31 (144 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_value_offset (GuestAddrs.mpt_walk + 1076)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_value_offset (GuestAddrs.mpt_walk + 1076)),
    .AUIPC .x14 (laHi GuestAddrs.mw_value_length (GuestAddrs.mpt_walk + 1084)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_value_length (GuestAddrs.mpt_walk + 1084)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 1092)),
    .BNE .x10 .x0 (104 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_value_length (GuestAddrs.mpt_walk + 1100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_value_length (GuestAddrs.mpt_walk + 1100)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x21 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mw_value_offset (GuestAddrs.mpt_walk + 1116)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_value_offset (GuestAddrs.mpt_walk + 1116)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x7 .x23 .x7,
    .MV .x28 .x20,
    .LI .x29 (256 : Word),
    .BLTU .x29 .x6 (8 : BitVec 13),
    .JAL .x0 (8 : BitVec 21),
    .MV .x6 .x29,
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x5 .x7 (0 : BitVec 12),
    .SB .x28 .x5 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (1 : Word),
    .SD .x21 .x0 (0 : BitVec 12),
    .JAL .x0 (12 : BitVec 21),
    .LI .x10 (2 : Word),
    .SD .x21 .x0 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptWalk_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptWalk_relocs : RelocTable :=
  [ (17, .la .x5 "mw_lookup_hash"),
    (29, .la .x12 "mw_lookup_hash"),
    (31, .la .x13 "mw_lookup_offset"),
    (33, .la .x14 "mw_lookup_length"),
    (35, .jal .x1 "witness_lookup_by_hash"),
    (37, .la .x5 "mw_lookup_offset"),
    (41, .la .x5 "mw_lookup_length"),
    (47, .jal .x1 "mpt_node_kind"),
    (60, .la .x13 "mw_child_offset"),
    (62, .la .x14 "mw_child_length"),
    (64, .jal .x1 "rlp_list_nth_item"),
    (67, .la .x5 "mw_child_length"),
    (73, .la .x5 "mw_child_offset"),
    (79, .la .x5 "mw_child_offset"),
    (83, .la .x28 "mw_lookup_hash"),
    (95, .la .x12 "mw_lookup_hash"),
    (97, .la .x13 "mw_lookup_offset"),
    (99, .la .x14 "mw_lookup_length"),
    (101, .jal .x1 "witness_lookup_by_hash"),
    (103, .la .x5 "mw_lookup_offset"),
    (107, .la .x5 "mw_lookup_length"),
    (114, .la .x13 "mw_value_offset"),
    (116, .la .x14 "mw_value_length"),
    (118, .jal .x1 "rlp_list_nth_item"),
    (120, .la .x5 "mw_value_length"),
    (128, .la .x13 "mw_path_offset"),
    (130, .la .x14 "mw_path_length"),
    (132, .jal .x1 "rlp_list_nth_item"),
    (134, .la .x5 "mw_path_offset"),
    (138, .la .x5 "mw_path_length"),
    (141, .la .x12 "mw_nibble_buf"),
    (143, .la .x13 "mw_nibble_count"),
    (145, .la .x14 "mw_is_leaf"),
    (147, .jal .x1 "hp_decode_nibbles"),
    (149, .la .x5 "mw_is_leaf"),
    (153, .la .x5 "mw_nibble_count"),
    (158, .la .x7 "mw_nibble_buf"),
    (174, .la .x13 "mw_child_offset"),
    (176, .la .x14 "mw_child_length"),
    (178, .jal .x1 "rlp_list_nth_item"),
    (180, .la .x5 "mw_child_length"),
    (183, .la .x5 "mw_child_offset"),
    (192, .la .x29 "mw_lookup_hash"),
    (204, .la .x12 "mw_lookup_hash"),
    (206, .la .x13 "mw_lookup_offset"),
    (208, .la .x14 "mw_lookup_length"),
    (210, .jal .x1 "witness_lookup_by_hash"),
    (212, .la .x5 "mw_lookup_offset"),
    (216, .la .x5 "mw_lookup_length"),
    (223, .la .x13 "mw_path_offset"),
    (225, .la .x14 "mw_path_length"),
    (227, .jal .x1 "rlp_list_nth_item"),
    (229, .la .x5 "mw_path_offset"),
    (233, .la .x5 "mw_path_length"),
    (236, .la .x12 "mw_nibble_buf"),
    (238, .la .x13 "mw_nibble_count"),
    (240, .la .x14 "mw_is_leaf"),
    (242, .jal .x1 "hp_decode_nibbles"),
    (244, .la .x5 "mw_is_leaf"),
    (249, .la .x5 "mw_nibble_count"),
    (254, .la .x7 "mw_nibble_buf"),
    (269, .la .x13 "mw_value_offset"),
    (271, .la .x14 "mw_value_length"),
    (273, .jal .x1 "rlp_list_nth_item"),
    (275, .la .x5 "mw_value_length"),
    (279, .la .x5 "mw_value_offset") ]

def mptWalkFunction : String :=
  "mpt_walk:\n" ++ emitProgramR mptWalk_prog mptWalk_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptWalk_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptWalkFunction_eq_prog :
    mptWalkFunction = "mpt_walk:\n" ++ emitProgramR mptWalk_prog mptWalk_relocs := rfl

#guard mptWalkFunction.startsWith "mpt_walk:\n"
#guard mptWalk_prog.length = 314
/-- `zisk_mpt_walk`: probe BuildUnit. Reads
    (witness_len, path_len, root_hash, path_nibbles,
     witness_bytes) from host input, writes
    (status, value_len, value_bytes) to OUTPUT.
    Input layout:
      bytes   0..  8 : witness_len (u64)
      bytes   8.. 16 : path_len (u64)
      bytes  16.. 48 : root_hash (32 bytes)
      bytes  48..   : path_nibbles bytes (path_len of them)
      bytes  48 + path_len .. : witness section bytes
    Output layout:
      bytes   0.. 8 : status (0 found / 1 not / 2 fail)
      bytes   8..16 : value_len
      bytes  16..   : value bytes (up to 256 - 16 = 240) -/
def ziskMptWalkPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # path_len\n" ++
  "  addi a0, a7, 24             # root_hash ptr (offset 16 from start of file)\n" ++
  "  addi a3, a7, 56             # path_nibbles ptr (offset 48)\n" ++
  "  # witness ptr = path_nibbles + path_len.\n" ++
  "  add a1, a3, t5\n" ++
  "  mv a2, t6                   # witness_len\n" ++
  "  mv a4, t5                   # path_len\n" ++
  "  li a5, 0xa0010010           # value buf at OUTPUT + 16\n" ++
  "  li a6, 0xa0010008           # value_len ptr at OUTPUT + 8\n" ++
  "  jal ra, mpt_walk\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lmw_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  ".Lmw_pdone:"

def ziskMptWalkDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  -- A state-witness node is SSZ ByteList[1024] (checked by the entry decoder).
  -- HP decoding emits at most 2 * 1024 - 1 = 2047 one-byte nibbles.
  "  .zero 2048"

def ziskMptWalkProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptWalkPrologue
  dataAsm     := ziskMptWalkDataSection
}

/-! ## bytes_to_nibbles -- PR-K25 byte → nibble array expansion

    Convert N bytes into 2N nibbles (one byte per nibble, in
    [0..15]). Each input byte writes 2 output bytes: high nibble
    then low nibble. The output format matches what `mpt_walk`
    (PR-K24) consumes as its path argument.

    Composes with `zkvm_keccak256` to derive the standard MPT
    path from a state-trie or storage-trie key:

        keccak256(address)   -- 32 bytes
        bytes_to_nibbles     -- 64 nibbles
        mpt_walk(...)        -- account / slot lookup

    Calling convention:
      a0 (input)  : src bytes ptr
      a1 (input)  : src byte length
      a2 (input)  : dst nibble buf ptr (2 * a1 bytes)
      ra (input)  : return
      a0 (output) : 2 * a1 (number of nibbles emitted)

    Pure register arithmetic, no scratch memory, leaf-callable. -/
def bytesToNibbles_prog : Program :=
  [ .MV .x5 .x10,
    .MV .x6 .x12,
    .MV .x7 .x11,
    .LI .x31 (0 : Word),
    .BEQ .x7 .x0 (44 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SRLI .x29 .x28 (4 : BitVec 6),
    .ANDI .x30 .x28 (15 : BitVec 12),
    .SB .x6 .x29 (0 : BitVec 12),
    .SB .x6 .x30 (1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (2 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .ADDI .x31 .x31 (2 : BitVec 12),
    .JAL .x0 (-40 : BitVec 21),
    .MV .x10 .x31,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bytesToNibblesFunction : String :=
  "bytes_to_nibbles:\n" ++ emitProgram bytesToNibbles_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bytesToNibbles_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bytesToNibblesFunction_eq_prog :
    bytesToNibblesFunction = "bytes_to_nibbles:\n" ++ emitProgram bytesToNibbles_prog := rfl

#guard bytesToNibblesFunction.startsWith "bytes_to_nibbles:\n"
#guard bytesToNibbles_prog.length = 17
/-- `zisk_bytes_to_nibbles`: probe BuildUnit. Reads
    (src_len, src_bytes) from host input, writes
    (nibble_count, nibbles) to OUTPUT.
    Input layout:
      bytes  0.. 8 : src_len (u64)
      bytes  8..   : src bytes
    Output layout:
      bytes  0.. 8 : nibble_count (u64 = 2 * src_len)
      bytes  8..   : nibble bytes -/
def ziskBytesToNibblesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # src_len\n" ++
  "  addi a0, a3, 16             # src bytes ptr\n" ++
  "  li a2, 0xa0010008           # nibble buf at OUTPUT + 8\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # nibble_count at OUTPUT + 0\n" ++
  "  j .Lbtn_pdone\n" ++
  bytesToNibblesFunction ++ "\n" ++
  ".Lbtn_pdone:"

def ziskBytesToNibblesDataSection : String :=
  ".section .data\n" ++
  "btn_pad:\n" ++
  "  .zero 8"

def ziskBytesToNibblesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBytesToNibblesPrologue
  dataAsm     := ziskBytesToNibblesDataSection
}

/-! ## mpt_lookup_by_key -- PR-K26 keccak + nibbles + mpt_walk

    Compose the lookup chain that turns a raw key (address or
    storage slot index) into a value via Ethereum's standard
    `keccak256(key) -> path -> mpt_walk(...)` shape.

    Both Ethereum state and storage tries use this same shape;
    only the value semantics differ (account RLP vs 32-byte
    storage word).

    Calling convention:
      a0 (input)  : key bytes ptr (20-byte address or 32-byte
                    storage slot index, big-endian)
      a1 (input)  : key byte length
      a2 (input)  : root_hash ptr (32 bytes)
      a3 (input)  : witness section ptr
      a4 (input)  : witness section_len
      a5 (input)  : value output buffer ptr (256 bytes)
      a6 (input)  : u64 out ptr (matched value byte length)
      ra (input)  : return
      a0 (output) : 0 found / 1 not found / 2 parse error
                    (mirrors mpt_walk return codes).

    Internal scratch buffers:
      mlk_keccak_buf : 32 bytes (keccak256 output)
      mlk_nibble_buf : 64 bytes (one nibble per byte) -/
def mptLookupByKey_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x12,
    .MV .x9 .x13,
    .MV .x18 .x14,
    .MV .x19 .x15,
    .MV .x20 .x16,
    .AUIPC .x12 (laHi GuestAddrs.mlk_keccak_buf (GuestAddrs.mpt_lookup_by_key + 48)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mlk_keccak_buf (GuestAddrs.mpt_lookup_by_key + 48)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.mpt_lookup_by_key + 56)),
    .AUIPC .x10 (laHi GuestAddrs.mlk_keccak_buf (GuestAddrs.mpt_lookup_by_key + 60)),
    .ADDI .x10 .x10 (laLo GuestAddrs.mlk_keccak_buf (GuestAddrs.mpt_lookup_by_key + 60)),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.mlk_nibble_buf (GuestAddrs.mpt_lookup_by_key + 72)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mlk_nibble_buf (GuestAddrs.mpt_lookup_by_key + 72)),
    .JAL .x1 (jalOff GuestAddrs.bytes_to_nibbles (GuestAddrs.mpt_lookup_by_key + 80)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .AUIPC .x13 (laHi GuestAddrs.mlk_nibble_buf (GuestAddrs.mpt_lookup_by_key + 96)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mlk_nibble_buf (GuestAddrs.mpt_lookup_by_key + 96)),
    .LI .x14 (64 : Word),
    .MV .x15 .x19,
    .MV .x16 .x20,
    .JAL .x1 (jalOff GuestAddrs.mpt_walk (GuestAddrs.mpt_lookup_by_key + 116)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptLookupByKey_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptLookupByKey_relocs : RelocTable :=
  [ (12, .la .x12 "mlk_keccak_buf"),
    (14, .jal .x1 "zkvm_keccak256"),
    (15, .la .x10 "mlk_keccak_buf"),
    (18, .la .x12 "mlk_nibble_buf"),
    (20, .jal .x1 "bytes_to_nibbles"),
    (24, .la .x13 "mlk_nibble_buf"),
    (29, .jal .x1 "mpt_walk") ]

def mptLookupByKeyFunction : String :=
  "mpt_lookup_by_key:\n" ++ emitProgramR mptLookupByKey_prog mptLookupByKey_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptLookupByKey_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptLookupByKeyFunction_eq_prog :
    mptLookupByKeyFunction = "mpt_lookup_by_key:\n" ++ emitProgramR mptLookupByKey_prog mptLookupByKey_relocs := rfl

#guard mptLookupByKeyFunction.startsWith "mpt_lookup_by_key:\n"
#guard mptLookupByKey_prog.length = 38
/-- `zisk_mpt_lookup_by_key`: probe BuildUnit. Reads
    (witness_len, key_len, root_hash, key, witness) from host
    input and writes (status, value_len, value_bytes) to OUTPUT.
    Input layout:
      bytes   0.. 8 : witness_len (u64)
      bytes   8..16 : key_len (u64)
      bytes  16..48 : root_hash (32 bytes)
      bytes  48..   : key bytes (key_len)
      bytes  48+key_len.. : witness section bytes
    Output: same as PR-K24 mpt_walk. -/
def ziskMptLookupByKeyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # key_len\n" ++
  "  addi a2, a7, 24             # root_hash ptr (input offset 16)\n" ++
  "  addi a0, a7, 56             # key ptr (input offset 48)\n" ++
  "  mv a1, t5                   # key_len\n" ++
  "  add a3, a0, t5              # witness ptr = key + key_len\n" ++
  "  mv a4, t6                   # witness_len\n" ++
  "  li a5, 0xa0010010           # value buf at OUTPUT + 16\n" ++
  "  li a6, 0xa0010008           # value_len at OUTPUT + 8\n" ++
  "  jal ra, mpt_lookup_by_key\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lmlk_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  ".Lmlk_pdone:"

def ziskMptLookupByKeyDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 2048\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64"

def ziskMptLookupByKeyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptLookupByKeyPrologue
  dataAsm     := ziskMptLookupByKeyDataSection
}


/-! ## hp_encode_nibbles -- PR-K32 inverse of hp_decode_nibbles

    Encode a nibble array + leaf/extension flag into the HP
    byte string format used as the first item of MPT leaf and
    extension nodes. Inverse of PR-K23 `hp_decode_nibbles`.

    HP encoding rules:
      flag = (is_leaf ? 2 : 0) + (is_odd_nibble_count ? 1 : 0)
      byte 0 = (flag << 4) | (first_nibble if odd else 0)
      bytes 1.. = remaining nibble pairs (high then low)

    Output length:
      even nibble count: 1 + nibble_count / 2 bytes
      odd  nibble count: 1 + (nibble_count - 1) / 2 bytes
                       = ceil(nibble_count / 2) + (0 or 1)

    Or more uniformly: ceil((nibble_count + 2) / 2) bytes.

    Calling convention:
      a0 (input)  : nibbles ptr (1 byte per nibble, low 4 bits)
      a1 (input)  : nibble count
      a2 (input)  : is_leaf flag (0 = extension, 1 = leaf)
      a3 (input)  : output byte buffer ptr
      ra (input)  : return
      a0 (output) : number of bytes written

    Pure register arithmetic, no scratch, leaf-callable. -/
def hpEncodeNibbles_prog : Program :=
  [ .ANDI .x5 .x11 (1 : BitVec 12),
    .MV .x6 .x13,
    .SLLI .x7 .x12 (1 : BitVec 6),
    .OR .x7 .x7 .x5,
    .SLLI .x7 .x7 (4 : BitVec 6),
    .BEQ .x5 .x0 (32 : BitVec 13),
    .LBU .x28 .x10 (0 : BitVec 12),
    .OR .x7 .x7 .x28,
    .SB .x6 .x7 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (-1 : BitVec 12),
    .JAL .x0 (12 : BitVec 21),
    .SB .x6 .x7 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .BEQ .x11 .x0 (40 : BitVec 13),
    .LBU .x28 .x10 (0 : BitVec 12),
    .SLLI .x28 .x28 (4 : BitVec 6),
    .LBU .x29 .x10 (1 : BitVec 12),
    .OR .x28 .x28 .x29,
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x10 .x10 (2 : BitVec 12),
    .ADDI .x11 .x11 (-2 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .SUB .x10 .x6 .x13,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def hpEncodeNibblesFunction : String :=
  "hp_encode_nibbles:\n" ++ emitProgram hpEncodeNibbles_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `hpEncodeNibbles_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem hpEncodeNibblesFunction_eq_prog :
    hpEncodeNibblesFunction = "hp_encode_nibbles:\n" ++ emitProgram hpEncodeNibbles_prog := rfl

#guard hpEncodeNibblesFunction.startsWith "hp_encode_nibbles:\n"
#guard hpEncodeNibbles_prog.length = 27
/-- `zisk_hp_encode_nibbles`: probe BuildUnit. Reads
    (nibble_count, is_leaf, nibbles) from host input, writes
    (bytes_written, hp_bytes) to OUTPUT.
    Input layout:
      bytes  0.. 8 : nibble_count (u64)
      bytes  8..16 : is_leaf (u64; 0 or 1)
      bytes 16..   : nibble bytes (each in [0..15]) -/
def ziskHpEncodeNibblesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # nibble_count\n" ++
  "  ld a2, 16(a4)               # is_leaf\n" ++
  "  addi a0, a4, 24             # nibbles ptr\n" ++
  "  li a3, 0xa0010008           # output at OUTPUT + 8\n" ++
  "  jal ra, hp_encode_nibbles\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # bytes_written\n" ++
  "  j .Lhpe_pdone\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  ".Lhpe_pdone:"

def ziskHpEncodeNibblesDataSection : String :=
  ".section .data\n" ++
  "hpe_pad:\n" ++
  "  .zero 8"

def ziskHpEncodeNibblesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHpEncodeNibblesPrologue
  dataAsm     := ziskHpEncodeNibblesDataSection
}



end EvmAsm.Codegen
