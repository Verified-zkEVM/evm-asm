/-
  EvmAsm.Codegen.Programs.MptTail

  Tail of the MPT program definitions, split to keep each Codegen/Programs
  module under the 1500-line file-size cap.
-/

import EvmAsm.Codegen.Programs.MptBase

namespace EvmAsm.Codegen

open EvmAsm.Rv64

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
