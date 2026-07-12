/-
  EvmAsm.Codegen.Programs.SszParentHeader

  extract_parent_header_and_state_root (bead evm-asm-fhsxz.2.4.2.4): the last
  SSZ-input extractor the Step-2 verdict needs. The recompute starts from the
  PARENT block's state_root, and validate_header_rlp_pair needs the parent
  header RLP. Both come from the witness `headers` section (a List[ByteList]
  of RLP headers): find the one whose keccak256 equals `this.parent_hash`, and
  read its state_root (field 3).

  Navigation:
    witness     = SSZ_BASE + outer.offsets[1]
    witness_end = SSZ_BASE + outer.offsets[2]
    headers_ptr = witness + witness.inner.offsets[2]
    headers_len = witness_end - headers_ptr
  Then witness_lookup_by_hash(headers_ptr, headers_len, this.parent_hash)
  locates the parent header (it keccaks each List[ByteList] element and
  compares), and header_extract_state_root(parent) copies field 3.

  Composes already-merged primitives (witness_lookup_by_hash,
  header_extract_state_root); u32 offsets read byte-wise (no-misaligned).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.MptWitnessLookup
import EvmAsm.Codegen.Programs.HeaderFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## eph_u32le -- read a little-endian u32 byte-wise (a0=ptr -> a0). Leaf. -/
def ephU32le_prog : Program :=
  [ .LBU .x5 .x10 (0 : BitVec 12),
    .LBU .x6 .x10 (1 : BitVec 12),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (2 : BitVec 12),
    .SLLI .x6 .x6 (16 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (3 : BitVec 12),
    .SLLI .x6 .x6 (24 : BitVec 6),
    .OR .x5 .x5 .x6,
    .MV .x10 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def ephU32leFunction : String :=
  "eph_u32le:\n" ++ emitProgram ephU32le_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `ephU32le_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem ephU32leFunction_eq_prog :
    ephU32leFunction = "eph_u32le:\n" ++ emitProgram ephU32le_prog := rfl

#guard ephU32leFunction.startsWith "eph_u32le:\n"
#guard ephU32le_prog.length = 12
/-- `extract_parent_header_and_state_root`.
    a0 = SSZ_BASE ptr            a1 = this.parent_hash ptr (32 B)
    a2 = out parent header ptr   a3 = out parent header length
    a4 = out parent state_root (32 B)
    a0 (output) = 0 (ok) / 1 (parent header not in witness) / 2 (state_root
    parse fail). -/
def extractParentHeaderAndStateRoot_prog : Program :=
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
    .ADDI .x10 .x8 (4 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.eph_u32le (GuestAddrs.extract_parent_header_and_state_root + 60)),
    .ADD .x21 .x8 .x10,
    .ADDI .x10 .x8 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.eph_u32le (GuestAddrs.extract_parent_header_and_state_root + 72)),
    .ADD .x22 .x8 .x10,
    .ADDI .x10 .x21 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.eph_u32le (GuestAddrs.extract_parent_header_and_state_root + 84)),
    .ADD .x8 .x21 .x10,
    .MV .x10 .x8,
    .SUB .x11 .x22 .x8,
    .MV .x12 .x9,
    .AUIPC .x13 (laHi GuestAddrs.eph_off (GuestAddrs.extract_parent_header_and_state_root + 104)),
    .ADDI .x13 .x13 (laLo GuestAddrs.eph_off (GuestAddrs.extract_parent_header_and_state_root + 104)),
    .AUIPC .x14 (laHi GuestAddrs.eph_len (GuestAddrs.extract_parent_header_and_state_root + 112)),
    .ADDI .x14 .x14 (laLo GuestAddrs.eph_len (GuestAddrs.extract_parent_header_and_state_root + 112)),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.extract_parent_header_and_state_root + 120)),
    .BNE .x10 .x0 (68 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.eph_off (GuestAddrs.extract_parent_header_and_state_root + 128)),
    .ADDI .x5 .x5 (laLo GuestAddrs.eph_off (GuestAddrs.extract_parent_header_and_state_root + 128)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.eph_len (GuestAddrs.extract_parent_header_and_state_root + 144)),
    .ADDI .x5 .x5 (laLo GuestAddrs.eph_len (GuestAddrs.extract_parent_header_and_state_root + 144)),
    .LD .x28 .x5 (0 : BitVec 12),
    .SD .x18 .x7 (0 : BitVec 12),
    .SD .x19 .x28 (0 : BitVec 12),
    .MV .x10 .x7,
    .MV .x11 .x28,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (GuestAddrs.extract_parent_header_and_state_root + 176)),
    .BEQ .x10 .x0 (16 : BitVec 13),
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

/-- Reloc side-table for `extractParentHeaderAndStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def extractParentHeaderAndStateRoot_relocs : RelocTable :=
  [ (15, .jal .x1 "eph_u32le"),
    (18, .jal .x1 "eph_u32le"),
    (21, .jal .x1 "eph_u32le"),
    (26, .la .x13 "eph_off"),
    (28, .la .x14 "eph_len"),
    (30, .jal .x1 "witness_lookup_by_hash"),
    (32, .la .x5 "eph_off"),
    (36, .la .x5 "eph_len"),
    (44, .jal .x1 "header_extract_state_root") ]

def extractParentHeaderAndStateRootFunction : String :=
  "extract_parent_header_and_state_root:\n" ++ emitProgramR extractParentHeaderAndStateRoot_prog extractParentHeaderAndStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `extractParentHeaderAndStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem extractParentHeaderAndStateRootFunction_eq_prog :
    extractParentHeaderAndStateRootFunction = "extract_parent_header_and_state_root:\n" ++ emitProgramR extractParentHeaderAndStateRoot_prog extractParentHeaderAndStateRoot_relocs := rfl

#guard extractParentHeaderAndStateRootFunction.startsWith "extract_parent_header_and_state_root:\n"
#guard extractParentHeaderAndStateRoot_prog.length = 59
/-- `zisk_extract_parent_header_and_state_root`: probe. Input file (-> INPUT+8):
      bytes 0..32 : this.parent_hash
      bytes 32..  : SszStatelessInput SSZ blob (SSZ_BASE = INPUT+40 for the probe)
    Output: OUTPUT+0 = status, OUTPUT+8 = parent header length,
    OUTPUT+16 = parent state_root (32 B). -/
def ziskExtractParentHeaderPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a1, t0, 8              # this.parent_hash (INPUT+8)\n" ++
  "  addi a0, t0, 40             # SSZ_BASE (INPUT+40)\n" ++
  "  la a2, eph_hdr_ptr; la a3, eph_hdr_len; la a4, eph_state_root\n" ++
  "  jal ra, extract_parent_header_and_state_root\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)         # status\n" ++
  "  la t0, eph_hdr_len; ld t1, 0(t0); li t2, 0xa0010008; sd t1, 0(t2)\n" ++
  "  # copy state_root (32B) to OUTPUT+16\n" ++
  "  la t0, eph_state_root; li t1, 0xa0010010\n" ++
  "  ld t2, 0(t0); sd t2, 0(t1); ld t2, 8(t0); sd t2, 8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  j .Leph_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  ephU32leFunction ++ "\n" ++
  extractParentHeaderAndStateRootFunction ++ "\n" ++
  ".Leph_pdone:"

def ziskExtractParentHeaderDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n  .zero 8\n" ++
  "hesr_length:\n  .zero 8\n" ++
  "eph_off:\n  .zero 8\n" ++
  "eph_len:\n  .zero 8\n" ++
  "eph_hdr_ptr:\n  .zero 8\n" ++
  "eph_hdr_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "eph_state_root:\n  .zero 32"

def ziskExtractParentHeaderProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskExtractParentHeaderPrologue
  dataAsm     := ziskExtractParentHeaderDataSection
}

end EvmAsm.Codegen
