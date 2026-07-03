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
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
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
def extractParentHeaderAndStateRootFunction : String :=
  "extract_parent_header_and_state_root:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # SSZ_BASE\n" ++
  "  mv s1, a1                   # this.parent_hash\n" ++
  "  mv s2, a2                   # out hdr ptr\n" ++
  "  mv s3, a3                   # out hdr len\n" ++
  "  mv s4, a4                   # out state_root\n" ++
  "  # witness = SSZ_BASE + outer.offsets[1]\n" ++
  "  addi a0, s0, 4\n" ++
  "  jal ra, eph_u32le\n" ++
  "  add s5, s0, a0              # s5 = witness\n" ++
  "  # witness_end = SSZ_BASE + outer.offsets[2]\n" ++
  "  addi a0, s0, 8\n" ++
  "  jal ra, eph_u32le\n" ++
  "  add s6, s0, a0              # s6 = witness_end\n" ++
  "  # headers_ptr = witness + inner.offsets[2]\n" ++
  "  addi a0, s5, 8\n" ++
  "  jal ra, eph_u32le\n" ++
  "  add s0, s5, a0              # s0 = headers_ptr (SSZ_BASE no longer needed)\n" ++
  "  # find parent header: witness_lookup_by_hash(headers, len, parent_hash).\n" ++
  "  mv a0, s0\n" ++
  "  sub a1, s6, s0             # headers_len = witness_end - headers_ptr\n" ++
  "  mv a2, s1\n" ++
  "  la a3, eph_off; la a4, eph_len\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Leph_notfound\n" ++
  "  la t0, eph_off; ld t1, 0(t0); add t2, s0, t1   # parent_hdr_ptr\n" ++
  "  la t0, eph_len; ld t3, 0(t0)                   # parent_hdr_len\n" ++
  "  sd t2, 0(s2); sd t3, 0(s3)\n" ++
  "  # state_root = header_extract_state_root(parent_hdr_ptr, len).\n" ++
  "  mv a0, t2; mv a1, t3; mv a2, s4\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  # a0 = 0/1/2 from the extractor (1/2 => parse issue); map nonzero to 2.\n" ++
  "  beqz a0, .Leph_ret\n" ++
  "  li a0, 2\n" ++
  "  j .Leph_ret\n" ++
  ".Leph_notfound:\n" ++
  "  li a0, 1\n" ++
  ".Leph_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

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
