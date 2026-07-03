/-
  EvmAsm.Codegen.Programs.BlockAccessListHash

  block_access_list_hash (bead evm-asm-fhsxz.2.4.2.5): compute the Amsterdam RLP
  header field `block_access_list_hash` (field 21 of 23) = keccak256 of the raw
  `block_access_list` section bytes in the SSZ ExecutionPayload. Verified against
  real zkevm@v0.4.0 fixtures (the fixture blockHeader's blockAccessListHash).

  This is a prerequisite for `block_hash` verification (reconstruct the full
  23-field Amsterdam header and check keccak == payload.block_hash), the
  cornerstone of a SOUND Step-2 verdict that can be wired into the guest without
  false-positive regressions.

  Navigation (all byte-wise; no-misaligned invariant):
    NPR          = SSZ_BASE + 16          (outer.offsets[0] is 16 for this schema)
    exec_payload = NPR + 44               (NPR fixed header)
    bal_off      = u32 @ exec_payload+528 (block_access_list offset, rel exec_payload)
    vh_off       = u32 @ NPR+4            (versioned_hashes offset, rel NPR = payload end)
    bal_start    = exec_payload + bal_off
    bal_end      = NPR + vh_off           (= exec_payload end)
  block_access_list_hash = keccak256(bal_start .. bal_end).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bah_u32le -- read a little-endian u32 byte-wise (a0=ptr -> a0). Leaf. -/
def bahU32le_prog : Program :=
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

def bahU32leFunction : String :=
  "bah_u32le:\n" ++ emitProgram bahU32le_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bahU32le_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bahU32leFunction_eq_prog :
    bahU32leFunction = "bah_u32le:\n" ++ emitProgram bahU32le_prog := rfl

#guard bahU32leFunction.startsWith "bah_u32le:\n"
#guard bahU32le_prog.length = 12
/-! ## block_access_list_hash
    a0 = SSZ_BASE ptr   a1 = 32-byte out hash ptr.   a0 (output) = 0. -/
def blockAccessListHash_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .ADDI .x18 .x8 (16 : BitVec 12),
    .ADDI .x28 .x18 (44 : BitVec 12),
    .ADDI .x10 .x28 (528 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bah_u32le (GuestAddrs.block_access_list_hash + 40)),
    .ADDI .x28 .x18 (44 : BitVec 12),
    .ADD .x29 .x28 .x10,
    .AUIPC .x5 (laHi GuestAddrs.bah_bal_start (GuestAddrs.block_access_list_hash + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bah_bal_start (GuestAddrs.block_access_list_hash + 52)),
    .SD .x5 .x29 (0 : BitVec 12),
    .ADDI .x10 .x18 (4 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bah_u32le (GuestAddrs.block_access_list_hash + 68)),
    .ADD .x30 .x18 .x10,
    .AUIPC .x5 (laHi GuestAddrs.bah_bal_start (GuestAddrs.block_access_list_hash + 76)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bah_bal_start (GuestAddrs.block_access_list_hash + 76)),
    .LD .x29 .x5 (0 : BitVec 12),
    .SUB .x11 .x30 .x29,
    .MV .x10 .x29,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.block_access_list_hash + 100)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockAccessListHash_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockAccessListHash_relocs : RelocTable :=
  [ (10, .jal .x1 "bah_u32le"),
    (13, .la .x5 "bah_bal_start"),
    (17, .jal .x1 "bah_u32le"),
    (19, .la .x5 "bah_bal_start"),
    (25, .jal .x1 "zkvm_keccak256") ]

def blockAccessListHashFunction : String :=
  "block_access_list_hash:\n" ++ emitProgramR blockAccessListHash_prog blockAccessListHash_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockAccessListHash_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockAccessListHashFunction_eq_prog :
    blockAccessListHashFunction = "block_access_list_hash:\n" ++ emitProgramR blockAccessListHash_prog blockAccessListHash_relocs := rfl

#guard blockAccessListHashFunction.startsWith "block_access_list_hash:\n"
#guard blockAccessListHash_prog.length = 33
/-- `zisk_block_access_list_hash`: probe. Fed the SAME `-i` input as the guest
    (SSZ_BASE = 0x40000012). Output: OUTPUT+0 = block_access_list_hash (32 B). -/
def ziskBlockAccessListHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a0, 0x40000000; addi a0, a0, 18    # SSZ_BASE\n" ++
  "  li a1, 0xa0010000\n" ++
  "  jal ra, block_access_list_hash\n" ++
  "  j .Lbah_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bahU32leFunction ++ "\n" ++
  blockAccessListHashFunction ++ "\n" ++
  ".Lbah_pdone:"

def ziskBlockAccessListHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  ".balign 8\n" ++
  "bah_bal_start:\n  .zero 8"

def ziskBlockAccessListHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockAccessListHashPrologue
  dataAsm     := ziskBlockAccessListHashDataSection
}

end EvmAsm.Codegen
