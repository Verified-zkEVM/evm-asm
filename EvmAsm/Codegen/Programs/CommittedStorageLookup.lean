/-
  EvmAsm.Codegen.Programs.CommittedStorageLookup

  Bounded consumer-side helper for the cross-transaction committed-storage table.
  It prepares the recipient/slot query exactly like the previous inline
  dispatch path, rejects counts above the named capacity, and delegates the
  last-match scan to `exec_log_latest_value`.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.ExecLogLatestValue

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bv_mtx_committed_chunked_latest_value
    a0 = recipient ptr (20B, block context address)
    a1 = slotKey ptr (32B big-endian BAL key)
    a2 = chunked committed table base (128B entries, contiguous pages)
    a3 = committed table count across all chunks
    a4 = committed table total capacity
    a5 = out value ptr (32B; written on match)
    a6 = recipient scratch ptr (32B)
    a7 = slot scratch ptr (32B)
    returns:
      a0 = 0 no match, 1 found, 2 count exceeds capacity

    The chunked table preserves the 128-byte committed-map entry layout, so the
    lookup normalizes the query key and delegates to
    `exec_log_latest_value` over the populated contiguous prefix. Duplicate
    matches across page boundaries preserve last-wins semantics. -/
def bvMtxCommittedChunkedLatestValue_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .BLTU .x14 .x13 (144 : BitVec 13),
    .MV .x8 .x15,
    .MV .x9 .x16,
    .MV .x18 .x17,
    .SD .x9 .x0 (0 : BitVec 12),
    .SD .x9 .x0 (8 : BitVec 12),
    .SD .x9 .x0 (16 : BitVec 12),
    .SD .x9 .x0 (24 : BitVec 12),
    .LI .x5 (0 : Word),
    .LI .x6 (20 : Word),
    .BEQ .x5 .x6 (28 : BitVec 13),
    .ADD .x7 .x10 .x5,
    .LBU .x28 .x7 (0 : BitVec 12),
    .ADD .x7 .x9 .x5,
    .SB .x7 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x5 .x11 (31 : BitVec 12),
    .MV .x6 .x18,
    .LI .x7 (32 : Word),
    .BEQ .x7 .x0 (28 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .MV .x14 .x8,
    .JAL .x1 (jalOff GuestAddrs.exec_log_latest_value (GuestAddrs.bv_mtx_committed_chunked_latest_value + 140)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bvMtxCommittedChunkedLatestValue_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bvMtxCommittedChunkedLatestValue_relocs : RelocTable :=
  [ (35, .jal .x1 "exec_log_latest_value") ]

def committedStorageChunkedLatestValueFunction : String :=
  "bv_mtx_committed_chunked_latest_value:\n" ++ emitProgramR bvMtxCommittedChunkedLatestValue_prog bvMtxCommittedChunkedLatestValue_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bvMtxCommittedChunkedLatestValue_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem committedStorageChunkedLatestValueFunction_eq_prog :
    committedStorageChunkedLatestValueFunction = "bv_mtx_committed_chunked_latest_value:\n" ++ emitProgramR bvMtxCommittedChunkedLatestValue_prog bvMtxCommittedChunkedLatestValue_relocs := rfl

#guard committedStorageChunkedLatestValueFunction.startsWith "bv_mtx_committed_chunked_latest_value:\n"
#guard bvMtxCommittedChunkedLatestValue_prog.length = 48
/-- `zisk_mtx_committed_chunked_latest_value`: focused probe.
    Input after ziskemu's length wrapper:
      +8 mode: 0 empty, 1 no-match, 2 chunk0 match, 3 chunk1 match,
          4 duplicate latest in later chunk, 5 over-capacity
    Output:
      +0 returned status
      +8 output value low word
      +16 recipient scratch low word
      +24 slot scratch low word -/
def ziskCommittedStorageChunkedLookupPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  li t6, 0x40000000; ld s1, 8(t6)\n" ++
  "  la t0, cscl_recipient; li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0)\n" ++
  "  la t0, cscl_key_be; li t1, 7; sb t1, 31(t0)\n" ++
  "  la t0, cscl_out; li t1, 0xEE; sd t1, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t0, cscl_table\n" ++
  "  li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0); li t1, 9; sd t1, 32(t0); li t1, 0x55; sd t1, 96(t0)\n" ++
  "  addi t0, t0, 128; li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0); li t1, 7; sd t1, 32(t0); li t1, 0x11; sd t1, 96(t0)\n" ++
  "  la t0, cscl_table; li t1, 16512; add t0, t0, t1; li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0); li t1, 7; sd t1, 32(t0); li t1, 0x77; sd t1, 96(t0)\n" ++
  "  li a3, 0; li a4, 512\n" ++
  "  beqz s1, .Lcscl_call\n" ++
  "  li t0, 1; beq s1, t0, .Lcscl_no_match\n" ++
  "  li t0, 2; beq s1, t0, .Lcscl_chunk0\n" ++
  "  li t0, 3; beq s1, t0, .Lcscl_chunk1\n" ++
  "  li t0, 4; beq s1, t0, .Lcscl_duplicate\n" ++
  "  li a3, 513; j .Lcscl_call\n" ++
  ".Lcscl_no_match:\n  li a3, 1; j .Lcscl_call\n" ++
  ".Lcscl_chunk0:\n  li a3, 2; j .Lcscl_call\n" ++
  ".Lcscl_chunk1:\n" ++
  "  la t0, cscl_key_be; li t1, 8; sb t1, 31(t0)\n" ++
  "  la t0, cscl_table; li t1, 16512; add t0, t0, t1; li t1, 8; sd t1, 32(t0)\n" ++
  "  li a3, 130; j .Lcscl_call\n" ++
  ".Lcscl_duplicate:\n  li a3, 130\n" ++
  ".Lcscl_call:\n" ++
  "  la a0, cscl_recipient; la a1, cscl_key_be; la a2, cscl_table; la a5, cscl_out; la a6, cscl_recip_scratch; la a7, cscl_slot_scratch\n" ++
  "  jal ra, bv_mtx_committed_chunked_latest_value\n" ++
  "  sd a0, 0(s0); la t0, cscl_out; ld t1, 0(t0); sd t1, 8(s0); la t0, cscl_recip_scratch; ld t1, 0(t0); sd t1, 16(s0); la t0, cscl_slot_scratch; ld t1, 0(t0); sd t1, 24(s0)\n" ++
  "  j .Lcscl_done\n" ++
  committedStorageChunkedLatestValueFunction ++ "\n" ++
  execLogLatestValueFunction ++ "\n" ++
  ".Lcscl_done:"

def ziskCommittedStorageChunkedLookupDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "cscl_table:\n  .zero 65536\n" ++
  "cscl_recipient:\n  .zero 32\n" ++
  "cscl_key_be:\n  .zero 32\n" ++
  "cscl_out:\n  .zero 32\n" ++
  "cscl_recip_scratch:\n  .zero 32\n" ++
  "cscl_slot_scratch:\n  .zero 32\n"

def ziskCommittedStorageChunkedLookupProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCommittedStorageChunkedLookupPrologue
  dataAsm     := ziskCommittedStorageChunkedLookupDataSection
}

end EvmAsm.Codegen
