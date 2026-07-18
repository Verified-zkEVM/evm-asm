/-
  EvmAsm.Codegen.Programs.CommittedStorageBlockVerdictProbe

  Focused zisk probe for the block-verdict-facing chunked committed-storage
  globals. Unlike the helper-local probes, this uses the real
  `bv_mtx_committed_chunked`, `bv_mtx_committed_chunk_count`,
  `bv_mtx_committed_chunk_overflow`, `dtrc_threadval`, `dtrc_recipkey`, and
  `dtrc_slotkey_le` labels used by the stateless verdict v2 data section.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.CommittedStorageLookup
import EvmAsm.Codegen.Programs.CommittedStorageSnapshot
import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- `zisk_mtx_committed_block_verdict_threading`: block-verdict-facing probe.
    Input after ziskemu's length wrapper:
      +8 mode: 0 zero, 1 129 unique keys, 2 130 duplicate writes to one key,
          3 chunk-capacity overflow
    Output:
      +0  committed chunk count
      +8  upsert status
      +16 stored chunk overflow flag
      +24 lookup status for the queried key
      +32 lookup value low word
      +40 entry0 current low word
      +48 entry128 current low word
      +56 sentinel word after the chunked table (`dtrc_recipkey[0]`) -/
def ziskCommittedStorageBlockVerdictThreadingPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  li t6, 0x40000000; ld s1, 8(t6)\n" ++
  "  la t0, csg_recipient; li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0)\n" ++
  "  la t0, csg_key_be; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t0, csg_out; li t1, 0xEE; sd t1, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t0, bv_mtx_committed_chunk_count; sd zero, 0(t0); la t0, bv_mtx_committed_chunk_overflow; sd zero, 0(t0)\n" ++
  "  la t0, dtrc_recipkey; li t1, 0xEE; sd t1, 0(t0)\n" ++
  "  beqz s1, .Lcsg_query\n" ++
  "  li t0, 1; beq s1, t0, .Lcsg_unique129\n" ++
  "  li t0, 2; beq s1, t0, .Lcsg_duplicate130\n" ++
  "  j .Lcsg_overflow\n" ++
  ".Lcsg_unique129:\n" ++
  "  la t0, csg_live; li t2, 0\n" ++
  ".Lcsg_unique_loop:\n" ++
  "  li t3, 129; beq t2, t3, .Lcsg_unique_done\n" ++
  "  li t1, 0xBB; sb t1, 0(t0); li t1, 0xAA; sb t1, 19(t0); addi t1, t2, 1; sd t1, 32(t0); sd t1, 64(t0); sd t1, 96(t0)\n" ++
  "  addi t0, t0, 128; addi t2, t2, 1; j .Lcsg_unique_loop\n" ++
  ".Lcsg_unique_done:\n" ++
  "  la a0, csg_recipient; la a1, csg_live; li a2, 129; la a3, bv_mtx_committed_chunked\n" ++
  "  la t0, bv_mtx_committed_chunk_count; ld a4, 0(t0); li a5, 512; la a6, bv_mtx_committed_chunk_overflow\n" ++
  "  jal ra, bv_mtx_committed_chunked_snapshot_upsert\n" ++
  "  la t0, bv_mtx_committed_chunk_count; sd a0, 0(t0); sd a1, 8(s0)\n" ++
  "  la t0, csg_key_be; li t1, 129; sb t1, 31(t0); j .Lcsg_query\n" ++
  ".Lcsg_duplicate130:\n" ++
  "  la t0, csg_live; li t2, 0\n" ++
  ".Lcsg_dup_loop:\n" ++
  "  li t3, 130; beq t2, t3, .Lcsg_dup_done\n" ++
  "  li t1, 0xBB; sb t1, 0(t0); li t1, 0xAA; sb t1, 19(t0); li t1, 7; sd t1, 32(t0); sd t1, 64(t0); addi t1, t2, 1; sd t1, 96(t0)\n" ++
  "  addi t0, t0, 128; addi t2, t2, 1; j .Lcsg_dup_loop\n" ++
  ".Lcsg_dup_done:\n" ++
  "  la a0, csg_recipient; la a1, csg_live; li a2, 130; la a3, bv_mtx_committed_chunked\n" ++
  "  la t0, bv_mtx_committed_chunk_count; ld a4, 0(t0); li a5, 512; la a6, bv_mtx_committed_chunk_overflow\n" ++
  "  jal ra, bv_mtx_committed_chunked_snapshot_upsert\n" ++
  "  la t0, bv_mtx_committed_chunk_count; sd a0, 0(t0); sd a1, 8(s0)\n" ++
  "  la t0, csg_key_be; li t1, 7; sb t1, 31(t0); j .Lcsg_query\n" ++
  ".Lcsg_overflow:\n" ++
  "  la t0, csg_live; li t1, 0xBB; sb t1, 0(t0); li t1, 0xAA; sb t1, 19(t0); li t1, 1; sd t1, 32(t0); sd t1, 64(t0); li t1, 0x55; sd t1, 96(t0)\n" ++
  "  la t0, bv_mtx_committed_chunk_count; li t1, 512; sd t1, 0(t0)\n" ++
  "  la a0, csg_recipient; la a1, csg_live; li a2, 1; la a3, bv_mtx_committed_chunked\n" ++
  "  li a4, 512; li a5, 512; la a6, bv_mtx_committed_chunk_overflow\n" ++
  "  jal ra, bv_mtx_committed_chunked_snapshot_upsert\n" ++
  "  la t0, bv_mtx_committed_chunk_count; sd a0, 0(t0); sd a1, 8(s0)\n" ++
  ".Lcsg_query:\n" ++
  "  la t0, bv_mtx_committed_chunk_count; ld a3, 0(t0); sd a3, 0(s0)\n" ++
  "  la t0, bv_mtx_committed_chunk_overflow; ld t1, 0(t0); sd t1, 16(s0)\n" ++
  "  bnez t1, .Lcsg_no_lookup\n" ++
  "  beqz a3, .Lcsg_no_lookup\n" ++
  "  la a0, csg_recipient; la a1, csg_key_be; la a2, bv_mtx_committed_chunked; li a4, 512\n" ++
  "  la a5, csg_out; la a6, dtrc_recipkey; la a7, dtrc_slotkey_le\n" ++
  "  jal ra, bv_mtx_committed_chunked_latest_value; sd a0, 24(s0); j .Lcsg_dump\n" ++
  ".Lcsg_no_lookup:\n" ++
  "  sd zero, 24(s0)\n" ++
  ".Lcsg_dump:\n" ++
  "  la t0, csg_out; ld t1, 0(t0); sd t1, 32(s0)\n" ++
  "  la t0, bv_mtx_committed_chunked; ld t1, 96(t0); sd t1, 40(s0)\n" ++
  "  li t2, 16384; add t3, t0, t2; ld t1, 96(t3); sd t1, 48(s0)\n" ++
  "  la t0, dtrc_recipkey; ld t1, 0(t0); sd t1, 56(s0)\n" ++
  "  j .Lcsg_done\n" ++
  committedStorageChunkedSnapshotUpsertFunction ++ "\n" ++
  committedStorageChunkedLatestValueFunction ++ "\n" ++
  execLogLatestValueFunction ++ "\n" ++
  ".Lcsg_done:"

def ziskCommittedStorageBlockVerdictThreadingDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bv_mtx_committed_chunk_count:\n  .zero 8\n" ++
  "bv_mtx_committed_chunk_overflow:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_mtx_committed_chunked:\n  .zero " ++ toString bvMtxCommittedChunkBytes ++ "\n" ++
  "dtrc_recipkey:\n  .zero 32\n" ++
  "dtrc_threadval:\n  .zero 32\n" ++
  "dtrc_slotkey_le:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "csg_live:\n  .zero 16640\n" ++
  "csg_recipient:\n  .zero 32\n" ++
  "csg_key_be:\n  .zero 32\n" ++
  "csg_out:\n  .zero 32\n"

def ziskCommittedStorageBlockVerdictThreadingProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCommittedStorageBlockVerdictThreadingPrologue
  dataAsm     := ziskCommittedStorageBlockVerdictThreadingDataSection
}

end EvmAsm.Codegen
