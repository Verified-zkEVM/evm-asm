import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockAccessListBuilder
import EvmAsm.Codegen.Programs.BalSerializerTail
import EvmAsm.Codegen.Programs.BalRlpEncode
import EvmAsm.Codegen.Programs.BalCanonicalSort

/-!
# `zisk_bal_order_dump` -- publish the EMITTED BYTES, not a digest

Case 12 (the ordering fixture) fails, and five hypotheses have been eliminated against
it: the measure pass, the hand-derivation, all four orderings, the upsert, and the sort's
mechanics. Each elimination cost a run and yielded one bit, because a digest is a one-bit
oracle.

This unit replaces the keccak sponge with a BYTE SINK. `keccak_absorb` appends to a
buffer instead of permuting a state, so `bal_serializer_emit_account` writes its bytes
where they can be read directly. One run gives the whole answer.

The stubs are safe precisely because nothing here checks a digest: `keccak_init` resets
the write cursor, `keccak_absorb` appends, `keccak_final` is a no-op. A unit that both
stubbed the sponge AND checked a hash would be checking the stub.

Same input as case 12: two slots, and two changes on one of them, seeded DESCENDING at
both levels. Expected emission, derived from the spec:

  cf c5 03 c3 c2 01 07  c8 07 c6 c2 01 05 c2 02 06
  ^  ^slot 3 (index 1)  ^slot 7 (index 1, index 2)
  storage_changes header, payload 15
-/

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- One 96-byte builder row. Slot at byte 63 because rows hold it BIG-ENDIAN. -/
private def balOrderDumpRow (idx bai slotByte valByte : Nat) : String :=
  let off := idx * 96
  "  la t0, bal_builder_storage_changes; addi t0, t0, " ++ toString off ++ "\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); sd zero, 56(t0)\n" ++
  "  sd zero, 64(t0); sd zero, 72(t0); sd zero, 80(t0); sd zero, 88(t0)\n" ++
  "  li t1, 0xAA; sb t1, 0(t0)\n" ++
  "  li t1, " ++ toString bai ++ "; sd t1, 24(t0)\n" ++
  "  li t1, " ++ toString slotByte ++ "; sb t1, 63(t0)\n" ++
  "  li t1, " ++ toString valByte ++ "; sb t1, 64(t0)\n"

/-- Byte-sink replacements for the incremental keccak ABI. -/
def balOrderDumpSink : String :=
  -- THE SINK MUST DISTINGUISH CONTEXTS. `bal_serializer_measure_code` measures the code
  -- blob through the THROWAWAY keccak route, which absorbs into
  -- `bal_serializer_throwaway_ctx`. A sink that appends every context to one buffer
  -- records the measurement pass as well as the emission -- and `keccak_init` on the
  -- throwaway resets the cursor mid-emission. Both were visible in the first dump: the
  -- code blobs appeared before the outer header and again inside the field.
  --
  -- So init and absorb act ONLY on the real context and ignore the throwaway.
  "keccak_init:\n" ++
  "  la t2, bal_serializer_rebuilt_ctx; bne a0, t2, .Lbod_skip_init\n" ++
  "  la t0, bod_cursor; la t1, bod_buf; sd t1, 0(t0)\n" ++
  ".Lbod_skip_init:\n" ++
  "  ret\n" ++
  "keccak_absorb:\n" ++                        -- a0 = ctx, a1 = ptr, a2 = len
  "  la t2, bal_serializer_rebuilt_ctx; bne a0, t2, .Lbod_absorb_ret\n" ++
  "  la t0, bod_cursor; ld t1, 0(t0)\n" ++
  ".Lbod_cp:\n" ++
  "  beqz a2, .Lbod_cp_done\n" ++
  "  lbu t2, 0(a1); sb t2, 0(t1); addi a1, a1, 1; addi t1, t1, 1; addi a2, a2, -1\n" ++
  "  j .Lbod_cp\n" ++
  ".Lbod_cp_done:\n" ++
  "  la t0, bod_cursor; sd t1, 0(t0)\n" ++
  ".Lbod_absorb_ret:\n" ++
  "  ret\n" ++
  "keccak_final:\n" ++
  "  ret\n"

def ziskBalOrderDumpPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, bod_addr\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  li t1, 0xAA; sb t1, 0(t0)\n" ++
  -- three rows: (slot 7, index 2), (slot 7, index 1), (slot 3, index 1) -- descending
  -- at BOTH levels. Slots are BE32, so the slot byte goes at 63.
  balOrderDumpRow 0 2 7 6 ++
  balOrderDumpRow 1 1 7 5 ++
  balOrderDumpRow 2 1 3 7 ++
  "  la t0, bal_builder_storage_change_count; li t1, 3; sd t1, 0(t0)\n" ++
  -- TWO balance changes, seeded DESCENDING by index (2 before 1), so the balance
  -- ordering rule is exercised rather than trivially satisfied. Row is 64 bytes:
  -- addr BE20 at 0, index at 24, post value LE at 32.
  "  la t0, bal_builder_balance_changes\n" ++
  "  sd zero, 0(t0);  sd zero, 8(t0);  sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); sd zero, 56(t0)\n" ++
  "  sd zero, 64(t0); sd zero, 72(t0); sd zero, 80(t0); sd zero, 88(t0)\n" ++
  "  sd zero, 96(t0); sd zero, 104(t0); sd zero, 112(t0); sd zero, 120(t0)\n" ++
  "  li t1, 0xAA; sb t1, 0(t0);  li t1, 2; sd t1, 24(t0); li t1, 4; sb t1, 32(t0)\n" ++
  "  li t1, 0xAA; sb t1, 64(t0); li t1, 1; sd t1, 88(t0); li t1, 3; sb t1, 96(t0)\n" ++
  "  la t0, bal_builder_balance_count; li t1, 2; sd t1, 0(t0)\n" ++
  -- TWO nonce changes, seeded DESCENDING by index. Same 0x08189400 descriptor as
  -- balance, so this settles the family rather than resting on shared machinery.
  -- Row is 40 bytes: addr BE20 at 0, index at 24, nonce u64 at 32.
  "  la t0, bal_builder_nonce_changes\n" ++
  "  sd zero, 0(t0);  sd zero, 8(t0);  sd zero, 16(t0); sd zero, 24(t0); sd zero, 32(t0)\n" ++
  "  sd zero, 40(t0); sd zero, 48(t0); sd zero, 56(t0); sd zero, 64(t0); sd zero, 72(t0)\n" ++
  "  li t1, 0xAA; sb t1, 0(t0);  li t1, 2; sd t1, 24(t0); li t1, 9; sd t1, 32(t0)\n" ++
  "  li t1, 0xAA; sb t1, 40(t0); li t1, 1; sd t1, 64(t0); li t1, 8; sd t1, 72(t0)\n" ++
  "  la t0, bal_builder_nonce_count; li t1, 2; sd t1, 0(t0)\n" ++
  -- TWO storage reads, seeded DESCENDING by slot. This is the only stream using the
  -- 0x2020 descriptor -- an LE slot key rather than a BE address -- so it is the one
  -- ordering rule no other case covers. Rows at 0xa1908780, stride 64: address as an
  -- LE stack word (BE byte 0 lands at row byte 19), slot as an LE stack word at 32.
  "  li t0, 0xa1908780\n" ++
  "  sd zero, 0(t0);  sd zero, 8(t0);  sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); sd zero, 56(t0)\n" ++
  "  sd zero, 64(t0); sd zero, 72(t0); sd zero, 80(t0); sd zero, 88(t0)\n" ++
  "  sd zero, 96(t0); sd zero, 104(t0); sd zero, 112(t0); sd zero, 120(t0)\n" ++
  "  li t1, 0xAA; sb t1, 19(t0); li t1, 11; sb t1, 32(t0)\n" ++
  "  li t1, 0xAA; sb t1, 83(t0); li t1, 5;  sb t1, 96(t0)\n" ++
  "  la t0, storage_reads_count; li t1, 2; sd t1, 0(t0)\n" ++
  -- TWO code changes, seeded DESCENDING by index. Code is the one field whose value is
  -- a BYTE STRING rather than a scalar, so the two entries carry different-length blobs
  -- (1 and 2 bytes) and encode to different widths -- index 1 as the self-encoding 0x2a,
  -- index 2 as 0x82 60 00. Equal-length blobs would order correctly by accident if the
  -- entries were swapped. Row is 64 bytes: addr BE20 at 0, index at 24, ptr 32, len 40.
  "  la t0, bod_code_a; li t1, 0x2a; sb t1, 0(t0)\n" ++
  "  la t0, bod_code_b; li t1, 0x60; sb t1, 0(t0); sb zero, 1(t0)\n" ++
  "  la t0, bal_builder_code_changes\n" ++
  "  sd zero, 0(t0);  sd zero, 8(t0);  sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); sd zero, 56(t0)\n" ++
  "  sd zero, 64(t0); sd zero, 72(t0); sd zero, 80(t0); sd zero, 88(t0)\n" ++
  "  sd zero, 96(t0); sd zero, 104(t0); sd zero, 112(t0); sd zero, 120(t0)\n" ++
  "  li t1, 0xAA; sb t1, 0(t0);  li t1, 2; sd t1, 24(t0)\n" ++
  "  la t2, bod_code_b; sd t2, 32(t0); li t1, 2; sd t1, 40(t0)\n" ++
  "  li t1, 0xAA; sb t1, 64(t0); li t1, 1; sd t1, 88(t0)\n" ++
  "  la t2, bod_code_a; sd t2, 96(t0); li t1, 1; sd t1, 104(t0)\n" ++
  "  la t0, bal_builder_code_count; li t1, 2; sd t1, 0(t0)\n" ++
  "  la t0, bal_builder_accounts\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0)\n" ++
  "  li t1, 0xAA; sb t1, 0(t0)\n" ++
  "  la t0, bal_builder_account_count; li t1, 1; sd t1, 0(t0)\n" ++
  "  la a0, bod_scratch; la a1, bod_hashout; jal ra, bal_serializer_rebuild_hash\n" ++
  "  sd a0, 0(s0)\n" ++                        -- sort status
  -- byte count, then the bytes themselves
  "  la t0, bod_cursor; ld t1, 0(t0); la t2, bod_buf; sub t1, t1, t2; sd t1, 8(s0)\n" ++
  "  la t2, bod_buf; addi t3, s0, 16; li t4, 0\n" ++
  ".Lbod_out:\n" ++
  "  beq t4, t1, .Lbod_out_done\n" ++
  "  add t5, t2, t4; lbu t6, 0(t5); add t5, t3, t4; sb t6, 0(t5)\n" ++
  "  addi t4, t4, 1; j .Lbod_out\n" ++
  ".Lbod_out_done:\n" ++
  "  j .Lbod_done\n" ++
  balOrderDumpSink ++
  balSerializerSlotToLeFunction ++ "\n" ++
  balSerializerBalanceToLeFunction ++ "\n" ++
  balSerializerAddrMatchesBeFunction ++ "\n" ++
  balSerializerAddrMatchesFunction ++ "\n" ++
  balSerializerSlotEqFunction ++ "\n" ++
  balSerializerSlotWrittenFunction ++ "\n" ++
  balSerializerSlotSeenBeforeFunction ++ "\n" ++
  balSerializerU64ToFieldFunction ++ "\n" ++
  balSerializerMeasureSlotFunction ++ "\n" ++
  balSerializerMeasureStorageFunction ++ "\n" ++
  balSerializerMeasureReadsFunction ++ "\n" ++
  balSerializerMeasureBalanceFunction ++ "\n" ++
  balSerializerMeasureNonceFunction ++ "\n" ++
  balSerializerMeasureCodeFunction ++ "\n" ++
  balSerializerMeasureAccountFunction ++ "\n" ++
  balSerializerEmitStorageFunction ++ "\n" ++
  balSerializerEmitReadsFunction ++ "\n" ++
  balSerializerEmitBalanceFunction ++ "\n" ++
  balSerializerEmitNonceFunction ++ "\n" ++
  balSerializerEmitCodeFunction ++ "\n" ++
  balSerializerEmitAccountFunction ++ "\n" ++
  balSerializerMeasureOuterFunction ++ "\n" ++
  balSerializerEmitOuterFunction ++ "\n" ++
  balSerializerRebuildHashFunction ++ "\n" ++
  balCanonicalSortFunction ++ "\n" ++
  balRlpScalarLenFunction ++ "\n" ++
  balRlpScalarRlpLenFunction ++ "\n" ++
  balRlpListHeaderLenFunction ++ "\n" ++
  balRlpEmitScalarFunction ++ "\n" ++
  balRlpEmitListHeaderFunction ++ "\n" ++
  balRlpEmitBytesFunction ++ "\n" ++
  balRlpMeasureIntoThrowawayFunction ++ "\n" ++
  ".Lbod_done:"

def ziskBalOrderDumpDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bod_addr:\n  .zero 32\n" ++
  "bod_scratch:\n  .zero 256\n" ++
  "bod_hashout:\n  .zero 32\n" ++
  "bod_cursor:\n  .zero 8\n" ++
  "bod_buf:\n  .zero 512\n" ++
  "bod_code_a:\n  .zero 8\n" ++
  "bod_code_b:\n  .zero 8\n" ++
  "bal_builder_storage_change_count:\n  .zero 8\n" ++
  "bal_builder_storage_changes:\n  .zero 512\n" ++
  "bal_serializer_len_table:\n  .zero 48\n" ++
  "bal_serializer_u64_field:\n  .zero 32\n" ++
  "bal_serializer_slot_le:\n  .zero 32\n" ++
  "bal_serializer_balance_le:\n  .zero 32\n" ++
  "bal_serializer_outer_payload:\n  .zero 8\n" ++
  "bal_serializer_sort_status:\n  .zero 8\n" ++
  "bal_serializer_rebuilt_ctx:\n  .zero 512\n" ++
  "bal_serializer_throwaway_ctx:\n  .zero 512\n" ++
  "bal_serializer_hdr_scratch:\n  .zero 64\n" ++
  "storage_reads_count:\n  .zero 8\n" ++
  "bal_builder_balance_count:\n  .zero 8\n" ++
  "bal_builder_balance_changes:\n  .zero 128\n" ++
  "bal_builder_nonce_count:\n  .zero 8\n" ++
  "bal_builder_nonce_changes:\n  .zero 128\n" ++
  "bal_builder_code_count:\n  .zero 8\n" ++
  "bal_builder_code_changes:\n  .zero 128\n" ++
  "bal_builder_accounts:\n  .zero 128\n" ++
  "bal_builder_account_count:\n  .zero 8\n" ++
  balCanonicalSortDataSection

def ziskBalOrderDumpProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalOrderDumpPrologue
  dataAsm     := ziskBalOrderDumpDataSection
}

/-! ## Guards -/

-- The sink must REPLACE the sponge, and nothing here may check a digest -- a unit that
-- stubs keccak and then verifies a hash is verifying the stub.
#guard (ziskBalOrderDumpPrologue.splitOn "keccak_absorb:").length == 2
-- The sink must gate on the context: the throwaway measurement absorbs too, and a sink
-- that records it dumps the measure pass alongside the emission.
#guard (ziskBalOrderDumpPrologue.splitOn "bal_serializer_rebuilt_ctx; bne a0, t2").length == 3
#guard (ziskBalOrderDumpPrologue.splitOn "keccak_init:").length == 2

-- Descending at BOTH levels, or the dump cannot distinguish a sort from its absence.
-- Descending at BOTH storage levels AND in the balance list: index 2 seeded before
-- index 1 in each. Two occurrences of the index-2 store, one per stream.
-- Descending seeds in all five streams: two storage levels, balance, nonce and code.
#guard (ziskBalOrderDumpPrologue.splitOn "li t1, 2; sd t1, 24(t0)").length == 5

end EvmAsm.Codegen
