import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockAccessListBuilder
import EvmAsm.Codegen.Programs.BalRlpEncode
import EvmAsm.Codegen.Programs.KeccakIncremental
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.BalCanonicalSort
import EvmAsm.Codegen.Programs.BalCanonicalSort

/-!
# `zisk_bal_serializer_measure` -- the first EXECUTING test of the measure pass

Every other check on `bal_serializer_measure_*` is a `#guard` over the emitted string.
Those pin structure, not behaviour: a routine can be defined, fully guarded, emitted into
the guest, and still compute the wrong number. The widener bug (`bal_serializer_u64_to_field`
writing the scalar field in the opposite byte order to every consumer, so
`block_access_index = 1` measured as 33 bytes instead of 1) is exactly what that gap
produces, and it was found by reading, not by a test.

The measure pass cannot be reached from any fixture -- `bal_serializer_measure_account`
has zero callers -- so a synthetic probe is the only way to execute it at all.

Each case populates `bal_builder_storage_changes` directly, calls
`bal_serializer_measure_storage`, and stores the result to the output area. The expected
values are hand-derived from the yellow paper's RLP rules, and the script compares the
output bytes.

## The cases, and what each one can catch

Row layout is 96 bytes: `address[20]` BE at +0, `block_access_index` u64 at +24,
`slot[32]` LE at +32, `new_value[32]` LE at +64.

| # | rows | expected | what a wrong answer means |
|---|---|---|---|
| 1 | one change, bai=1, slot=1, value=5 | 6 | the baseline nesting: 3 header levels |
| 2 | two changes to the SAME slot | 9 | 18 means the first-occurrence dedup is gone |
| 3 | two changes to DIFFERENT slots | 12 | 6 means the slot walk stops early |
| 4 | second row belongs to another address | 6 | 12 means the address filter is gone |
| 5 | one change, value = 0x0100 | 8 | 6 means multi-byte scalars measure as one byte |

Case 1 derivation, which the rest follow: `scalar(1)` and `scalar(5)` are one byte each,
so the `StorageChange` payload is 2 and its header is 1, giving 3. One change makes the
changes-list payload 3, header 1, giving 4. `scalar(slot=1)` is 1, so the `SlotChanges`
payload is 5, its header 1, and the field payload is 6.

Case 2 is the load-bearing one: with `bai` 1 and 2 the two changes are distinct rows on
one slot, so the slot must be measured ONCE with both changes inside it. Measuring it
twice gives 18 -- the exact failure the `slot_seen_before` guard claims to prevent and
has never demonstrated.

Case 5 discriminates the widener/scalar byte order that the string guards cannot: with
the pre-fix widener this case and case 1 both came back 32 bytes too large.
-/

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Zero a 96-byte row at `t0`, then set address byte 0, bai, slot byte 0, value byte 0. -/
private def probeRow (idx : Nat) (addrByte bai slotByte valByte : Nat) : String :=
  let off := idx * 96
  "  la t0, bal_builder_storage_changes; addi t0, t0, " ++ toString off ++ "\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); sd zero, 56(t0)\n" ++
  "  sd zero, 64(t0); sd zero, 72(t0); sd zero, 80(t0); sd zero, 88(t0)\n" ++
  "  li t1, " ++ toString addrByte ++ "; sb t1, 0(t0)\n" ++
  "  li t1, " ++ toString bai ++ "; sd t1, 24(t0)\n" ++
  "  li t1, " ++ toString slotByte ++ "; sb t1, 32(t0)\n" ++
  "  li t1, " ++ toString valByte ++ "; sb t1, 64(t0)\n"

/-- Set the row count and run `measure_storage` for address A, storing to `off(s0)`. -/
private def probeRun (count : Nat) (off : Nat) : String :=
  "  la t0, bal_builder_storage_change_count; li t1, " ++ toString count ++ "; sd t1, 0(t0)\n" ++
  "  la a0, bsmp_addr_a; jal ra, bal_serializer_measure_storage\n" ++
  "  sd a0, " ++ toString off ++ "(s0)\n"

def ziskBalSerializerMeasurePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- Address A = 0xAA followed by 19 zero bytes; B differs in byte 0 only.
  "  la t0, bsmp_addr_a\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  li t1, 0xAA; sb t1, 0(t0)\n" ++
  -- Case 1: one change, bai=1, slot=1, value=5 -> 6
  probeRow 0 0xAA 1 1 5 ++
  probeRun 1 0 ++
  -- Case 1b: measure_slot's two payloads for the same input -> 5 and 3
  "  la a0, bsmp_addr_a; la a1, bal_builder_storage_changes\n" ++
  "  jal ra, bal_serializer_measure_slot\n" ++
  "  sd a0, 40(s0); sd a1, 48(s0)\n" ++
  -- Case 2: two changes to the SAME slot (bai 1 and 2) -> 9, not 18
  probeRow 0 0xAA 1 1 5 ++
  probeRow 1 0xAA 2 1 6 ++
  probeRun 2 8 ++
  -- Case 3: two DIFFERENT slots -> 12
  probeRow 0 0xAA 1 1 5 ++
  probeRow 1 0xAA 1 2 5 ++
  probeRun 2 16 ++
  -- Case 4: the second row belongs to address B -> 6
  probeRow 0 0xAA 1 1 5 ++
  probeRow 1 0xBB 1 2 5 ++
  probeRun 2 24 ++
  -- Case 5: a two-byte value, 0x0100 (LE: byte 0 = 0x00, byte 1 = 0x01) -> 8
  probeRow 0 0xAA 1 1 0 ++
  "  la t0, bal_builder_storage_changes; li t1, 1; sb t1, 65(t0)\n" ++
  probeRun 1 32 ++
  -- Case 6: EMIT case 1's storage_changes and publish the DIGEST. This is the
  -- acceptance criterion in miniature -- hash the bytes and compare the hash -- rather
  -- than another length. Expected RLP, derived by hand: SlotChanges payload 5 -> 0xc5,
  -- scalar(slot=1) -> 0x01, changes list payload 3 -> 0xc3, StorageChange payload 2 ->
  -- 0xc2, scalar(bai=1) -> 0x01, scalar(value=5) -> 0x05, i.e. `c5 01 c3 c2 01 05`.
  -- The runner checks its keccak-256 against an independent pure-python reference.
  probeRow 0 0xAA 1 1 5 ++
  "  la t0, bal_builder_storage_change_count; li t1, 1; sd t1, 0(t0)\n" ++
  "  la a0, bsmp_ctx; jal ra, keccak_init\n" ++
  "  la a0, bsmp_ctx; la a1, bsmp_addr_a; la a2, bsmp_scratch\n" ++
  "  jal ra, bal_serializer_emit_storage\n" ++
  "  la a0, bsmp_ctx; addi a1, s0, 64; jal ra, keccak_final\n" ++
  -- Case 7: measure and then EMIT the whole AccountChanges, publishing its digest at
  -- +96. With only case 1's single storage change and every other field empty, the
  -- encoding is derivable by hand end to end:
  --   e0 94 <20 addr bytes> c6 c5 01 c3 c2 01 05 c0 c0 c0 c0
  -- i.e. account payload 32 (21 address + 7 storage_changes + four empty lists), so the
  -- account header is 0xc0+32 = 0xe0. The four trailing 0xc0 are the point: an empty
  -- field is an empty LIST, not an omitted one, and dropping them still yields
  -- well-formed RLP of a different account.
  "  la a0, bsmp_addr_a; jal ra, bal_serializer_measure_account\n" ++
  "  la a0, bsmp_ctx; jal ra, keccak_init\n" ++
  "  la a0, bsmp_ctx; la a1, bsmp_addr_a; la a2, bsmp_scratch\n" ++
  "  jal ra, bal_serializer_emit_account\n" ++
  "  la a0, bsmp_ctx; addi a1, s0, 96; jal ra, keccak_final\n" ++
  -- Case 8: the OUTER list over two accounts, digest at +128. Two accounts of 33 bytes
  -- each make a 66-byte payload, which is past the 55-byte boundary, so the outer header
  -- takes the LONG form f8 42 rather than 0xc0+66. That boundary is the reason for two
  -- accounts rather than one: a single account stays in short form and the long-form
  -- branch of the header emitter would never run.
  probeRow 0 0xAA 1 1 5 ++
  probeRow 1 0xBB 1 1 5 ++
  "  la t0, bal_builder_storage_change_count; li t1, 2; sd t1, 0(t0)\n" ++
  "  la t0, bal_builder_accounts\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0)\n" ++
  "  sd zero, 24(t0); sd zero, 32(t0); sd zero, 40(t0)\n" ++
  "  li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 24(t0)\n" ++
  "  la t0, bal_builder_account_count; li t1, 2; sd t1, 0(t0)\n" ++
  "  la a0, bsmp_ctx; jal ra, keccak_init\n" ++
  "  la a0, bsmp_ctx; la a1, bsmp_scratch; jal ra, bal_serializer_emit_outer\n" ++
  "  la a0, bsmp_ctx; addi a1, s0, 128; jal ra, keccak_final\n" ++
  -- Case 9: THE DISCRIMINATING storage_reads CASE. Slot 7 is read AND written (at
  -- block_access_index 3, i.e. a different transaction from the read); slot 11 is read
  -- and never written. EIP-7928 excludes a read whose slot is written ANYWHERE in the
  -- block, so 7 must drop out and 11 must survive.
  --
  -- No single-transaction fixture can produce this: the exclusion is block-scoped, so
  -- read-in-tx-0/written-in-tx-3 only exists across transactions. That is why it is here
  -- rather than in the EEST corpus.
  --
  -- Read rows live at 0xa1ba0000 on a 64-byte stride and hold the address as an LE stack
  -- word, so BE byte 0 of the address sits at row byte 19 -- not byte 0, which is where
  -- the builder rows keep it.
  "  li t0, 0xa1ba0000\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); sd zero, 56(t0)\n" ++
  "  sd zero, 64(t0); sd zero, 72(t0); sd zero, 80(t0); sd zero, 88(t0)\n" ++
  "  sd zero, 96(t0); sd zero, 104(t0); sd zero, 112(t0); sd zero, 120(t0)\n" ++
  "  li t1, 0xAA; sb t1, 19(t0); sb t1, 83(t0)\n" ++
  "  li t1, 7; sb t1, 32(t0); li t1, 11; sb t1, 96(t0)\n" ++
  "  la t0, storage_reads_count; li t1, 2; sd t1, 0(t0)\n" ++
  -- one write: address A, slot 7, at block_access_index 3
  probeRow 0 0xAA 3 7 5 ++
  "  la t0, bal_builder_storage_change_count; li t1, 1; sd t1, 0(t0)\n" ++
  "  la a0, bsmp_addr_a; jal ra, bal_serializer_measure_reads\n" ++
  "  sd a0, 160(s0)\n" ++
  "  la a0, bsmp_ctx; jal ra, keccak_init\n" ++
  "  la a0, bsmp_ctx; la a1, bsmp_addr_a; la a2, bsmp_scratch\n" ++
  "  jal ra, bal_serializer_emit_reads\n" ++
  "  la a0, bsmp_ctx; addi a1, s0, 192; jal ra, keccak_final\n" ++
  -- Case 10: SORT-THEN-REBUILD. Same two accounts as case 8, seeded in DESCENDING
  -- address order (B before A). `bal_serializer_rebuild_hash` sorts before it emits, so
  -- the digest must come out IDENTICAL to case 8's ascending one.
  --
  -- Seeding out of order is the only construction that can demonstrate the sort runs: an
  -- unsorted emission is a well-formed BAL where every byte is individually correct and
  -- only the SEQUENCE is wrong, so an in-order seed passes whether or not the sort is
  -- ever called.
  --
  -- RUN THIS ON SPIKE, NOT ZISKEMU. It faulted at a 20-byte account stride because the
  -- sort swaps rows with ld/sd and row 1 landed at base+20; rows are 24 bytes now, which
  -- is 8-aligned (see `balBuilderAccountRowBytes`). AGENTS.md:220 notes ziskemu tolerates
  -- unaligned reads at runtime, so under it the broken layout would likely have passed --
  -- a green case certifying a layout the verified semantics reject.
  "  li t0, 0xdead; sd t0, 224(s0); sd t0, 232(s0)\n" ++
  -- Reset the reads count. Case 9 left it at 2, and the cases share one set of globals,
  -- so without this the accounts carry a storage_reads field and the digest cannot
  -- match case 8. Caught by this case disagreeing rather than by inspection.
  "  la t0, storage_reads_count; sd zero, 0(t0)\n" ++
  probeRow 0 0xAA 1 1 5 ++
  probeRow 1 0xBB 1 1 5 ++
  "  la t0, bal_builder_storage_change_count; li t1, 2; sd t1, 0(t0)\n" ++
  "  la t0, bal_builder_accounts\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0)\n" ++
  "  sd zero, 24(t0); sd zero, 32(t0); sd zero, 40(t0)\n" ++
  "  li t1, 0xBB; sb t1, 0(t0); li t1, 0xAA; sb t1, 24(t0)\n" ++
  "  la t0, bal_builder_account_count; li t1, 2; sd t1, 0(t0)\n" ++
  "  la a0, bsmp_scratch; la a1, bsmp_rebuilt; jal ra, bal_serializer_rebuild_hash\n" ++
  "  sd a0, 224(s0)\n" ++
  "  la t0, bsmp_rebuilt; ld t1, 0(t0); sd t1, 232(s0)\n" ++
  "  j .Lbsmp_done\n" ++
  balSerializerAddrMatchesBeFunction ++
  balSerializerSlotEqFunction ++
  balSerializerSlotSeenBeforeFunction ++
  balSerializerU64ToFieldFunction ++
  balSerializerMeasureSlotFunction ++
  balSerializerMeasureStorageFunction ++
  balRlpScalarLenFunction ++
  balRlpScalarRlpLenFunction ++
  balRlpListHeaderLenFunction ++
  balRlpEmitScalarFunction ++
  balRlpEmitListHeaderFunction ++
  balSerializerEmitStorageFunction ++
  balSerializerEmitReadsFunction ++
  balSerializerEmitBalanceFunction ++
  balSerializerEmitNonceFunction ++
  balSerializerEmitCodeFunction ++
  balSerializerEmitAccountFunction ++
  balSerializerMeasureOuterFunction ++
  balSerializerEmitOuterFunction ++
  balSerializerRebuildHashFunction ++
  balCanonicalSortFunction ++
  balSerializerMeasureAccountFunction ++
  balSerializerMeasureReadsFunction ++
  balSerializerMeasureBalanceFunction ++
  balSerializerMeasureNonceFunction ++
  balSerializerMeasureCodeFunction ++
  balSerializerAddrMatchesFunction ++
  balSerializerSlotWrittenFunction ++
  balRlpEmitBytesFunction ++
  balRlpMeasureIntoThrowawayFunction ++
  keccakIncrementalFunctions ++
  zkvmKeccak256Function ++ "\n" ++
  ".Lbsmp_done:"

/-- Only the four data symbols the measure path touches. The real arena is megabytes;
    five rows is all these cases need, and a short arena also means a walk that runs off
    the end faults instead of reading plausible zeros. -/
def ziskBalSerializerMeasureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bsmp_addr_a:\n  .zero 32\n" ++
  "bal_builder_storage_change_count:\n  .zero 8\n" ++
  "bal_serializer_len_table:\n  .zero 48\n" ++
  "bal_serializer_u64_field:\n  .zero 32\n" ++
  "bal_builder_storage_changes:\n  .zero 480\n" ++
  ".balign 8\n" ++
  "bsmp_ctx:\n  .zero 512\n" ++
  "bsmp_scratch:\n  .zero 256\n" ++

  "zk3_state:\n  .zero 200\n" ++
  "storage_reads_count:\n  .zero 8\n" ++
  "bal_builder_balance_count:\n  .zero 8\n" ++
  "bal_builder_balance_changes:\n  .zero 128\n" ++
  "bal_builder_nonce_count:\n  .zero 8\n" ++
  "bal_builder_nonce_changes:\n  .zero 128\n" ++
  "bal_builder_code_count:\n  .zero 8\n" ++
  "bal_builder_code_changes:\n  .zero 128\n" ++
  "bal_serializer_throwaway_ctx:\n  .zero 512\n" ++
  "bal_serializer_hdr_scratch:\n  .zero 64\n" ++
  "bal_serializer_outer_payload:\n  .zero 8\n" ++
  "bal_builder_account_count:\n  .zero 8\n" ++
  "bal_builder_accounts:\n  .zero 128\n" ++
  "bal_serializer_sort_status:\n  .zero 8\n" ++
  "bal_serializer_rebuilt_ctx:\n  .zero 512\n" ++
  "bsmp_rebuilt:\n  .zero 32\n" ++
  balCanonicalSortDataSection ++
  keccakIncrementalDataSection

def ziskBalSerializerMeasureProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalSerializerMeasurePrologue
  dataAsm     := ziskBalSerializerMeasureDataSection
}

/-! ## Guards

The probe is only worth anything if the discriminating cases are really present. -/

-- Five `measure_storage` runs, keyed on the probe's OWN call site. A bare mnemonic count
-- drifts every time another body is spliced into the closure -- `measure_account` calls
-- `measure_storage` too -- and says nothing about how many cases the probe runs.
#guard (ziskBalSerializerMeasurePrologue.splitOn
  "  la a0, bsmp_addr_a; jal ra, bal_serializer_measure_storage\n").length == 6
-- Keyed on the probe's OWN call site, not on a bare mnemonic. The prologue splices in
-- `measure_storage` and `emit_storage`, which both call `measure_slot` themselves, so a
-- bare count is a function of who else got spliced -- it drifts every time the closure
-- changes and says nothing about whether the probe still measures a slot.
#guard (ziskBalSerializerMeasurePrologue.splitOn
  "  la a0, bsmp_addr_a; la a1, bal_builder_storage_changes\n  jal ra, bal_serializer_measure_slot\n").length == 2

-- Case 2 must use TWO DISTINCT `block_access_index` values on ONE slot. With equal
-- indices the upsert semantics make them one change and the case stops discriminating
-- the dedup, which is the single thing it exists to catch.
#guard (ziskBalSerializerMeasurePrologue.splitOn "li t1, 2; sd t1, 24(t0)").length == 2

-- Case 5 must set a SECOND value byte. Without it the case duplicates case 1 and the
-- multi-byte scalar path goes untested.
#guard (ziskBalSerializerMeasurePrologue.splitOn "sb t1, 65(t0)").length == 2

-- Address B must actually differ from A, or case 4 tests nothing. THREE, because case 8
-- also places B, as does case 8: TWO uses, both load bearing. Only the `probeRow`
-- expansions match -- the account seeds spell `0xBB` in raw asm rather than going
-- through `toString`, so they read as 0xBB and not as 187.
#guard (ziskBalSerializerMeasurePrologue.splitOn "li t1, 187; sb t1, 0(t0)").length == 4

-- Case 6 must actually EMIT and finalise, or the digest slot holds whatever keccak_init
-- left and a wrong digest reads as a wrong constant rather than as a missing call.
#guard (ziskBalSerializerMeasurePrologue.splitOn
  "  la a0, bsmp_ctx; la a1, bsmp_addr_a; la a2, bsmp_scratch\n  jal ra, bal_serializer_emit_storage\n").length == 2
#guard (ziskBalSerializerMeasurePrologue.splitOn
  "  la a0, bsmp_ctx; addi a1, s0, 64; jal ra, keccak_final\n").length == 2

-- Case 7 must MEASURE before it emits: every header in the account emitter is read
-- from the length table, so emitting against a stale table yields a well-formed
-- account with the wrong headers and only the digest would notice.
#guard (ziskBalSerializerMeasurePrologue.splitOn
  "  la a0, bsmp_addr_a; jal ra, bal_serializer_measure_account\n").length == 2
-- Keyed on case 7's own call site: `emit_outer` is spliced in and calls `emit_account`
-- too, so a bare count tracks the closure rather than the case.
#guard (ziskBalSerializerMeasurePrologue.splitOn
  "  la a0, bsmp_ctx; la a1, bsmp_addr_a; la a2, bsmp_scratch\n  jal ra, bal_serializer_emit_account\n").length == 2
#guard (ziskBalSerializerMeasurePrologue.splitOn
  "  la a0, bsmp_ctx; addi a1, s0, 96; jal ra, keccak_final\n").length == 2

-- Case 8 needs TWO accounts. With one the outer payload is 33, inside the short form,
-- and the long-form branch of the list-header emitter is never exercised.
#guard (ziskBalSerializerMeasurePrologue.splitOn
  "  la t0, bal_builder_account_count; li t1, 2; sd t1, 0(t0)\n").length == 3
#guard (ziskBalSerializerMeasurePrologue.splitOn
  "  la a0, bsmp_ctx; la a1, bsmp_scratch; jal ra, bal_serializer_emit_outer\n").length == 2

-- Case 9 must write the slot at a DIFFERENT block_access_index from any read, or it
-- stops testing the cross-transaction exclusion and becomes a same-tx case that a
-- fixture could already produce.
#guard (ziskBalSerializerMeasurePrologue.splitOn "li t1, 3; sd t1, 24(t0)").length == 2
-- Two reads, one written and one not. With both written or both unwritten the case
-- cannot distinguish an exclusion from a blanket drop or a blanket keep.
#guard (ziskBalSerializerMeasurePrologue.splitOn "li t1, 7; sb t1, 32(t0); li t1, 11; sb t1, 96(t0)").length == 2

end EvmAsm.Codegen
