/-
  EvmAsm.Codegen.Programs.BlockAccessListBuilder

  Persistent execution-side representation of Amsterdam's
  `BlockAccessListBuilder.accounts : Dict[Address, AccountData]`.

  The guest cannot use a host dictionary, so this module keeps one canonical
  20-byte big-endian account table and four homogeneous event streams.  The
  table deduplicates/touches accounts; every event also carries its canonical
  BE20 address as its first field.  This deliberate duplication lets the
  three-segment sorter consume exactly the spec's ordering key in-row
  (`address`, then `slot` where relevant, then `block_access_index`), rather
  than sorting an insertion index and relying on a remap argument.  The five
  logical `AccountData`
  fields are represented as follows:

  * `storage_changes` -- the dedicated 96-byte builder stream;
  * `storage_reads` -- the existing block-lifetime `storage_reads` set;
  * `balance_changes`, `nonce_changes`, `code_changes` -- their dedicated
    streams below.

  Storage reads are deliberately not duplicated here.  `storage_read_record`
  and `read_sets_incorporate_tx` already implement the spec's block-level set
  lifetime; the serializer will canonicalise its stack-word address key and
  omit any slot also present in `storage_changes`, matching
  `_build_from_builder`.

  These are NOBITS reservations only.  They must survive transaction execution
  through BAL serialization and hashing, so they cannot alias `.sszscratch`:
  the serializer itself invokes the SSZ scratch routines.  They are emitted at
  the data-section tail so no existing data symbol is moved.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BalSerializer

namespace EvmAsm.Codegen

/-- Account-table row: a 20-byte big-endian `Address` in 24 bytes.

    THE 4 PADDING BYTES ARE LOAD-BEARING, and the rule behind them is project-wide rather
    than local to this table.

    ANY ROW ARRAY THAT WILL BE SORTED MUST HAVE AN 8-ALIGNED STRIDE. `bal_canonical_sort`
    swaps rows with `ld`/`sd` (`BalCanonicalSort.lean:254`), and per AGENTS.md:211 the
    verified RV64 semantics give `LD`/`SD` NO SEMANTICS unless the address is a multiple
    of 8 -- `isValidDwordAccess` is `isValidMemAddr && isAligned8`. This is not a platform
    quirk to be worked around: a proof that reaches a misaligned access cannot close. 24
    is the smallest 8-aligned stride that holds a 20-byte address.

    The sort's own ABI does not say this. It documents `a2 = row stride in bytes` with no
    constraint, and its comment about using `mul` rather than a shift "so the routine is
    not silently wrong for a non-power-of-two stride a future caller passes" reads as an
    invitation to pass any stride. Violating the real precondition faults rather than
    returning one of its five documented status codes.

    MEASURED ON SPIKE, AND ZISKEMU WOULD NOT HAVE CAUGHT IT. Same sort, same descriptor,
    only the stride varied: 32 sorts cleanly and returns the expected order, 20 faults at
    that swap instruction. AGENTS.md:220 warns that ziskemu tolerates unaligned reads at
    runtime, so the 20-byte layout would likely have PASSED under it -- a green test
    certifying a layout the verified semantics reject.

    24 rather than 32: the arena is capacity 76923, so 24 costs 307,692 bytes and fits
    below `.sszscratch`, while a separate 32-byte staging copy needed 2,461,536 and did
    not. -/
def balBuilderAccountRowBytes : Nat := 24
/-- `{address[20], pad[4], u64 BAI, slot[32], post value[32]}`. -/
def balBuilderStorageChangeRowBytes : Nat := 96
/-- `{address[20], pad[4], u64 BAI, post balance[32]}`. -/
def balBuilderBalanceRowBytes : Nat := 64
/-- `{address[20], pad[4], u64 BAI, post nonce}`. -/
def balBuilderNonceRowBytes : Nat := 40
/-- `{address[20], pad[4], u64 BAI, code-effect reference/meta[32]}`. -/
def balBuilderCodeRowBytes : Nat := 64

/-- Separate resource bounds. They are intentionally not added as if one block
    could maximize every list simultaneously. The joint 200M-gas enumeration
    behind the persistent 7,281,964-byte reservation is:

    * blob-sidecar / transaction-sidecar work, the densest currently reachable
      route, at about 0.0190 emitted bytes per gas (about 3.80MB);
    * storage and ordinary balance/nonce/code producer routes, each below that
      density once their intrinsic or state-gas charges are included; and
    * EIP-6780 SELFDESTRUCT deletion: Amsterdam only deletes an originator in
      `tx_state.created_accounts`, so it is same-transaction-created and pays
      CREATE state gas plus the 5000 SELFDESTRUCT base (about 0.0037 B/gas even
      under its three-component 136-byte expansion). Its pre-state is absent,
      so the boundary comparison normally emits no deletion-only component.

The enumeration reflects the Amsterdam spec areas read to date and must be
revisited when a new producer route is understood. The reservation is therefore
a joint upper bound with material slack, not a sum of independent maxima. -/
def balBuilderAccountCapacity : Nat := 76923
def balBuilderStorageChangeCapacity : Nat := 15384
def balBuilderBalanceCapacity : Nat := 50000
def balBuilderNonceCapacity : Nat := 16666
def balBuilderCodeCapacity : Nat := 6250

/-! ## The serializer's length table

    RLP requires a list's payload length BEFORE its header can be written, so a walk
    over nested lists is always two passes: measure, then emit. The table exists so
    those two passes cannot disagree — **the emit pass reads a length it never
    computes.** Two implementations of one length rule is how they diverge, and a
    divergence produces a well-formed buffer with a wrong header, which is invisible
    until the hash is compared.

    ## THE CONVENTION, WHICH IS THE CLASSIC NESTING ERROR HERE

    **Every entry is a PAYLOAD length: the bytes INSIDE the list, excluding that
    list's own header.** `rlp_encode_list_prefix` takes exactly this, so an entry can
    be handed to it unmodified.

    The consequence that must not be got wrong: the outer list's payload length is the
    sum of each account's **ENCODED** size — its own header plus its payload — and NOT
    the sum of the account payload entries. Summing payloads leaves the outer header
    short by the total size of every account header, which for many accounts is large
    and completely silent: the prefix is still well-formed.

    So a caller that needs an encoded size derives it as
    `payload + headerLen(payload)`, and the word "payload" in this table always means
    the narrow thing.

    ## GRANULARITY: ONE ENTRY PER HEADER WRITTEN

    Emit writes SIX headers per account — the account list itself, and each of its five
    field lists — so the table carries six entries. Storing only the account total would
    force emit to recompute the five field lengths, which is precisely the duplication
    the table exists to prevent.

    ## IT IS PER ACCOUNT, NOT BLOCK-SCOPE, AND THAT IS A MEMORY CEILING NOT A CHOICE

    One entry per account across the block would be `balBuilderAccountCapacity * 48` =
    3.52 MiB. **`.bss` has 1.14 MiB of headroom**: it ends at `0xbf85b4a0` and
    `.sszscratch` begins at `0xbf980000`, and the linker rejects the overlap outright
    (`section .sszscratch VMA ... overlaps section .bss VMA ...`).

    So the walk is: one pass over all accounts accumulating the outer list's payload
    length into a single dword, then a second pass which, per account, measures into
    this 48-byte table and emits immediately from it.

    Each account is therefore measured twice — but by the SAME routine over the same
    data, so the two cannot disagree, which is the property that matters. The cost is
    walk time, not correctness.

    A per-account table is also safer than the block-scope one it replaces: that version
    would have been indexed by account index, so an account count above capacity writes
    past the table into whatever `.bss` follows. A 48-byte table is not indexed and
    cannot overrun.

        +0   account payload      (the AccountChanges list's own payload)
        +8   storage_changes      payload of that field's list
        +16  storage_reads        payload of the SURVIVING reads list
        +24  balance_changes      payload
        +32  nonce_changes        payload
        +40  code_changes         payload -/
def balBuilderLenTableEntryBytes : Nat := 48

/-! ## There is no surviving-reads scratch, deliberately

    `_build_from_builder` (`:544-547`) excludes a slot from `storage_reads` when the same
    account also changed it. An earlier version of this materialised the survivors into a
    16384-slot list so measure and emit would read one filtered list.

    **That list is not needed, and it cost half a megabyte of `.bss` that the guest does
    not have.** The reason to filter once was to avoid TWO IMPLEMENTATIONS of one rule —
    but re-running `bal_serializer_slot_written`, a single predicate, cannot diverge from
    itself. The other reason was the surviving COUNT for the read list's header, and that
    comes from the filter's return value without storing any slot key.

    So the predicate runs three times per read slot — once to count, once to measure, once
    to emit — which is walk time rather than correctness, the same trade the per-account
    length table already makes by measuring each account twice.

    It is also safer: a scratch list indexed by survivor count writes past itself if the
    filter ever yields more survivors than the arena holds. No list, no overrun.

    **The difference is PER ACCOUNT, not global.** In the spec both fields hang off the same
    `changes` object inside `for address, changes in builder.accounts.items()`, so a slot
    excluded from account A's reads because A wrote it MUST still appear in account B's
    reads if B only read it. -/

def balBuilderAccountBytes : Nat := balBuilderAccountCapacity * balBuilderAccountRowBytes
def balBuilderStorageChangeBytes : Nat := balBuilderStorageChangeCapacity * balBuilderStorageChangeRowBytes
def balBuilderBalanceBytes : Nat := balBuilderBalanceCapacity * balBuilderBalanceRowBytes
def balBuilderNonceBytes : Nat := balBuilderNonceCapacity * balBuilderNonceRowBytes
def balBuilderCodeBytes : Nat := balBuilderCodeCapacity * balBuilderCodeRowBytes
def balBuilderPersistentBytes : Nat :=
  balBuilderAccountBytes + balBuilderStorageChangeBytes + balBuilderBalanceBytes +
    balBuilderNonceBytes + balBuilderCodeBytes

/-! ## Builder row field table -- THE authoritative byte-order declaration

    Cite this table. Do not re-derive a field's byte order from a nearby docstring: three
    byte-order defects in this area were each two components internally consistent with a
    different correct-sounding reading, and what was missing was one statement both sides
    could contradict.

    THE RULE THE TABLE FOLLOWS: canonical BE20 arrives FROM THE PRODUCER. A row whose
    source is an EVM stack word is reversed on append; a row whose source is an
    account-write row is not, because that row is already canonical. Every entry below is
    a consequence of where its source came from.

    | stream          | field | off | width | byte order                    |
    | storage_changes | addr  |   0 |    20 | BE20   (reversed on append)   |
    | storage_changes | bai   |  24 |     8 | native LE u64                 |
    | storage_changes | slot  |  32 |    32 | BE32   (reversed on append)   |
    | storage_changes | value |  64 |    32 | LE     (passed VERBATIM)      |
    | balance_changes | addr  |   0 |    20 | BE20   (already canonical)    |
    | balance_changes | bai   |  24 |     8 | native LE u64                 |
    | balance_changes | post  |  32 |    32 | LE                            |
    | nonce_changes   | addr  |   0 |    20 | BE20                          |
    | nonce_changes   | bai   |  24 |     8 | native LE u64                 |
    | nonce_changes   | nonce |  32 |     8 | native LE u64                 |
    | code_changes    | addr  |   0 |    20 | BE20                          |
    | code_changes    | bai   |  24 |     8 | native LE u64                 |
    | code_changes    | ptr   |  32 |     8 | pointer (no byte order)       |
    | code_changes    | len   |  40 |     8 | length  (no byte order)       |
    | storage_reads   | addr  |   0 |    32 | LE stack word                 |
    | storage_reads   | slot  |  32 |    32 | LE stack word                 |

    THE STORAGE ROW CARRIES TWO CONVENTIONS AT ONCE and that is not an accident to be
    tidied away: `bal_emit_storage_changes` reverses the address and the slot into
    `besc_addr_be` / `besc_slot_be`, then passes the value as `a3 = s4+64` verbatim. Slot
    is BE32 and value is LE32 in the same 96-byte row.

    CONSEQUENCE FOR READERS: `bal_rlp_scalar_len` / `bal_rlp_emit_scalar` are documented
    for LE limbs (`BalRlpEncode.lean:375`) -- they scan DOWN from byte 31 for the most
    significant byte. They are correct on every LE field above and WRONG on the storage
    slot, which must be reversed into scratch before being handed to them. Sources:
    `AccountWriteMap.lean:129`/`:160` for the account-write convention,
    `StorageReadLog.lean:43` for the exec-log stack word, `balSortBuilderStorageSegments`
    for the storage row's three sorted segments. -/

/-- BSS labels for the persistent builder.  Every producer has its own count
    and latches the shared overflow bit; later append routines will additionally
    set their component latch to make diagnostics precise. -/
def blockAccessListBuilderDataSection : String :=
  ".balign 8\n" ++
  "bal_builder_current_bai:\n  .zero 8\n" ++
  "bal_builder_account_count:\n  .zero 8\n" ++
  "besc_addr_be:\n  .zero 32\n" ++
  "besc_slot_be:\n  .zero 32\n" ++
  "besc_base_le:\n  .zero 32\n" ++
  "bal_builder_storage_change_count:\n  .zero 8\n" ++
  "bal_builder_balance_count:\n  .zero 8\n" ++
  "bal_builder_nonce_count:\n  .zero 8\n" ++
  "bal_builder_code_count:\n  .zero 8\n" ++
  "bal_builder_overflow:\n  .zero 8\n" ++
  "bal_builder_storage_change_overflow:\n  .zero 8\n" ++
  "bal_builder_balance_overflow:\n  .zero 8\n" ++
  "bal_builder_nonce_overflow:\n  .zero 8\n" ++
  "bal_builder_code_overflow:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bal_builder_accounts:\n  .zero " ++ toString balBuilderAccountBytes ++ "\n" ++
  ".balign 8\n" ++
  -- The serializer's length table and surviving-reads scratch. NOBITS, like their
  -- siblings, and for the same reason: they must survive execution through
  -- serialization, and .data growth would shift the address-pinned rfl proofs.
  "bal_serializer_len_table:\n  .zero " ++ toString balBuilderLenTableEntryBytes ++ "\n" ++
  "bal_serializer_outer_payload:\n  .zero 8\n" ++
  "bal_serializer_surviving_read_count:\n  .zero 8\n" ++
  -- The widener's destination. 32 bytes, 8-aligned, reused per scalar -- it holds one
  -- widened u64 at a time and is consumed immediately by the scalar measurer.
  "bal_serializer_u64_field:\n  .zero 32\n" ++
  "bal_serializer_slot_le:\n  .zero 32\n" ++
  "bal_serializer_sort_status:\n  .zero 8\n" ++
  "bal_serializer_rebuilt_ctx:\n  .zero 512\n" ++
  "bal_serializer_rebuilt_hash:\n  .zero 32\n" ++
  "bal_serializer_supplied_hash:\n  .zero 32\n" ++
  "bal_serializer_hdr_scratch:\n  .zero 16\n" ++
  "bal_serializer_throwaway_ctx:\n  .zero 208\n" ++
  "bal_builder_storage_changes:\n  .zero " ++ toString balBuilderStorageChangeBytes ++ "\n" ++
  "bal_builder_balance_changes:\n  .zero " ++ toString balBuilderBalanceBytes ++ "\n" ++
  "bal_builder_nonce_changes:\n  .zero " ++ toString balBuilderNonceBytes ++ "\n" ++
  "bal_builder_code_changes:\n  .zero " ++ toString balBuilderCodeBytes ++ "\n"

/-! ## Account interning

`ensure_account` is the only builder writer allowed to create an account-table
entry.  It performs a bytewise comparison over the canonical BE20 key and
appends only on a miss, so every address has exactly one stable table index
during execution.  Event rows duplicate the same address for sorting; the
table remains the single source for existence and touched-account dedup.

Calling convention:

* `a0` = pointer to a canonical 20-byte big-endian address;
* return `a0` = stable table index, or `-1` after latching overflow.

The bytewise implementation deliberately avoids unaligned word loads: BE20
addresses have no eight-byte alignment guarantee. -/
def balBuilderEnsureAccountFunction : String :=
  "bal_builder_ensure_account:\n" ++
  "  addi sp, sp, -48; sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp); sd s3, 24(sp); sd s4, 32(sp); sd s5, 40(sp)\n" ++
  "  mv s0, a0; la s1, bal_builder_account_count; ld s2, 0(s1); li s3, 0; la s4, bal_builder_accounts\n" ++
  ".Lbabe_scan:\n" ++
  "  bgeu s3, s2, .Lbabe_append\n" ++
  -- `s5 = accounts + 24 * index` as (i*3)*8, without a multiply extension dependency.
  -- 24 is the ROW stride; only the low 20 bytes are the address, the rest is padding.
  "  slli s5, s3, 1; add s5, s5, s3; slli s5, s5, 3; add s5, s4, s5; li t0, 20; mv t1, s5; mv t2, s0\n" ++
  ".Lbabe_cmp:\n" ++
  "  beqz t0, .Lbabe_hit; lbu t3, 0(t1); lbu t4, 0(t2); bne t3, t4, .Lbabe_next; addi t1, t1, 1; addi t2, t2, 1; addi t0, t0, -1; j .Lbabe_cmp\n" ++
  ".Lbabe_next:\n" ++
  "  addi s3, s3, 1; j .Lbabe_scan\n" ++
  ".Lbabe_append:\n" ++
  "  li t0, " ++ toString balBuilderAccountCapacity ++ "; bgeu s2, t0, .Lbabe_overflow\n" ++
  "  slli s5, s2, 1; add s5, s5, s2; slli s5, s5, 3; add s5, s4, s5; li t0, 20; mv t1, s5; mv t2, s0\n" ++
  ".Lbabe_copy:\n" ++
  "  beqz t0, .Lbabe_append_done; lbu t3, 0(t2); sb t3, 0(t1); addi t1, t1, 1; addi t2, t2, 1; addi t0, t0, -1; j .Lbabe_copy\n" ++
  ".Lbabe_append_done:\n" ++
  "  addi t0, s2, 1; sd t0, 0(s1); mv s3, s2\n" ++
  ".Lbabe_hit:\n" ++
  "  mv a0, s3; j .Lbabe_ret\n" ++
  ".Lbabe_overflow:\n" ++
  "  la t0, bal_builder_overflow; li t1, 1; sd t1, 0(t0); li a0, -1\n" ++
  ".Lbabe_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp); addi sp, sp, 48; ret\n"

/-! ## Non-storage append primitives

These mirror `add_balance_change`, `add_nonce_change`, and `add_code_change`.
They are consumed by one transaction-boundary walk of `tx_account_writes`,
whose upsert key is the account address.  That map, rather than an informal
caller convention, supplies exactly one final post-state per address at the
fixed transaction BAI; the walk must occur before
`account_writes_incorporate_tx` clears the transaction map.

All three first intern the address for the builder's account/touched set, then
copy that same BE20 key into the event row for the canonical sorter.  A full
arena latches both its component bit and `bal_builder_overflow`; the common
verdict gate will reject rather than truncate an event stream.
-/
def balBuilderAppendBalanceFunction : String :=
  "bal_builder_append_balance:\n" ++
  "  addi sp, sp, -40; sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp); sd a2, 24(sp)\n" ++
  "  jal ra, bal_builder_ensure_account; bltz a0, .Lbabb_overflow\n" ++
  "  la t0, bal_builder_balance_count; ld t1, 0(t0); li t2, " ++ toString balBuilderBalanceCapacity ++ "; bgeu t1, t2, .Lbabb_overflow\n" ++
  "  slli t2, t1, 6; la t3, bal_builder_balance_changes; add t3, t3, t2; ld t4, 8(sp); li t5, 20\n" ++
  ".Lbabb_addr:\n" ++
  "  beqz t5, .Lbabb_bai; lbu t6, 0(t4); sb t6, 0(t3); addi t4, t4, 1; addi t3, t3, 1; addi t5, t5, -1; j .Lbabb_addr\n" ++
  ".Lbabb_bai:\n" ++
  "  la t3, bal_builder_balance_changes; slli t2, t1, 6; add t3, t3, t2; ld t4, 16(sp); sd t4, 24(t3); ld t4, 24(sp); ld t5, 0(t4); sd t5, 32(t3); ld t5, 8(t4); sd t5, 40(t3); ld t5, 16(t4); sd t5, 48(t3); ld t5, 24(t4); sd t5, 56(t3); addi t1, t1, 1; la t0, bal_builder_balance_count; sd t1, 0(t0); li a0, 0; j .Lbabb_ret\n" ++
  ".Lbabb_overflow:\n" ++
  "  la t0, bal_builder_balance_overflow; li t1, 1; sd t1, 0(t0); la t0, bal_builder_overflow; sd t1, 0(t0); li a0, 1\n" ++
  ".Lbabb_ret:\n" ++
  "  ld ra, 0(sp); addi sp, sp, 40; ret\n"

/-! ## `bal_builder_record_storage_change`

    Mirrors `add_storage_write` (`block_access_lists.py:334-367`).

    **It is an UPSERT, not an append**, which is why it is not named `append_storage`
    like its three siblings. The spec walks the slot's existing changes and, if one
    already carries this `block_access_index`, REPLACES its value and returns —
    "keeping only the final write" (`:346`). Only on no match does it append. A
    caller invoking an append-named routine twice for one
    `(address, slot, block_access_index)` would get two rows where the spec keeps one,
    and the resulting BAL would be well-formed with the wrong entry count.

    Calling convention:
      a0 = address ptr (20 B big-endian)
      a1 = block_access_index (u64)
      a2 = slot ptr  (32 B, canonical big-endian BAL key)
      a3 = value ptr (32 B, the post value)
      ra = return
      no result register; overflow is reported via the builder's flags.

    Row layout, 96 B (`balBuilderStorageChangeRowBytes`), matching the documented
    `{address[20], pad[4], u64 BAI, slot[32], post value[32]}`:

        +0  address (20 B, 4 B pad to +24)
        +24 block_access_index (u64)
        +32 slot   (32 B)
        +64 value  (32 B)

    That is exactly what `balSortBuilderStorageSegments` decodes to — segment 0 at
    offset 0 width 20 big-endian, segment 1 at offset 32 width 32 big-endian,
    segment 2 at offset 24 width 8 little-endian — so the sorter consumes the spec's
    ordering key in-row with no remap. -/
def balBuilderRecordStorageChangeFunction : String :=
  "bal_builder_record_storage_change:\n" ++
  "  addi sp, sp, -48; sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp); sd a2, 24(sp); sd a3, 32(sp)\n" ++
  "  jal ra, bal_builder_ensure_account; bltz a0, .Lbrsc_overflow\n" ++
  -- UPSERT SCAN: find an existing row with this (address, slot, BAI) and overwrite
  -- its value in place. This is the half that `append` would have omitted.
  "  la t0, bal_builder_storage_change_count; ld t1, 0(t0)\n" ++
  "  li t4, 0\n" ++                                            -- t4 = scan index
  ".Lbrsc_scan:\n" ++
  "  bgeu t4, t1, .Lbrsc_append\n" ++
  "  li t2, 96; mul t2, t4, t2; la t3, bal_builder_storage_changes; add t5, t3, t2\n" ++
  -- BAI first: it is one dword and discriminates fastest.
  "  ld t2, 24(t5); ld t6, 16(sp); bne t2, t6, .Lbrsc_next\n" ++
  -- slot (4 dwords at +32)
  "  ld a4, 24(sp)\n" ++
  "  ld t2, 32(t5); ld t6, 0(a4);  bne t2, t6, .Lbrsc_next\n" ++
  "  ld t2, 40(t5); ld t6, 8(a4);  bne t2, t6, .Lbrsc_next\n" ++
  "  ld t2, 48(t5); ld t6, 16(a4); bne t2, t6, .Lbrsc_next\n" ++
  "  ld t2, 56(t5); ld t6, 24(a4); bne t2, t6, .Lbrsc_next\n" ++
  -- address (20 bytes at +0, compared byte-wise so the 4 pad bytes cannot matter)
  "  ld a4, 8(sp); li t2, 20; mv t6, t5\n" ++
  ".Lbrsc_acmp:\n" ++
  "  beqz t2, .Lbrsc_hit\n" ++
  "  lbu a5, 0(a4); lbu a6, 0(t6); bne a5, a6, .Lbrsc_next\n" ++
  "  addi a4, a4, 1; addi t6, t6, 1; addi t2, t2, -1; j .Lbrsc_acmp\n" ++
  ".Lbrsc_next:\n" ++
  "  addi t4, t4, 1; j .Lbrsc_scan\n" ++
  ".Lbrsc_hit:\n" ++
  -- Same (address, slot, BAI): keep only the final write -- overwrite and return
  -- WITHOUT bumping the count.
  "  ld a4, 32(sp)\n" ++
  "  ld t2, 0(a4);  sd t2, 64(t5)\n" ++
  "  ld t2, 8(a4);  sd t2, 72(t5)\n" ++
  "  ld t2, 16(a4); sd t2, 80(t5)\n" ++
  "  ld t2, 24(a4); sd t2, 88(t5)\n" ++
  "  j .Lbrsc_ret\n" ++
  ".Lbrsc_append:\n" ++
  "  li t2, " ++ toString balBuilderStorageChangeCapacity ++ "\n" ++
  "  bgeu t1, t2, .Lbrsc_overflow\n" ++
  "  li t2, 96; mul t2, t1, t2; la t3, bal_builder_storage_changes; add t5, t3, t2\n" ++
  -- address: 20 bytes, byte-wise (the source is a 20-byte BE address, not padded)
  "  ld a4, 8(sp); li t2, 20; mv t6, t5\n" ++
  ".Lbrsc_wa:\n" ++
  "  beqz t2, .Lbrsc_wpad; lbu a5, 0(a4); sb a5, 0(t6); addi a4, a4, 1; addi t6, t6, 1; addi t2, t2, -1; j .Lbrsc_wa\n" ++
  ".Lbrsc_wpad:\n" ++
  "  sb zero, 20(t5); sb zero, 21(t5); sb zero, 22(t5); sb zero, 23(t5)\n" ++
  "  ld t2, 16(sp); sd t2, 24(t5)\n" ++                         -- BAI
  "  ld a4, 24(sp)\n" ++
  "  ld t2, 0(a4);  sd t2, 32(t5)\n" ++
  "  ld t2, 8(a4);  sd t2, 40(t5)\n" ++
  "  ld t2, 16(a4); sd t2, 48(t5)\n" ++
  "  ld t2, 24(a4); sd t2, 56(t5)\n" ++
  "  ld a4, 32(sp)\n" ++
  "  ld t2, 0(a4);  sd t2, 64(t5)\n" ++
  "  ld t2, 8(a4);  sd t2, 72(t5)\n" ++
  "  ld t2, 16(a4); sd t2, 80(t5)\n" ++
  "  ld t2, 24(a4); sd t2, 88(t5)\n" ++
  "  addi t1, t1, 1; la t0, bal_builder_storage_change_count; sd t1, 0(t0)\n" ++
  "  j .Lbrsc_ret\n" ++
  ".Lbrsc_overflow:\n" ++
  "  la t0, bal_builder_storage_change_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  "  la t0, bal_builder_overflow; sd t1, 0(t0)\n" ++
  ".Lbrsc_ret:\n" ++
  "  ld ra, 0(sp); addi sp, sp, 48; ret\n"

def balBuilderAppendNonceFunction : String :=
  "bal_builder_append_nonce:\n" ++
  "  addi sp, sp, -40; sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp); sd a2, 24(sp)\n" ++
  "  jal ra, bal_builder_ensure_account; bltz a0, .Lbabc_overflow\n" ++
  "  la t0, bal_builder_nonce_count; ld t1, 0(t0); li t2, " ++ toString balBuilderNonceCapacity ++ "; bgeu t1, t2, .Lbabc_overflow\n" ++
  "  slli t2, t1, 2; add t2, t2, t1; slli t2, t2, 3; la t3, bal_builder_nonce_changes; add t3, t3, t2; ld t4, 8(sp); li t5, 20\n" ++
  ".Lbabc_addr:\n" ++
  "  beqz t5, .Lbabc_bai; lbu t6, 0(t4); sb t6, 0(t3); addi t4, t4, 1; addi t3, t3, 1; addi t5, t5, -1; j .Lbabc_addr\n" ++
  ".Lbabc_bai:\n" ++
  "  la t3, bal_builder_nonce_changes; slli t2, t1, 2; add t2, t2, t1; slli t2, t2, 3; add t3, t3, t2; ld t4, 16(sp); sd t4, 24(t3); ld t4, 24(sp); sd t4, 32(t3); addi t1, t1, 1; la t0, bal_builder_nonce_count; sd t1, 0(t0); li a0, 0; j .Lbabc_ret\n" ++
  ".Lbabc_overflow:\n" ++
  "  la t0, bal_builder_nonce_overflow; li t1, 1; sd t1, 0(t0); la t0, bal_builder_overflow; sd t1, 0(t0); li a0, 1\n" ++
  ".Lbabc_ret:\n" ++
  "  ld ra, 0(sp); addi sp, sp, 40; ret\n"

def balBuilderAppendCodeFunction : String :=
  "bal_builder_append_code:\n" ++
  "  addi sp, sp, -48; sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp); sd a2, 24(sp); sd a3, 32(sp)\n" ++
  "  jal ra, bal_builder_ensure_account; bltz a0, .Lbabcod_overflow\n" ++
  "  la t0, bal_builder_code_count; ld t1, 0(t0); li t2, " ++ toString balBuilderCodeCapacity ++ "; bgeu t1, t2, .Lbabcod_overflow\n" ++
  "  slli t2, t1, 6; la t3, bal_builder_code_changes; add t3, t3, t2; ld t4, 8(sp); li t5, 20\n" ++
  ".Lbabcod_addr:\n" ++
  "  beqz t5, .Lbabcod_bai; lbu t6, 0(t4); sb t6, 0(t3); addi t4, t4, 1; addi t3, t3, 1; addi t5, t5, -1; j .Lbabcod_addr\n" ++
  ".Lbabcod_bai:\n" ++
  "  la t3, bal_builder_code_changes; slli t2, t1, 6; add t3, t3, t2; ld t4, 16(sp); sd t4, 24(t3); ld t4, 24(sp); sd t4, 32(t3); ld t4, 32(sp); sd t4, 40(t3); addi t1, t1, 1; la t0, bal_builder_code_count; sd t1, 0(t0); li a0, 0; j .Lbabcod_ret\n" ++
  ".Lbabcod_overflow:\n" ++
  "  la t0, bal_builder_code_overflow; li t1, 1; sd t1, 0(t0); la t0, bal_builder_overflow; sd t1, 0(t0); li a0, 1\n" ++
  ".Lbabcod_ret:\n" ++
  "  ld ra, 0(sp); addi sp, sp, 48; ret\n"

/-! ## `bal_emit_storage_changes`

    Emits this transaction's storage CHANGES into the builder, applying the spec's
    net-zero exclusion (`block_access_lists.py:667-676`).

    ## Where the baseline comes from — no capture and no carry

    The spec compares each write against
    `_get_pre_tx_storage(block_state.storage_writes, pre_state, ...)`: the block
    container if the slot is present, else pre-state. Both halves are readable AT THE
    MOMENT OF USE:

    * **Container hit** — the block-level scan already distinguishes found from
      not-found, so the discriminator comes from the scan and nothing needs storing.
      This must run BEFORE the tx→block merge, which is why it is called from the top
      of `write_sets_incorporate_tx`: the spec does the same, and says so
      (`state_tracker.py`: "Update BAL builder before merging writes into block
      state").
    * **Container miss** — `slot_at_header_state_root` against the PARENT header.

    The four arguments that read needs come from **globals `block_verdict` already
    publishes** at its own top, before this runs:

    | global | source | meaning |
    |---|---|---|
    | `sv_pre_rlp_ptr` | `params+8` | PARENT header rlp ptr |
    | `sv_pre_rlp_len` | `params+16` | PARENT header rlp len |
    | `bv_witness_state_ptr` | `params+80` | witness section ptr |
    | `bv_witness_state_len` | `params+88` | witness section len |

    That is the property that makes this design immune to what defeated four earlier
    attempts at the same value: nothing is carried, nothing's validity depends on which
    path arrived, and the reads are identical on every path by construction.

    **`sv_pre_rlp_*`, never `sv_this_rlp`** — the latter is this block's POST-state
    header and would silently return a post-state baseline.

    State and storage are passed as ONE section twice, matching the working SSTORE-side
    caller: this guest has a single witness section, not separate state and storage.

    ## ABSENT IS NOT ZERO

    A container miss does NOT mean the baseline is zero. `_get_pre_tx_storage` falls
    back to pre-state, which can be nonzero, and its "Returns `0` if not set" is about
    PRE-STATE being unset rather than about the container. Treating a miss as zero
    emits a spurious entry for every first-write-in-block to a nonzero slot — a
    well-formed BAL with the wrong entry count and therefore the wrong hash.

    ## Encodings

    Tx rows hold EVM stack words (little-endian limbs); `slot_at_header_state_root`
    wants a 20-byte BE address and a 32-byte BE slot, and the builder row wants BE20 +
    BE32 to match `balSortBuilderStorageSegments`. So the address and slot are reversed
    into scratch before either call — the same conversion the SSTORE path already does
    for its own lookup (`.Lsstore_prestate_addr_rev` / `.Lsstore_prestate_key_rev`).
    The VALUE needs no conversion: container, tx row and builder row all hold LE limbs,
    and the RLP scalar encoder consumes that form.

    a0 = block_access_index for this transaction.

    INERT: nothing calls this yet. -/
def balEmitStorageChangesFunction : String :=
  "bal_emit_storage_changes:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  sd s7, 64(sp); sd s8, 72(sp); sd a0, 80(sp)\n" ++          -- 80(sp) = BAI
  "  la s0, tx_storage_writes_count; ld s1, 0(s0)\n" ++          -- s1 = tx row count
  "  li s2, 0xa21a0000\n" ++                                    -- s2 = tx rows
  "  li s3, 0\n" ++                                             -- s3 = i
  ".Lbesc_loop:\n" ++
  "  bgeu s3, s1, .Lbesc_done\n" ++
  "  slli s4, s3, 7; add s4, s2, s4\n" ++                        -- s4 = &txrow[i]
  -- ---- baseline: scan the BLOCK container for (addr, slot) ----
  "  la t0, storage_writes_count; ld t1, 0(t0)\n" ++
  "  li t3, 0xa1fa0000; li t4, 0\n" ++
  "  li s5, 0\n" ++                                             -- s5 = &baseline or 0
  ".Lbesc_scan:\n" ++
  "  bgeu t4, t1, .Lbesc_miss\n" ++
  "  slli t2, t4, 7; add t5, t3, t2\n" ++
  "  ld t2, 0(t5);  ld t6, 0(s4);  bne t2, t6, .Lbesc_next\n" ++
  "  ld t2, 8(t5);  ld t6, 8(s4);  bne t2, t6, .Lbesc_next\n" ++
  "  ld t2, 16(t5); ld t6, 16(s4); bne t2, t6, .Lbesc_next\n" ++
  "  ld t2, 24(t5); ld t6, 24(s4); bne t2, t6, .Lbesc_next\n" ++
  "  ld t2, 32(t5); ld t6, 32(s4); bne t2, t6, .Lbesc_next\n" ++
  "  ld t2, 40(t5); ld t6, 40(s4); bne t2, t6, .Lbesc_next\n" ++
  "  ld t2, 48(t5); ld t6, 48(s4); bne t2, t6, .Lbesc_next\n" ++
  "  ld t2, 56(t5); ld t6, 56(s4); bne t2, t6, .Lbesc_next\n" ++
  "  addi s5, t5, 64; j .Lbesc_have\n" ++                        -- HIT: container value
  ".Lbesc_next:\n" ++
  "  addi t4, t4, 1; j .Lbesc_scan\n" ++
  ".Lbesc_miss:\n" ++
  -- Reverse address (20 B) and slot (32 B) into scratch for the BE-keyed reader.
  "  la t0, besc_addr_be; li t1, 20; addi t2, s4, 19\n" ++
  ".Lbesc_arev:\n" ++
  "  beqz t1, .Lbesc_arev_done; lbu t5, 0(t2); sb t5, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1; j .Lbesc_arev\n" ++
  ".Lbesc_arev_done:\n" ++
  "  la t0, besc_slot_be; li t1, 32; addi t2, s4, 63\n" ++
  ".Lbesc_srev:\n" ++
  "  beqz t1, .Lbesc_srev_done; lbu t5, 0(t2); sb t5, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1; j .Lbesc_srev\n" ++
  ".Lbesc_srev_done:\n" ++
  -- ABSENT IS NOT ZERO: read pre-state via the PARENT header, from the globals
  -- block_verdict publishes. sv_pre_rlp_*, never sv_this_rlp (post-state).
  "  la t0, sv_pre_rlp_ptr; ld a0, 0(t0)\n" ++
  "  la t0, sv_pre_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, besc_addr_be; la a3, besc_slot_be\n" ++
  "  la t0, bv_witness_state_ptr; ld a4, 0(t0); ld a6, 0(t0)\n" ++
  "  la t0, bv_witness_state_len; ld a5, 0(t0); ld a7, 0(t0)\n" ++
  "  jal ra, slot_at_header_state_root\n" ++
  "  bnez a0, .Lbesc_zero_base\n" ++                             -- no proof => treat as 0
  -- sahsr_u256 is canonical BE; reverse to LE limbs so it compares against the row.
  "  la t0, besc_base_le; li t1, 32; la t2, sahsr_u256; addi t2, t2, 31\n" ++
  ".Lbesc_brev:\n" ++
  "  beqz t1, .Lbesc_brev_done; lbu t5, 0(t2); sb t5, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1; j .Lbesc_brev\n" ++
  ".Lbesc_brev_done:\n" ++
  "  la s5, besc_base_le; j .Lbesc_have\n" ++
  ".Lbesc_zero_base:\n" ++
  "  la t0, besc_base_le; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la s5, besc_base_le\n" ++
  ".Lbesc_have:\n" ++
  -- ---- net-zero exclusion: emit only when baseline != post ----
  "  addi s6, s4, 64\n" ++                                       -- s6 = &post
  "  ld t2, 0(s5);  ld t6, 0(s6);  bne t2, t6, .Lbesc_emit\n" ++
  "  ld t2, 8(s5);  ld t6, 8(s6);  bne t2, t6, .Lbesc_emit\n" ++
  "  ld t2, 16(s5); ld t6, 16(s6); bne t2, t6, .Lbesc_emit\n" ++
  "  ld t2, 24(s5); ld t6, 24(s6); bne t2, t6, .Lbesc_emit\n" ++
  -- NET-ZERO EXCLUSION, verified at `block_access_lists.py:667-676`: the spec calls
  -- `add_storage_write` only `if pre_value != post_value`, and `pre_value` comes from
  -- `_get_pre_tx_storage(block_state.storage_writes, pre_state, ...)` -- the BLOCK
  -- cumulative value, not the transaction's own pre-state. That is why the baseline
  -- here is the block container first and the header state root only on a miss.
  --
  -- The same lines settle the slot's type: `u256_slot = U256.from_be_bytes(key)`, so the
  -- BAL slot is a NUMERIC U256 and encodes as a minimal-length scalar with leading zeros
  -- dropped -- not as a fixed 32-byte string.
  "  j .Lbesc_advance\n" ++                                      -- net-zero: emit nothing
  ".Lbesc_emit:\n" ++
  -- The builder row wants BE20 address and BE32 slot, matching
  -- balSortBuilderStorageSegments. Reverse again on this path -- the miss path may not
  -- have run.
  "  la t0, besc_addr_be; li t1, 20; addi t2, s4, 19\n" ++
  ".Lbesc_arev2:\n" ++
  "  beqz t1, .Lbesc_arev2_done; lbu t5, 0(t2); sb t5, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1; j .Lbesc_arev2\n" ++
  ".Lbesc_arev2_done:\n" ++
  "  la t0, besc_slot_be; li t1, 32; addi t2, s4, 63\n" ++
  ".Lbesc_srev2:\n" ++
  "  beqz t1, .Lbesc_srev2_done; lbu t5, 0(t2); sb t5, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1; j .Lbesc_srev2\n" ++
  ".Lbesc_srev2_done:\n" ++
  "  la a0, besc_addr_be; ld a1, 80(sp); la a2, besc_slot_be; addi a3, s4, 64\n" ++
  "  jal ra, bal_builder_record_storage_change\n" ++
  ".Lbesc_advance:\n" ++
  "  addi s3, s3, 1; j .Lbesc_loop\n" ++
  ".Lbesc_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  ld s7, 64(sp); ld s8, 72(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n"

def blockAccessListBuilderFunctions : String :=
  balSerializerAddrMatchesFunction ++
  balSerializerAddrMatchesBeFunction ++
  balSerializerSlotEqFunction ++
  balSerializerSlotWrittenFunction ++
  balSerializerSlotSeenBeforeFunction ++
  balSerializerU64ToFieldFunction ++
  balSerializerFilterReadsFunction ++
  balSerializerMeasureReadsFunction ++
  balSerializerSlotToLeFunction ++
  balSerializerMeasureSlotFunction ++
  balSerializerMeasureStorageFunction ++
  balSerializerMeasureBalanceFunction ++
  balSerializerMeasureNonceFunction ++
  balSerializerMeasureCodeFunction ++
  balSerializerMeasureAccountFunction ++
  balSerializerEmitStorageFunction ++
  balSerializerEmitReadsFunction ++
  balSerializerEmitBalanceFunction ++
  balSerializerEmitNonceFunction ++
  balSerializerEmitCodeFunction ++
  balSerializerEmitAccountFunction ++
  balSerializerMeasureOuterFunction ++
  balSerializerEmitOuterFunction ++
  balSerializerRebuildHashFunction ++
  balSerializerVerifyFunction ++
  balBuilderEnsureAccountFunction ++
  balBuilderRecordStorageChangeFunction ++
  balEmitStorageChangesFunction ++
  balBuilderAppendBalanceFunction ++
  balBuilderAppendNonceFunction ++
  balBuilderAppendCodeFunction

/-! ## Guards for the rebuild-and-compare pair -/

#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_rebuild_hash:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_verify:").length == 2

-- The sort happens inside `rebuild_hash`, before any byte is absorbed. An unsorted
-- emission is a well-formed BAL with the wrong hash and is the ONE failure the digest
-- comparison cannot localise, so this must not become a caller's responsibility.
-- SIX calls, not one: see the seven-rule guard below. This originally pinned the single
-- account sort, back when that was the only ordering implemented.

-- The descriptor must carry the BIG-ENDIAN flag (0x80) in its width byte: 0x94 is
-- `0x80 | 20`. This is the same value `bal_sort_account_writes` passes, pinned on that
-- side by the matching guard in BalCanonicalSort.lean. Writing 0x1400 declares a
-- big-endian address little-endian and faults inside the sort on a bad pointer.
#guard (balSerializerRebuildHashFunction.splitOn "li a3, 0x9400").length == 2

-- ALL SEVEN ORDERING RULES, as FIVE sort calls: storage (carrying two rules in one
-- multi-segment pass), reads, balance, nonce, code, accounts. Six of these were missing
-- entirely and no probe could see it, because a one-element list is sorted by definition
-- and every case had one element at every inner level.
#guard (balSerializerRebuildHashFunction.splitOn "jal ra, bal_canonical_sort").length == 7
-- Every stride 8-ALIGNED: 96, 64, 64, 40, 64, 24.
#guard (balSerializerRebuildHashFunction.splitOn "li a2, 96;").length == 2
#guard (balSerializerRebuildHashFunction.splitOn "li a2, 40;").length == 2
#guard [96, 64, 40, 24].all (fun w => w % 8 == 0)

-- Stride 24, which is 8-ALIGNED, per the rule on `balBuilderAccountRowBytes`: the sort
-- swaps rows with ld/sd, and AGENTS.md:211 gives those no semantics off an 8-boundary.
#guard (balSerializerRebuildHashFunction.splitOn "li a2, 24").length == 2
#guard balBuilderAccountRowBytes % 8 == 0
-- ...and it must precede the emission, not follow it.
#guard (((balSerializerRebuildHashFunction.splitOn "jal ra, bal_canonical_sort").getD 0 "").splitOn "bal_serializer_emit_outer").length == 1

-- A nonzero sort status must abort rather than fall through to emitting an unsorted BAL.
#guard (balSerializerRebuildHashFunction.splitOn "  beqz a0, .Lbsrh_sorted\n").length == 2

-- The comparison is a full 32 bytes, four dwords. Comparing fewer accepts a collision on
-- the compared prefix, which is the one way a hash check can be weaker than it looks.
#guard (balSerializerVerifyFunction.splitOn "bne t2, t3, .Lbsv_differ").length == 5

-- Verify must hash the SUPPLIED bal through the routine the verdict path already uses,
-- not re-derive it. Two hashes of the same bytes by two implementations is a way to
-- agree by construction rather than by correctness.
#guard (balSerializerVerifyFunction.splitOn "jal ra, block_access_list_hash").length == 2

/-! ## Guards for the outer accumulation -/

#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_measure_outer:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_outer:").length == 2
-- The outer payload is a sum of ENCODED sizes. Summing the accounts' payloads instead
-- leaves the outer header short by one header per account -- well-formed RLP, wrong
-- hash, and no intermediate check notices. The `list_header_len` call is the conversion.
#guard (balSerializerMeasureOuterFunction.splitOn "jal ra, bal_rlp_list_header_len").length == 2
#guard (balSerializerMeasureOuterFunction.splitOn "  add s2, s2, t5; add s2, s2, a0\n").length == 2

-- Each account is re-measured immediately before being emitted. The length table holds
-- ONE account, and `measure_outer` leaves it on whichever account it saw last, so
-- emitting without re-measuring would give every account the last one's headers.
#guard (balSerializerEmitOuterFunction.splitOn "jal ra, bal_serializer_measure_account").length == 2
#guard (balSerializerEmitOuterFunction.splitOn "jal ra, bal_serializer_emit_account").length == 2

-- It does NOT sort. Ordering is `bal_canonical_sort`'s job and must precede this; an
-- unsorted emission is a well-formed BAL with the wrong hash. Pinning the absence keeps
-- the docstring's claim and the code in agreement.
#guard (balSerializerEmitOuterFunction.splitOn "bal_canonical_sort").length == 1

/-! ## `block_access_index` values, verified against the spec

    The spec assigns the index in `fork.py`:

      per transaction   `block_access_index = index + Uint(1)`  (`:1040`), so the 0-based
                        transaction `i` stamps `i + 1`
      post-execution    `ulen(transactions) + Uint(1)`          (`:917`), i.e. N+1
      system            0, the value before any transaction sets it

    The guest matches the transaction case exactly:
    `BlockVerdictMtxRuntime.lean:407` and `:448` compute `bv_mtx_i + 1` into
    `current_block_access_index`, and `bv_mtx_i` is the 0-based transaction index.

    THE OTHER TWO CASES HAVE NO PRODUCER IN THE GUEST. Nothing stamps 0 and nothing
    stamps N+1, so system-level and post-execution changes cannot appear in a rebuilt
    BAL at all. That is a PRODUCER gap, not a serializer one -- the emitters encode
    whatever index the row carries -- but it bounds what a digest comparison can prove:
    a block whose only divergence is a missing system-level change would still be
    accepted, because neither side of the comparison would contain it.

    Recorded here because the serializer is where someone will look for it. -/

/-! ## Guards for the CHANGE-STRUCT field order

    Verified against the class definitions in `block_access_lists.py`: `StorageChange`,
    `BalanceChange`, `NonceChange` and `CodeChange` all declare `block_access_index`
    FIRST and the value second; `SlotChanges` is `slot` then `changes`. Every emitter
    matches.

    Nothing pinned that. Each change is a two-element positional RLP list, so emitting
    the value before the index produces a well-formed change with its members
    transposed -- and when both encode to one byte, as `index 1` and `value 5` do, the
    only difference is which byte is which. A wrong order here is a wrong BAL that
    decodes cleanly at every level.

    Same gap as the `AccountChanges` field order, one level down, and found the same
    way: by enumerating what had been carried from prose rather than read. -/

-- index BEFORE value, in each of the four change emitters. Keyed on adjacency: the
-- scalar emitted from `bal_serializer_u64_field` (the widened index) must precede the
-- one emitted from the row's value offset.
#guard (((balSerializerEmitBalanceFunction.splitOn "la a1, bal_serializer_u64_field; mv a2, s2; jal ra, bal_rlp_emit_scalar").getD 1 "").splitOn "addi a1, t3, 32; mv a2, s2; jal ra, bal_rlp_emit_scalar").length == 2
#guard (((balSerializerEmitCodeFunction.splitOn "la a1, bal_serializer_u64_field; mv a2, s2; jal ra, bal_rlp_emit_scalar").getD 1 "").splitOn "jal ra, bal_rlp_emit_bytes").length == 2
#guard (((balSerializerEmitStorageFunction.splitOn "la a1, bal_serializer_u64_field; mv a2, s2; jal ra, bal_rlp_emit_scalar").getD 1 "").splitOn "addi a1, t3, 64; mv a2, s2; jal ra, bal_rlp_emit_scalar").length == 2
-- Nonce emits the index and the nonce from the SAME buffer, re-widened between the two,
-- so adjacency cannot separate them; pin the re-widen count instead. Four widens: two to
-- measure the pair, two to re-emit it in order.
#guard (balSerializerEmitNonceFunction.splitOn "jal ra, bal_serializer_u64_to_field").length == 5

-- SlotChanges is `slot` then `changes`: the slot scalar must precede the inner list.
#guard (((balSerializerEmitStorageFunction.splitOn "jal ra, bal_serializer_slot_to_le").getD 1 "").splitOn "mv a1, s7; mv a2, s2; jal ra, bal_rlp_emit_list_header").length == 2

/-! ## Guards for the field emitters and the account emitter -/

#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_reads:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_balance:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_nonce:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_code:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_account:").length == 2

-- The reads emitter uses the REVERSING comparator, matching its measurer. Read rows come
-- from the exec log and hold an LE stack word; builder rows are big-endian. Swapping the
-- two comparators silently matches nothing rather than erroring.
#guard (balSerializerEmitReadsFunction.splitOn "jal ra, bal_serializer_addr_matches\n").length == 2
#guard (balSerializerEmitReadsFunction.splitOn "addr_matches_be").length == 1
-- ...and every OTHER emitter uses the big-endian one.
#guard (balSerializerEmitBalanceFunction.splitOn "jal ra, bal_serializer_addr_matches_be").length == 2
#guard (balSerializerEmitNonceFunction.splitOn "jal ra, bal_serializer_addr_matches_be").length == 2
#guard (balSerializerEmitCodeFunction.splitOn "jal ra, bal_serializer_addr_matches_be").length == 2

-- Nonce widens FOUR times, not two: the scalar field is one shared buffer, so measuring
-- the pair overwrites it and both members must be re-widened before being emitted.
-- Emitting straight after the measure loop sends the nonce twice and drops the index.
#guard (balSerializerEmitNonceFunction.splitOn "jal ra, bal_serializer_u64_to_field").length == 5

-- The account emitter reads SIX table entries and emits six headers; it must never
-- recompute a length. And the address goes through emit_bytes, never emit_address.
#guard (balSerializerEmitAccountFunction.splitOn "jal ra, bal_rlp_emit_list_header").length == 7
#guard (balSerializerEmitAccountFunction.splitOn "la t0, bal_serializer_len_table").length == 7
#guard (balSerializerEmitAccountFunction.splitOn "bal_rlp_emit_address").length == 1
#guard (balSerializerEmitAccountFunction.splitOn "jal ra, bal_rlp_emit_bytes").length == 2
-- All five field emitters called, in AccountChanges order.
-- All five field emitters, IN AccountChanges ORDER. An RLP list is positional: swapping
-- two field emitters yields a well-formed account with the fields exchanged, and if both
-- are empty lists it is byte-identical. Order pinned by the sequence below, not by count
-- alone.
#guard (balSerializerEmitAccountFunction.splitOn "jal ra, bal_serializer_emit_").length == 6
#guard (((balSerializerEmitAccountFunction.splitOn "jal ra, bal_serializer_emit_storage").getD 1 "").splitOn "jal ra, bal_serializer_emit_reads").length == 2
#guard (((balSerializerEmitAccountFunction.splitOn "jal ra, bal_serializer_emit_reads").getD 1 "").splitOn "jal ra, bal_serializer_emit_balance").length == 2
#guard (((balSerializerEmitAccountFunction.splitOn "jal ra, bal_serializer_emit_balance").getD 1 "").splitOn "jal ra, bal_serializer_emit_nonce").length == 2
#guard (((balSerializerEmitAccountFunction.splitOn "jal ra, bal_serializer_emit_nonce").getD 1 "").splitOn "jal ra, bal_serializer_emit_code").length == 2

/-! ## Guards for the storage emitter -/

#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_storage:").length == 2

-- THREE list headers per slot: SlotChanges, the changes list, and each StorageChange.
-- Same three levels the measurer counts; dropping one leaves well-formed RLP of the
-- wrong shape, and the only symptom is a different digest.
#guard (balSerializerEmitStorageFunction.splitOn "jal ra, bal_rlp_emit_list_header").length == 4

-- Every nested length comes from the SHARED measurer. Emission is streaming, so a header
-- absorbed before its payload cannot be backpatched -- a locally recomputed length is
-- free to drift from the measure pass and nothing but the digest would show it.
#guard (balSerializerEmitStorageFunction.splitOn "jal ra, bal_serializer_measure_slot").length == 2

-- It must NOT use `bal_rlp_emit_address`, which reverses its input for an LE stack word.
-- Builder rows hold the address big-endian, so that helper would silently reverse it.
#guard (balSerializerEmitStorageFunction.splitOn "bal_rlp_emit_address").length == 1

-- Same walk shape as the measurer: address filter at both loop levels, dedup at the outer.
#guard (balSerializerEmitStorageFunction.splitOn "jal ra, bal_serializer_addr_matches_be").length == 3
#guard (balSerializerEmitStorageFunction.splitOn "jal ra, bal_serializer_slot_seen_before").length == 2

/-! ## Guards for the slot byte-order conversion -/

-- `slot_written` compares ACROSS conventions: an LE read slot against a BE row slot, so
-- byte i against byte 31-i. A dword-wise compare matches only palindromic slots.
#guard (balSerializerSlotWrittenFunction.splitOn ".Lbssw_scmp:").length == 2
#guard (balSerializerSlotWrittenFunction.splitOn "ld t5, 32(t4); ld t6, 0(a2)").length == 1

#guard (blockAccessListBuilderDataSection.splitOn "bal_serializer_slot_le:").length == 2

-- BOTH readers of the slot must go through the reversal. The row's slot is BE32 and the
-- scalar pair reads LE limbs, so a direct `row+32` hand-off is the defect this fixes --
-- and it is invisible to any probe that seeds rows in the reader's convention.
#guard (balSerializerMeasureSlotFunction.splitOn "jal ra, bal_serializer_slot_to_le").length == 2
#guard (balSerializerEmitStorageFunction.splitOn "jal ra, bal_serializer_slot_to_le").length == 2
#guard (balSerializerMeasureSlotFunction.splitOn "addi a0, s4, 32; jal ra, bal_rlp_scalar_rlp_len").length == 1
#guard (balSerializerEmitStorageFunction.splitOn "addi a1, s5, 32; mv a2, s2; jal ra, bal_rlp_emit_scalar").length == 1

-- The VALUE is passed verbatim and must NOT be reversed -- same row, opposite convention.
#guard (balSerializerEmitStorageFunction.splitOn "addi a1, t3, 64; mv a2, s2; jal ra, bal_rlp_emit_scalar").length == 2

/-! ## Guards for the shared slot measurement -/

#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_measure_slot:").length == 2

-- The whole point of the factoring is that BOTH passes call it. `measure_storage` must
-- not carry its own copy of the inner walk: two copies of this arithmetic drift, and a
-- drifted emit-side copy shows up only as a wrong digest, with the length table, the
-- per-field measurements and every structural check still agreeing.
#guard (balSerializerMeasureStorageFunction.splitOn "jal ra, bal_serializer_measure_slot").length == 2
#guard (balSerializerMeasureStorageFunction.splitOn ".Lbsms_chg:").length == 1

-- It returns two payloads, not one encoded size. `a1` is the inner changes-list payload,
-- which the emit pass cannot get anywhere else -- the length table holds one entry for
-- the whole field, and the per-slot change count is unbounded.
#guard (balSerializerMeasureSlotFunction.splitOn "  mv a0, s5; mv a1, s7\n").length == 2

/-! ## Guards for the storage-change upsert -/

-- Emitted at all.
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_record_storage_change:").length == 2

-- IT MUST BE AN UPSERT. `add_storage_write` (block_access_lists.py:352-367) replaces
-- the value when a row already carries this (address, slot, block_access_index) and
-- appends only on no match. Without the scan this is an append, and a caller invoking
-- it twice for one key gets two rows where the spec keeps one -- a well-formed BAL
-- with the wrong entry count and therefore the wrong hash.
#guard (balBuilderRecordStorageChangeFunction.splitOn ".Lbrsc_scan:").length == 2
#guard (balBuilderRecordStorageChangeFunction.splitOn ".Lbrsc_hit:").length == 2

-- The hit path must NOT bump the count -- that is what "keeping only the final write"
-- means. Guard the COUNT STORE specifically: the bare `sd t1, 0(t0)` also appears on
-- the overflow path twice (two flags), so counting that would pass for the wrong
-- reason. The count is stored exactly once, and only on the append path.
#guard (balBuilderRecordStorageChangeFunction.splitOn
          "la t0, bal_builder_storage_change_count; sd t1, 0(t0)").length == 2
-- ...and the hit path returns without reaching it.
#guard (balBuilderRecordStorageChangeFunction.splitOn "j .Lbrsc_ret").length == 3

-- Row offsets must match the documented layout AND balSortBuilderStorageSegments:
-- address@0, BAI@24, slot@32, value@64. A stride or offset drift here is silent --
-- the sorter would key on the wrong bytes and still produce a total order.
#guard (balBuilderRecordStorageChangeFunction.splitOn "sd t2, 24(t5)").length == 2
#guard (balBuilderRecordStorageChangeFunction.splitOn "sd t2, 32(t5)").length == 2
#guard (balBuilderRecordStorageChangeFunction.splitOn "sd t2, 64(t5)").length == 3
#guard (balBuilderRecordStorageChangeFunction.splitOn "li t2, 96").length == 3

-- The prose and the constant must agree on the row size. They did not: the file said
-- "80-byte builder stream" while the constant and the layout said 96, so a walk sized
-- from the prose would read every row after the first at the wrong offset.
#guard balBuilderStorageChangeRowBytes = 96

/-! ## Guards for the storage-change emission -/

-- THE PARENT HEADER, NEVER THIS BLOCK'S. sv_this_rlp is the POST-state header; using
-- it would silently return a post-state baseline, and it is the obvious wrong choice
-- because it is the header available as a global under a shorter name.
#guard (balEmitStorageChangesFunction.splitOn "sv_pre_rlp_ptr").length == 2
#guard (balEmitStorageChangesFunction.splitOn "sv_pre_rlp_len").length == 2
#guard (balEmitStorageChangesFunction.splitOn "sv_this_rlp").length == 1

-- ABSENT IS NOT ZERO: a container miss must reach the pre-state read, not fall through
-- to a zero baseline. Dropping this call turns every first-write-in-block to a nonzero
-- slot into a spurious BAL entry -- well-formed, wrong count, wrong hash, no fault.
#guard (balEmitStorageChangesFunction.splitOn "jal ra, slot_at_header_state_root").length == 2

-- Both keys must be reversed to big-endian before either call: tx rows hold LE stack
-- words, the reader wants BE, and the builder row wants BE to match
-- balSortBuilderStorageSegments. Passing a row field straight through names a
-- DIFFERENT slot -- a well-formed 32-byte wrong answer.
#guard (balEmitStorageChangesFunction.splitOn "besc_addr_be").length == 5
#guard (balEmitStorageChangesFunction.splitOn "besc_slot_be").length == 5

-- The net-zero exclusion must compare all four limbs and skip on equality. Comparing
-- fewer would emit entries the spec omits whenever the differing limb is unchecked.
#guard (balEmitStorageChangesFunction.splitOn "bne t2, t6, .Lbesc_emit").length == 5
#guard (balEmitStorageChangesFunction.splitOn "j .Lbesc_advance").length == 2

-- It must call the UPSERT, not append: same (address, slot, BAI) keeps only the final
-- write.
#guard (balEmitStorageChangesFunction.splitOn "jal ra, bal_builder_record_storage_change").length == 2

-- It must measure the FILTERED list, not the raw read set: measuring the raw set sizes
-- the header for slots emit will not write, and the buffer is well-formed with a long
-- header.
-- It applies BOTH predicates -- the same routines the filter and the emit use -- rather
-- than walking a materialised survivor list, which no longer exists. Re-running one
-- routine cannot diverge from itself, which is what made the list unnecessary.
#guard (balSerializerMeasureReadsFunction.splitOn "jal ra, bal_serializer_slot_written").length == 2
#guard (balSerializerMeasureReadsFunction.splitOn "jal ra, bal_serializer_addr_matches").length == 2
#guard (balSerializerMeasureReadsFunction.splitOn "bal_serializer_read_scratch").length == 1
-- The entry goes in the +16 slot, per the table's pinned layout. A wrong slot is
-- silent: emit reads a plausible number written for another field.
#guard (balSerializerMeasureReadsFunction.splitOn "sd s1, 16(t0)").length == 2
-- Same-layer pair: the scalar measurer whose emitter counterpart is bal_rlp_emit_scalar.
#guard (balSerializerMeasureReadsFunction.splitOn "jal ra, bal_rlp_scalar_rlp_len").length == 2

/-! ## Emission guards

    Every guard above examines a routine's own STRING. **A routine that is defined and never
    concatenated into `blockAccessListBuilderFunctions` passes all of them and does not exist
    in the guest.** Seven routines were in exactly that state — the two measurers reported as
    landed among them — because each was added to the definition list by an edit whose
    concatenation half silently did not apply.

    So the emission is guarded separately, by name, against the string that is actually
    emitted. -/
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_addr_matches:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_addr_matches_be:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_slot_eq:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_slot_written:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_slot_seen_before:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_u64_to_field:").length == 2

-- LITTLE-ENDIAN, matching `bal_rlp_scalar_len` / `bal_rlp_emit_scalar`, which read byte 0
-- as least significant. The reversing loop this replaced put the LSB at byte 31 and made
-- `block_access_index = 1` measure as 33 bytes instead of 1. Pin the single store, and
-- forbid the reversal returning: an index expression of the form `31 - i` is the shape of
-- the bug, and it reads as deliberate BE conversion rather than as a defect.
#guard (balSerializerU64ToFieldFunction.splitOn "  sd a1, 0(a0)\n").length == 2
#guard (balSerializerU64ToFieldFunction.splitOn "li t4, 31; sub t4, t4, t1").length == 1
-- The widener's DESTINATION must be reserved. A routine referencing a missing data symbol
-- builds fine in Lean and fails only at LINK, with a message naming the symbol rather than
-- the routine -- so the reservation is guarded next to the routine that needs it.
#guard (blockAccessListBuilderDataSection.splitOn "bal_serializer_u64_field:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_filter_reads:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_measure_reads:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_measure_storage:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_measure_balance:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_measure_nonce:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_measure_code:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_measure_account:").length == 2
#guard (blockAccessListBuilderDataSection.splitOn "bal_serializer_throwaway_ctx:").length == 2
#guard (blockAccessListBuilderDataSection.splitOn "bal_serializer_hdr_scratch:").length == 2

-- SIX header_len conversions, one per field: the table holds PAYLOADS and the account
-- payload needs each field's ENCODED size. Summing entries directly leaves the account
-- header short by five field headers -- silently, since every list stays well-formed.
#guard (balSerializerMeasureAccountFunction.splitOn "jal ra, bal_rlp_list_header_len").length == 6
-- All five field measurers must be called, or a field contributes zero and its table entry
-- is whatever the previous account left there.
#guard (balSerializerMeasureAccountFunction.splitOn "jal ra, bal_serializer_measure_").length == 6
-- The code measurer must use the throwaway route, never a generic measurer.
#guard (balSerializerMeasureCodeFunction.splitOn "jal ra, bal_rlp_measure_into_throwaway").length == 2
#guard (balSerializerMeasureCodeFunction.splitOn "rlp_bytes_encoded_size").length == 1

/-! ## Guards for the storage_changes measurer -/

-- These four are pinned on the PAIR of functions, because the slot-level arithmetic now
-- lives in `measure_slot` while the field-level walk stays in `measure_storage`. Keying
-- them to one function would let the refactor that moved the content also silence the
-- guard -- the same self-deleting failure as a dropped routine taking its guard with it.
private def balStorageMeasurePair : String :=
  balSerializerMeasureSlotFunction ++ balSerializerMeasureStorageFunction

-- THREE HEADER LEVELS below the field list, against one for balance and none for reads:
-- StorageChange, the changes list, and SlotChanges. Dropping any one leaves every
-- intermediate a well-formed RLP list of the wrong length -- the silent nesting error.
#guard (balStorageMeasurePair.splitOn "jal ra, bal_rlp_list_header_len").length == 4
-- ... and the split across the two must stay 2 (StorageChange, changes list) + 1
-- (SlotChanges), since the emit pass reads the inner two from `measure_slot`'s two
-- return values and writes the outer one itself.
#guard (balSerializerMeasureSlotFunction.splitOn "jal ra, bal_rlp_list_header_len").length == 3
#guard (balSerializerMeasureStorageFunction.splitOn "jal ra, bal_rlp_list_header_len").length == 2
-- Two scalars per change (BAI, new_value) plus one per slot.
#guard (balStorageMeasurePair.splitOn "jal ra, bal_rlp_scalar_rlp_len").length == 4
-- Each distinct slot measured EXACTLY ONCE, or a slot with three changes contributes its
-- SlotChanges three times.
#guard (balSerializerMeasureStorageFunction.splitOn "jal ra, bal_serializer_slot_seen_before").length == 2
-- Per account at BOTH loop levels: without the inner check, another account's change to
-- the same slot is folded into this account's list.
#guard (balStorageMeasurePair.splitOn "jal ra, bal_serializer_addr_matches_be").length == 3
-- The +8 slot, per the pinned table layout.
#guard (balSerializerMeasureStorageFunction.splitOn "sd s2, 8(t0)").length == 2
-- The seen-before scan must look only at EARLIER rows, or every row reports itself seen
-- and the field measures as empty.
#guard (balSerializerSlotSeenBeforeFunction.splitOn "bgeu s3, s2, .Lbssb_no").length == 2

/-! ## Guards for the serializer's scratch -/

-- SIX entries per account, one per header emit writes: the account list plus its five
-- field lists. Storing only the account total would force emit to recompute the five,
-- which is the duplication the table exists to prevent.
#guard balBuilderLenTableEntryBytes = 48
-- The table is PER ACCOUNT. A block-scope one is 3.52 MiB against 1.14 MiB of .bss
-- headroom before .sszscratch, which the linker rejects. It is also unindexed, so it
-- cannot overrun the way an account-indexed table could.
#guard (blockAccessListBuilderDataSection.splitOn "bal_serializer_outer_payload:").length == 2

-- The read scratch cannot be smaller than the set it filters, since the survivors are
-- a subset of STORAGE_READS_AREA's 16384.

-- Emitted at all.
#guard (blockAccessListBuilderDataSection.splitOn "bal_serializer_len_table:").length == 2
-- There must be NO surviving-reads scratch: it cost 0.5 MiB of a 1.14 MiB budget shared
-- with another lane, and re-running one predicate cannot diverge from itself.
#guard (blockAccessListBuilderDataSection.splitOn "bal_serializer_read_scratch:").length == 1
#guard (balSerializerFilterReadsFunction.splitOn "bal_serializer_read_scratch;").length == 1

-- 76923 * 24. Was 1538460 at a 20-byte row; the row is now 8-ALIGNED so
-- `bal_canonical_sort` can swap it with 8-byte loads. +307,692 bytes.
#guard balBuilderAccountBytes = 1846152
#guard balBuilderStorageChangeBytes = 1476864
#guard balBuilderBalanceBytes = 3200000
#guard balBuilderNonceBytes = 666640
#guard balBuilderCodeBytes = 400000
#guard balBuilderPersistentBytes = 7589656
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_ensure_account:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_append_balance:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_append_nonce:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_append_code:").length == 2

end EvmAsm.Codegen
