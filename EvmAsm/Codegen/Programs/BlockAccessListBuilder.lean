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

namespace EvmAsm.Codegen

/-- Canonical account-table entry: exactly the 20-byte big-endian `Address`. -/
def balBuilderAccountRowBytes : Nat := 20
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

/-! ## The surviving-reads scratch list

    `_build_from_builder` (`:544-547`) excludes a slot from `storage_reads` when the
    same account also has `storage_changes` for it. Filtered ONCE into this list, then
    measured and emitted from it — never re-filtered during emission, because the two
    passes would then apply the predicate twice and could disagree, and because the
    surviving COUNT is itself needed to size the list's header.

    **The difference is PER ACCOUNT, not global.** In the spec both fields hang off the
    same `changes` object inside `for address, changes in builder.accounts.items()`, so
    a slot excluded from account A's reads because A wrote it MUST still appear in
    account B's reads if B only read it.

    Sized to `STORAGE_READS_AREA`'s 16384, since the survivors are a subset of it. -/
def balSerializerReadScratchCapacity : Nat := 16384
def balSerializerReadScratchBytes : Nat := balSerializerReadScratchCapacity * 32

def balBuilderAccountBytes : Nat := balBuilderAccountCapacity * balBuilderAccountRowBytes
def balBuilderStorageChangeBytes : Nat := balBuilderStorageChangeCapacity * balBuilderStorageChangeRowBytes
def balBuilderBalanceBytes : Nat := balBuilderBalanceCapacity * balBuilderBalanceRowBytes
def balBuilderNonceBytes : Nat := balBuilderNonceCapacity * balBuilderNonceRowBytes
def balBuilderCodeBytes : Nat := balBuilderCodeCapacity * balBuilderCodeRowBytes
def balBuilderPersistentBytes : Nat :=
  balBuilderAccountBytes + balBuilderStorageChangeBytes + balBuilderBalanceBytes +
    balBuilderNonceBytes + balBuilderCodeBytes

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
  "bal_serializer_read_scratch:\n  .zero " ++ toString balSerializerReadScratchBytes ++ "\n" ++
  "bal_serializer_read_scratch_count:\n  .zero 8\n" ++
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
  -- `s5 = accounts + 20 * index` without a multiply extension dependency.
  "  slli s5, s3, 2; add s5, s5, s3; slli s5, s5, 2; add s5, s4, s5; li t0, 20; mv t1, s5; mv t2, s0\n" ++
  ".Lbabe_cmp:\n" ++
  "  beqz t0, .Lbabe_hit; lbu t3, 0(t1); lbu t4, 0(t2); bne t3, t4, .Lbabe_next; addi t1, t1, 1; addi t2, t2, 1; addi t0, t0, -1; j .Lbabe_cmp\n" ++
  ".Lbabe_next:\n" ++
  "  addi s3, s3, 1; j .Lbabe_scan\n" ++
  ".Lbabe_append:\n" ++
  "  li t0, " ++ toString balBuilderAccountCapacity ++ "; bgeu s2, t0, .Lbabe_overflow\n" ++
  "  slli s5, s2, 2; add s5, s5, s2; slli s5, s5, 2; add s5, s4, s5; li t0, 20; mv t1, s5; mv t2, s0\n" ++
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

/-! ## `bal_serializer_addr_matches` / `bal_serializer_slot_written`

    Two leaves the read filter needs. Split out so the filter reads as the spec's loop
    rather than as three nested scans.

    `bal_serializer_addr_matches`: does a read row belong to this account?
      a0 = address ptr (20 B BE)   a1 = read row ptr (addrHash at +0, 32 B stack word)
      a0 (out) = 1 on match, 0 otherwise

    The read row's key is a 32-byte EVM stack word and the account address is canonical
    BE20 — the same encoding split the sort descriptors already record, storage rows
    holding a stack word while account rows hold BE20. So the comparison reverses the
    row's low 20 bytes rather than comparing the two forms directly.

    `bal_serializer_slot_written`: does this account also have a storage CHANGE for this
    slot?
      a0 = slot ptr (32 B, as stored in the read row)   a1 = address ptr (20 B BE)
      a0 (out) = 1 if a change row matches (address, slot), 0 otherwise

    A hit means the spec drops the read (`:545-546`). Matching on BOTH address and slot
    is what makes the exclusion per-account: the same slot written by a different
    account must not suppress this account's read. -/
def balSerializerAddrMatchesFunction : String :=
  "bal_serializer_addr_matches:\n" ++
  "  li t0, 20; li t1, 0\n" ++
  -- BE20 byte i of the address vs byte (19 - i) of the reversed stack word, i.e.
  -- row byte i counted from the word's low end.
  ".Lbsam_cmp:\n" ++
  "  beq t1, t0, .Lbsam_yes\n" ++
  "  add t2, a0, t1\n" ++
  "  li t3, 19; sub t3, t3, t1; add t3, a1, t3\n" ++
  "  lbu t4, 0(t2); lbu t5, 0(t3); bne t4, t5, .Lbsam_no\n" ++
  "  addi t1, t1, 1; j .Lbsam_cmp\n" ++
  ".Lbsam_yes:\n" ++
  "  li a0, 1; ret\n" ++
  ".Lbsam_no:\n" ++
  "  li a0, 0; ret\n"

def balSerializerSlotWrittenFunction : String :=
  "bal_serializer_slot_written:\n" ++
  "  addi sp, sp, -32; sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp)\n" ++
  "  la t0, bal_builder_storage_change_count; ld t1, 0(t0)\n" ++
  "  li t3, 0\n" ++
  ".Lbssw_scan:\n" ++
  "  bgeu t3, t1, .Lbssw_no\n" ++
  "  li t0, 96; mul t2, t3, t0; la t4, bal_builder_storage_changes; add t4, t4, t2\n" ++
  -- slot at +32 of the change row, 4 dwords, against the read row's slot
  "  ld a2, 8(sp)\n" ++
  "  ld t5, 32(t4); ld t6, 0(a2);  bne t5, t6, .Lbssw_next\n" ++
  "  ld t5, 40(t4); ld t6, 8(a2);  bne t5, t6, .Lbssw_next\n" ++
  "  ld t5, 48(t4); ld t6, 16(a2); bne t5, t6, .Lbssw_next\n" ++
  "  ld t5, 56(t4); ld t6, 24(a2); bne t5, t6, .Lbssw_next\n" ++
  -- address at +0, BE20 in both, so a straight byte compare
  "  ld a2, 16(sp); li t5, 20; li t6, 0\n" ++
  ".Lbssw_acmp:\n" ++
  "  beq t6, t5, .Lbssw_yes\n" ++
  "  add t0, a2, t6; add t2, t4, t6\n" ++
  "  lbu t0, 0(t0); lbu t2, 0(t2); bne t0, t2, .Lbssw_next\n" ++
  "  addi t6, t6, 1; j .Lbssw_acmp\n" ++
  ".Lbssw_next:\n" ++
  "  addi t3, t3, 1; j .Lbssw_scan\n" ++
  ".Lbssw_yes:\n" ++
  "  li a0, 1; j .Lbssw_ret\n" ++
  ".Lbssw_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbssw_ret:\n" ++
  "  ld ra, 0(sp); addi sp, sp, 32; ret\n"

/-! ## `bal_serializer_filter_reads`

    Phase one of the serializer: build one account's SURVIVING storage_reads.

    Mirrors `_build_from_builder` (`:544-547`):

        storage_reads = []
        for slot in changes.storage_reads:
            if slot not in changes.storage_changes:
                storage_reads.append(slot)

    ## Filtered once, here — not during emission

    The surviving COUNT sizes the read list's RLP header, so the filter has to run
    before any emission regardless. Running it again inside emit would mean two
    implementations of one predicate, and a disagreement there yields a well-formed
    buffer whose read-list header is wrong by the number of slots the two passes
    disagreed about.

    ## PER ACCOUNT, NOT GLOBAL

    In the spec both fields hang off the same `changes` object inside
    `for address, changes in builder.accounts.items()`. So a slot excluded from account
    A's reads because A wrote it **must still appear in account B's reads if B only read
    it**. This routine is therefore called once per account with that account's address,
    and it consults only rows matching that address.

    ## Why a fixture cannot stumble into the discriminating case

    The rule only bites when a slot is BOTH read and written by one account. A block
    that only reads, or only writes, produces the same output with or without the
    filter — and, worse, so does a block that reads and writes DIFFERENT slots. The
    case that discriminates is a slot read in one transaction and written in a LATER
    one, which no single-transaction fixture can produce.

    Calling convention:
      a0 = address ptr (20 B big-endian)
      ra = return
      a0 (out) = surviving read count, also left in
                 `bal_serializer_read_scratch_count`

    Reads `STORAGE_READS_AREA` rows (`addrHash[32], slotKey[32]`, 64 B stride) against
    `bal_builder_storage_changes` (`address[20], pad[4], BAI[8], slot[32], value[32]`,
    96 B stride), and writes surviving 32-byte slot keys into
    `bal_serializer_read_scratch`.

    DELIBERATELY INERT PENDING ITS CALLER: the measure and emit phases land separately. -/
def balSerializerFilterReadsFunction : String :=
  "bal_serializer_filter_reads:\n" ++
  "  addi sp, sp, -32; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++                                             -- s0 = address ptr
  "  la t0, bal_serializer_read_scratch_count; sd zero, 0(t0)\n" ++
  "  li s1, 0\n" ++                                              -- s1 = survivor count
  "  la t0, storage_reads_count; ld s2, 0(t0)\n" ++               -- s2 = read row count
  "  li t3, 0\n" ++                                              -- t3 = read index
  ".Lbsfr_read:\n" ++
  "  bgeu t3, s2, .Lbsfr_done\n" ++
  "  li t0, 0xa1ba0000; slli t1, t3, 6; add t4, t0, t1\n" ++      -- t4 = &readrow[i]
  -- The read row's addrHash is a 32-byte stack-word key; the account address is BE20.
  -- Compare the low 20 bytes of the reversed key against it, which is the same
  -- canonicalisation the builder rows use.
  "  mv a0, s0; mv a1, t4; jal ra, bal_serializer_addr_matches\n" ++
  "  beqz a0, .Lbsfr_next\n" ++
  -- This read belongs to the account. Is its slot also in storage_changes FOR THIS
  -- ACCOUNT? Scan the change stream; a hit means the spec drops the read.
  "  addi a0, t4, 32; mv a1, s0; jal ra, bal_serializer_slot_written\n" ++
  "  bnez a0, .Lbsfr_next\n" ++                                  -- written => EXCLUDE
  -- Survivor: copy the 32-byte slot key into the scratch list.
  "  li t0, 32; mul t1, s1, t0; la t2, bal_serializer_read_scratch; add t5, t2, t1\n" ++
  "  addi t6, t4, 32\n" ++
  "  ld t0, 0(t6);  sd t0, 0(t5)\n" ++
  "  ld t0, 8(t6);  sd t0, 8(t5)\n" ++
  "  ld t0, 16(t6); sd t0, 16(t5)\n" ++
  "  ld t0, 24(t6); sd t0, 24(t5)\n" ++
  "  addi s1, s1, 1\n" ++
  ".Lbsfr_next:\n" ++
  "  addi t3, t3, 1; j .Lbsfr_read\n" ++
  ".Lbsfr_done:\n" ++
  "  la t0, bal_serializer_read_scratch_count; sd s1, 0(t0)\n" ++
  "  mv a0, s1\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n"

def blockAccessListBuilderFunctions : String :=
  balSerializerAddrMatchesFunction ++
  balSerializerSlotWrittenFunction ++
  balSerializerFilterReadsFunction ++
  balBuilderEnsureAccountFunction ++
  balBuilderRecordStorageChangeFunction ++
  balEmitStorageChangesFunction ++
  balBuilderAppendBalanceFunction ++
  balBuilderAppendNonceFunction ++
  balBuilderAppendCodeFunction

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
#guard balSerializerReadScratchCapacity = 16384
#guard balSerializerReadScratchBytes = 16384 * 32

-- Emitted at all.
#guard (blockAccessListBuilderDataSection.splitOn "bal_serializer_len_table:").length == 2
#guard (blockAccessListBuilderDataSection.splitOn "bal_serializer_read_scratch:").length == 2

#guard balBuilderAccountBytes = 1538460
#guard balBuilderStorageChangeBytes = 1476864
#guard balBuilderBalanceBytes = 3200000
#guard balBuilderNonceBytes = 666640
#guard balBuilderCodeBytes = 400000
#guard balBuilderPersistentBytes = 7281964
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_ensure_account:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_append_balance:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_append_nonce:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_append_code:").length == 2

end EvmAsm.Codegen
