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

  * `storage_changes` -- the dedicated 80-byte builder stream;
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

/-- Separate resource bounds.  They are intentionally not added as if one
    block could maximize every list simultaneously; the joint gas argument is
    documented at the producer/serializer boundary. -/
def balBuilderAccountCapacity : Nat := 76923
def balBuilderStorageChangeCapacity : Nat := 15384
def balBuilderBalanceCapacity : Nat := 50000
def balBuilderNonceCapacity : Nat := 16666
def balBuilderCodeCapacity : Nat := 6250

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
Their caller supplies one final post-state for a `(canonical address, BAI)`;
that transaction-boundary discipline is what gives the spec's same-BAI
replacement semantics without recording intermediate execution snapshots.

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

def blockAccessListBuilderFunctions : String :=
  balBuilderEnsureAccountFunction ++
  balBuilderAppendBalanceFunction ++
  balBuilderAppendNonceFunction ++
  balBuilderAppendCodeFunction

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
