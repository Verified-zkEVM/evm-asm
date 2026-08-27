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

module

public import EvmAsm.Codegen.Programs.BlockVerdictParams
public import EvmAsm.Codegen.Programs.BalSerializer
public import EvmAsm.Codegen.Programs.BalSerializerTail
public import EvmAsm.Codegen.Programs.BalCapacities
public import EvmAsm.Codegen.Emit
public import EvmAsm.Codegen.AsmReloc
public import EvmAsm.Codegen.GuestAddrs
public import EvmAsm.Codegen.Programs.BlockAccessListBuilderStorage
meta import EvmAsm.Codegen.Programs.BlockVerdictParams
meta import EvmAsm.Codegen.Programs.BalSerializer
meta import EvmAsm.Codegen.Programs.BalSerializerTail
meta import EvmAsm.Codegen.Programs.BalCapacities
meta import EvmAsm.Codegen.Emit
meta import EvmAsm.Codegen.AsmReloc
meta import EvmAsm.Codegen.GuestAddrs
meta import EvmAsm.Codegen.Programs.BlockAccessListBuilderStorage

@[expose] public section

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Account-table row: a 20-byte big-endian `Address` in 24 bytes.

    THE 4 PADDING BYTES ARE LOAD-BEARING, and the rule behind them is project-wide rather
    than local to this table.

    ANY ROW ARRAY THAT WILL BE SORTED MUST HAVE AN 8-ALIGNED STRIDE. `bal_canonical_sort`
    swaps rows with `ld`/`sd` (`scripts/asm-fixtures/balCanonicalSortFunction.s:65-67`,
    the `.Lbalsort_swap` loop — this cited `BalCanonicalSort.lean:254` until #10817,
    which had drifted to a range-frame load; the fixture is the stable citation),
    and per AGENTS.md:211 the
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

    24 rather than 32: the arena is capacity 140000, so the 4 padding bytes per
    row cost 560,000 bytes and fit below `.sszscratch`, while a separate
    32-byte staging copy needed 4,480,000 and did not. -/
def balBuilderAccountRowBytes : Nat := 24
/-- `{address[20], pad[4], u64 BAI, slot[32], post value[32]}`. -/
def balBuilderStorageChangeRowBytes : Nat := 96
/-- `{address[20], pad[4], u64 BAI, post balance[32]}`. -/
def balBuilderBalanceRowBytes : Nat := 64
/-- `{address[20], pad[4], u64 BAI, post nonce}`. -/
def balBuilderNonceRowBytes : Nat := 40
/-- `{address[20], pad[4], u64 BAI, code-effect reference/meta[32]}`. -/
def balBuilderCodeRowBytes : Nat := 64

/-! Separate resource bounds. They are intentionally not added as if one block
    could maximize every list simultaneously. The enumeration behind the
    persistent 16,882,112-byte reservation (row strides: account 24,
    storage-change 96, balance 64, nonce 40, code 64) is, per field:

    * account: 240M/3000 user + 6×⌊30M/3000⌋ system = 140000 (cold account
      cost 3000, `execution-specs` `amsterdam/vm/gas.py:69-71`);
    * storage-change: user leg ⌊1.5L/10100⌋ = 29702 — NOT a gas cost: a
      persistent entry costs WARM_ACCESS 100 + STORAGE_WRITE 10000 = 10100
      gross, and the refund cap (F ≤ (R+S)/5, S ≤ L, regular use R−F ≤ L)
      gives 0.8R − 0.2S ≤ L, i.e. R ≤ 1.5L — plus the system leg
      6×⌊30M/10100⌋ = 17820, total 47522;
    * balance: 240M/4000 + 6×⌊30M/4000⌋ = 105000;
    * nonce: 240M/12000 + 6×⌊30M/12000⌋ = 35000 (the old 16666 was exactly
      200M/TX_BASE with no system headroom);
    * code: six INDEPENDENT floors 6×⌊30M/32000⌋ = 5622 (pooling first would
      give ⌊180M/32000⌋ = 5625 — wrong leg structure), i.e. 13122, rounded UP
      to 13125 for slack and a rounder checkable number.

    Here 240M = 200M × 1.2 is the refund-effective allowance over the block
    gas limit, and the 6×30M system leg is the new producer route that forced
    this resize: SIX SYSTEM CALLS (2 unchecked + 4 checked request calls in
    `apply_body`, each at the 30M system-call gas allowance, each incorporated
    into the BAL) bypass the block gas counters and the user refund logic
    entirely, so no derivation from the block gas limit can see them.

    The enumeration reflects the Amsterdam spec areas read to date and must be
    revisited when a new producer route is understood. The reservation is
    therefore a joint upper bound with material slack, not a sum of
    independent maxima. -/
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
    6.41 MiB. **`.bss` has about 7.2 MiB of headroom**: after the GH #10836 arena
    resize its base moved down to `0xa2e07000` (into the `.data` slack), it ends at
    about `0xbf249580` — about 7.2 MiB of headroom to `.sszscratch` at `0xbf980000`;
    the linker rejects
    an overlap outright (`section .sszscratch VMA ... overlaps section .bss VMA ...`).

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

    The two verbatim scalar fields are caller contracts, not transformations performed by
    this writer: `NonstorageEffectLog.lean` declares the balance producer's post buffer as
    32-byte BE and `bal_builder_append_balance` copies it verbatim; the storage producer's
    transaction row is an LE stack word (`StorageWriteMap.lean`, value stores at +64), and
    `bal_emit_storage_changes` passes that row field verbatim to the builder. The serializer
    reverses the balance row only into its private LE scalar scratch.

    | stream          | field | off | width | byte order                    |
    | storage_changes | addr  |   0 |    20 | BE20   (reversed on append)   |
    | storage_changes | bai   |  24 |     8 | native LE u64                 |
    | storage_changes | slot  |  32 |    32 | BE32   (reversed on append)   |
    | storage_changes | value |  64 |    32 | LE (StorageWriteMap tx row; verbatim) |
    | balance_changes | addr  |   0 |    20 | BE20   (already canonical)    |
    | balance_changes | bai   |  24 |     8 | native LE u64                 |
    | balance_changes | post  |  32 |    32 | BE32 (NonstorageEffectLog; verbatim row) |
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
    significant byte. They are correct on every LE field above and WRONG on TWO BE fields -- the storage
    slot and (GH #10820) the balance post, both of which must be reversed into scratch
    before being handed to them. Judge a field by its PRODUCER, not by its row position:
    the balance sits beside the LE storage value and is produced by the `u256_*_be`
    helpers, and that grouping is how it was mislabelled LE here for so long. Sources:
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
  -- #10820: LE image of the row's BE32 post balance, mirroring the slot buffer above.
  "bal_serializer_balance_le:\n  .zero 32\n" ++
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
def balBuilderEnsureAccount_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x8 (0 : BitVec 12),
    .SD .x2 .x9 (8 : BitVec 12),
    .SD .x2 .x18 (16 : BitVec 12),
    .SD .x2 .x19 (24 : BitVec 12),
    .SD .x2 .x20 (32 : BitVec 12),
    .SD .x2 .x21 (40 : BitVec 12),
    .MV .x8 .x10,
    .AUIPC .x9 (laHi GuestAddrs.bal_builder_account_count (GuestAddrs.bal_builder_ensure_account + 32)),
    .ADDI .x9 .x9 (laLo GuestAddrs.bal_builder_account_count (GuestAddrs.bal_builder_ensure_account + 32)),
    .LD .x18 .x9 (0 : BitVec 12),
    .LI .x19 (0 : Word),
    .AUIPC .x20 (laHi GuestAddrs.bal_builder_accounts (GuestAddrs.bal_builder_ensure_account + 48)),
    .ADDI .x20 .x20 (laLo GuestAddrs.bal_builder_accounts (GuestAddrs.bal_builder_ensure_account + 48)),
    .BGEU .x19 .x18 (brOff (GuestAddrs.bal_builder_ensure_account + 128) (GuestAddrs.bal_builder_ensure_account + 56)),
    .SLLI .x21 .x19 (1 : BitVec 6),
    .ADD .x21 .x21 .x19,
    .SLLI .x21 .x21 (3 : BitVec 6),
    .ADD .x21 .x20 .x21,
    .LI .x5 (20 : Word),
    .MV .x6 .x21,
    .MV .x7 .x8,
    .BEQ .x5 .x0 (brOff (GuestAddrs.bal_builder_ensure_account + 208) (GuestAddrs.bal_builder_ensure_account + 88)),
    .LBU .x28 .x6 (0 : BitVec 12),
    .LBU .x29 .x7 (0 : BitVec 12),
    .BNE .x28 .x29 (20 : BitVec 13),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_builder_ensure_account + 56) (GuestAddrs.bal_builder_ensure_account + 124)),
    .LUI .x5 (34 : BitVec 20),
    .ADDIW .x5 .x5 (736 : BitVec 12),
    .BGEU .x18 .x5 (brOff (GuestAddrs.bal_builder_ensure_account + 216) (GuestAddrs.bal_builder_ensure_account + 136)),
    .SLLI .x21 .x18 (1 : BitVec 6),
    .ADD .x21 .x21 .x18,
    .SLLI .x21 .x21 (3 : BitVec 6),
    .ADD .x21 .x20 .x21,
    .LI .x5 (20 : Word),
    .MV .x6 .x21,
    .MV .x7 .x8,
    .BEQ .x5 .x0 (28 : BitVec 13),
    .LBU .x28 .x7 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x5 .x18 (1 : BitVec 12),
    .SD .x9 .x5 (0 : BitVec 12),
    .MV .x19 .x18,
    .MV .x10 .x19,
    .JAL .x0 (24 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_overflow (GuestAddrs.bal_builder_ensure_account + 216)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_overflow (GuestAddrs.bal_builder_ensure_account + 216)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (-1 : Word),
    .LD .x8 .x2 (0 : BitVec 12),
    .LD .x9 .x2 (8 : BitVec 12),
    .LD .x18 .x2 (16 : BitVec 12),
    .LD .x19 .x2 (24 : BitVec 12),
    .LD .x20 .x2 (32 : BitVec 12),
    .LD .x21 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balBuilderEnsureAccount_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balBuilderEnsureAccount_relocs : RelocTable :=
  [ (8, .la .x9 "bal_builder_account_count"),
    (12, .la .x20 "bal_builder_accounts"),
    (54, .la .x5 "bal_builder_overflow") ]

def balBuilderEnsureAccountFunction : String :=
  "bal_builder_ensure_account:\n" ++ emitProgramR balBuilderEnsureAccount_prog balBuilderEnsureAccount_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balBuilderEnsureAccount_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balBuilderEnsureAccountFunction_eq_prog :
    balBuilderEnsureAccountFunction = "bal_builder_ensure_account:\n" ++ emitProgramR balBuilderEnsureAccount_prog balBuilderEnsureAccount_relocs := rfl

#guard balBuilderEnsureAccountFunction.startsWith "bal_builder_ensure_account:\n"
#guard balBuilderEnsureAccount_prog.length = 67
/-! ## `bal_builder_incorporate_touched_accounts`

The spec's final build step feeds every address in the block-lifetime
`account_reads` set through `add_touched_account` before sorting the builder
(`block_access_lists.py:_build_from_builder`).  The guest already promotes that
set at each committed transaction; this late walk is its only consumer in the
BAL builder.  `bal_builder_ensure_account` is exactly the corresponding
primitive: a miss creates an account entry with all five change lists empty,
and a hit preserves an entry created earlier by a change producer.

`account_reads` rows are 32-byte slots with a BE20 address at their start.
Only those 20 bytes are passed to the builder, whose account table has a
24-byte stride for aligned sorting.  The source-set capacity is 16,384 and the
common builder overflow latch is checked by the block-verdict tail, so this
loop must not silently truncate a failed insertion. -/
def balBuilderIncorporateTouchedAccounts_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .AUIPC .x8 (laHi GuestAddrs.account_reads_count (GuestAddrs.bal_builder_incorporate_touched_accounts + 20)),
    .ADDI .x8 .x8 (laLo GuestAddrs.account_reads_count (GuestAddrs.bal_builder_incorporate_touched_accounts + 20)),
    .LD .x9 .x8 (0 : BitVec 12),
    .LI .x18 (0 : Word),
    .BGEU .x18 .x9 (40 : BitVec 13),
    .SLLI .x5 .x18 (5 : BitVec 6),
    .LUI .x6 (81 : BitVec 20),
    .ADDIW .x6 .x6 (-371 : BitVec 12),
    .SLLI .x6 .x6 (13 : BitVec 6),
    .ADDI .x6 .x6 (512 : BitVec 12),
    .ADD .x10 .x6 .x5,
    .JAL .x1 (jalOff GuestAddrs.bal_builder_ensure_account (GuestAddrs.bal_builder_incorporate_touched_accounts + 64)),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balBuilderIncorporateTouchedAccounts_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balBuilderIncorporateTouchedAccounts_relocs : RelocTable :=
  [ (5, .la .x8 "account_reads_count"),
    (16, .jal .x1 "bal_builder_ensure_account") ]

def balBuilderIncorporateTouchedAccountsFunction : String :=
  "bal_builder_incorporate_touched_accounts:\n" ++ emitProgramR balBuilderIncorporateTouchedAccounts_prog balBuilderIncorporateTouchedAccounts_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balBuilderIncorporateTouchedAccounts_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balBuilderIncorporateTouchedAccountsFunction_eq_prog :
    balBuilderIncorporateTouchedAccountsFunction = "bal_builder_incorporate_touched_accounts:\n" ++ emitProgramR balBuilderIncorporateTouchedAccounts_prog balBuilderIncorporateTouchedAccounts_relocs := rfl

#guard balBuilderIncorporateTouchedAccountsFunction.startsWith "bal_builder_incorporate_touched_accounts:\n"
#guard balBuilderIncorporateTouchedAccounts_prog.length = 25
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
def balBuilderAppendBalance_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x10 (8 : BitVec 12),
    .SD .x2 .x11 (16 : BitVec 12),
    .SD .x2 .x12 (24 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_builder_ensure_account (GuestAddrs.bal_builder_append_balance + 20)),
    .BLT .x10 .x0 (brOff (GuestAddrs.bal_builder_append_balance + 188) (GuestAddrs.bal_builder_append_balance + 24)),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_balance_count (GuestAddrs.bal_builder_append_balance + 28)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_balance_count (GuestAddrs.bal_builder_append_balance + 28)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (26 : BitVec 20),
    .ADDIW .x7 .x7 (-1496 : BitVec 12),
    .BGEU .x6 .x7 (brOff (GuestAddrs.bal_builder_append_balance + 188) (GuestAddrs.bal_builder_append_balance + 48)),
    .SLLI .x7 .x6 (6 : BitVec 6),
    .AUIPC .x28 (laHi GuestAddrs.bal_builder_balance_changes (GuestAddrs.bal_builder_append_balance + 56)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bal_builder_balance_changes (GuestAddrs.bal_builder_append_balance + 56)),
    .ADD .x28 .x28 .x7,
    .LD .x29 .x2 (8 : BitVec 12),
    .LI .x30 (20 : Word),
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x29 (0 : BitVec 12),
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x28 (laHi GuestAddrs.bal_builder_balance_changes (GuestAddrs.bal_builder_append_balance + 104)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bal_builder_balance_changes (GuestAddrs.bal_builder_append_balance + 104)),
    .SLLI .x7 .x6 (6 : BitVec 6),
    .ADD .x28 .x28 .x7,
    .LD .x29 .x2 (16 : BitVec 12),
    .SD .x28 .x29 (24 : BitVec 12),
    .LD .x29 .x2 (24 : BitVec 12),
    .LD .x30 .x29 (0 : BitVec 12),
    .SD .x28 .x30 (32 : BitVec 12),
    .LD .x30 .x29 (8 : BitVec 12),
    .SD .x28 .x30 (40 : BitVec 12),
    .LD .x30 .x29 (16 : BitVec 12),
    .SD .x28 .x30 (48 : BitVec 12),
    .LD .x30 .x29 (24 : BitVec 12),
    .SD .x28 .x30 (56 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_balance_count (GuestAddrs.bal_builder_append_balance + 168)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_balance_count (GuestAddrs.bal_builder_append_balance + 168)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (36 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_balance_overflow (GuestAddrs.bal_builder_append_balance + 188)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_balance_overflow (GuestAddrs.bal_builder_append_balance + 188)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_overflow (GuestAddrs.bal_builder_append_balance + 204)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_overflow (GuestAddrs.bal_builder_append_balance + 204)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balBuilderAppendBalance_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balBuilderAppendBalance_relocs : RelocTable :=
  [ (5, .jal .x1 "bal_builder_ensure_account"),
    (7, .la .x5 "bal_builder_balance_count"),
    (14, .la .x28 "bal_builder_balance_changes"),
    (26, .la .x28 "bal_builder_balance_changes"),
    (42, .la .x5 "bal_builder_balance_count"),
    (47, .la .x5 "bal_builder_balance_overflow"),
    (51, .la .x5 "bal_builder_overflow") ]

def balBuilderAppendBalanceFunction : String :=
  "bal_builder_append_balance:\n" ++ emitProgramR balBuilderAppendBalance_prog balBuilderAppendBalance_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balBuilderAppendBalance_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balBuilderAppendBalanceFunction_eq_prog :
    balBuilderAppendBalanceFunction = "bal_builder_append_balance:\n" ++ emitProgramR balBuilderAppendBalance_prog balBuilderAppendBalance_relocs := rfl

#guard balBuilderAppendBalanceFunction.startsWith "bal_builder_append_balance:\n"
#guard balBuilderAppendBalance_prog.length = 58
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
def balBuilderRecordStorageChange_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x10 (8 : BitVec 12),
    .SD .x2 .x11 (16 : BitVec 12),
    .SD .x2 .x12 (24 : BitVec 12),
    .SD .x2 .x13 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_builder_ensure_account (GuestAddrs.bal_builder_record_storage_change + 24)),
    .BLT .x10 .x0 (brOff (GuestAddrs.bal_builder_record_storage_change + 416) (GuestAddrs.bal_builder_record_storage_change + 28)),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_builder_record_storage_change + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_builder_record_storage_change + 32)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x29 (0 : Word),
    .BGEU .x29 .x6 (brOff (GuestAddrs.bal_builder_record_storage_change + 228) (GuestAddrs.bal_builder_record_storage_change + 48)),
    .LI .x7 (96 : Word),
    .MUL .x7 .x29 .x7,
    .AUIPC .x28 (laHi GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_builder_record_storage_change + 60)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_builder_record_storage_change + 60)),
    .ADD .x30 .x28 .x7,
    .LD .x7 .x30 (24 : BitVec 12),
    .LD .x31 .x2 (16 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.bal_builder_record_storage_change + 180) (GuestAddrs.bal_builder_record_storage_change + 80)),
    .LD .x14 .x2 (24 : BitVec 12),
    .LD .x7 .x30 (32 : BitVec 12),
    .LD .x31 .x14 (0 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.bal_builder_record_storage_change + 180) (GuestAddrs.bal_builder_record_storage_change + 96)),
    .LD .x7 .x30 (40 : BitVec 12),
    .LD .x31 .x14 (8 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.bal_builder_record_storage_change + 180) (GuestAddrs.bal_builder_record_storage_change + 108)),
    .LD .x7 .x30 (48 : BitVec 12),
    .LD .x31 .x14 (16 : BitVec 12),
    .BNE .x7 .x31 (60 : BitVec 13),
    .LD .x7 .x30 (56 : BitVec 12),
    .LD .x31 .x14 (24 : BitVec 12),
    .BNE .x7 .x31 (48 : BitVec 13),
    .LD .x14 .x2 (8 : BitVec 12),
    .LI .x7 (20 : Word),
    .MV .x31 .x30,
    .BEQ .x7 .x0 (40 : BitVec 13),
    .LBU .x15 .x14 (0 : BitVec 12),
    .LBU .x16 .x31 (0 : BitVec 12),
    .BNE .x15 .x16 (20 : BitVec 13),
    .ADDI .x14 .x14 (1 : BitVec 12),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_builder_record_storage_change + 48) (GuestAddrs.bal_builder_record_storage_change + 184)),
    .LD .x14 .x2 (32 : BitVec 12),
    .LD .x7 .x14 (0 : BitVec 12),
    .SD .x30 .x7 (64 : BitVec 12),
    .LD .x7 .x14 (8 : BitVec 12),
    .SD .x30 .x7 (72 : BitVec 12),
    .LD .x7 .x14 (16 : BitVec 12),
    .SD .x30 .x7 (80 : BitVec 12),
    .LD .x7 .x14 (24 : BitVec 12),
    .SD .x30 .x7 (88 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_builder_record_storage_change + 444) (GuestAddrs.bal_builder_record_storage_change + 224)),
    .LUI .x7 (12 : BitVec 20),
    .ADDIW .x7 .x7 (-1630 : BitVec 12),
    .BGEU .x6 .x7 (brOff (GuestAddrs.bal_builder_record_storage_change + 416) (GuestAddrs.bal_builder_record_storage_change + 236)),
    .LI .x7 (96 : Word),
    .MUL .x7 .x6 .x7,
    .AUIPC .x28 (laHi GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_builder_record_storage_change + 248)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_builder_record_storage_change + 248)),
    .ADD .x30 .x28 .x7,
    .LD .x14 .x2 (8 : BitVec 12),
    .LI .x7 (20 : Word),
    .MV .x31 .x30,
    .BEQ .x7 .x0 (28 : BitVec 13),
    .LBU .x15 .x14 (0 : BitVec 12),
    .SB .x31 .x15 (0 : BitVec 12),
    .ADDI .x14 .x14 (1 : BitVec 12),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .SB .x30 .x0 (20 : BitVec 12),
    .SB .x30 .x0 (21 : BitVec 12),
    .SB .x30 .x0 (22 : BitVec 12),
    .SB .x30 .x0 (23 : BitVec 12),
    .LD .x7 .x2 (16 : BitVec 12),
    .SD .x30 .x7 (24 : BitVec 12),
    .LD .x14 .x2 (24 : BitVec 12),
    .LD .x7 .x14 (0 : BitVec 12),
    .SD .x30 .x7 (32 : BitVec 12),
    .LD .x7 .x14 (8 : BitVec 12),
    .SD .x30 .x7 (40 : BitVec 12),
    .LD .x7 .x14 (16 : BitVec 12),
    .SD .x30 .x7 (48 : BitVec 12),
    .LD .x7 .x14 (24 : BitVec 12),
    .SD .x30 .x7 (56 : BitVec 12),
    .LD .x14 .x2 (32 : BitVec 12),
    .LD .x7 .x14 (0 : BitVec 12),
    .SD .x30 .x7 (64 : BitVec 12),
    .LD .x7 .x14 (8 : BitVec 12),
    .SD .x30 .x7 (72 : BitVec 12),
    .LD .x7 .x14 (16 : BitVec 12),
    .SD .x30 .x7 (80 : BitVec 12),
    .LD .x7 .x14 (24 : BitVec 12),
    .SD .x30 .x7 (88 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_builder_record_storage_change + 400)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_builder_record_storage_change + 400)),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x0 (32 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_storage_change_overflow (GuestAddrs.bal_builder_record_storage_change + 416)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_storage_change_overflow (GuestAddrs.bal_builder_record_storage_change + 416)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_overflow (GuestAddrs.bal_builder_record_storage_change + 432)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_overflow (GuestAddrs.bal_builder_record_storage_change + 432)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balBuilderRecordStorageChange_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balBuilderRecordStorageChange_relocs : RelocTable :=
  [ (6, .jal .x1 "bal_builder_ensure_account"),
    (8, .la .x5 "bal_builder_storage_change_count"),
    (15, .la .x28 "bal_builder_storage_changes"),
    (62, .la .x28 "bal_builder_storage_changes"),
    (100, .la .x5 "bal_builder_storage_change_count"),
    (104, .la .x5 "bal_builder_storage_change_overflow"),
    (108, .la .x5 "bal_builder_overflow") ]

def balBuilderRecordStorageChangeFunction : String :=
  "bal_builder_record_storage_change:\n" ++ emitProgramR balBuilderRecordStorageChange_prog balBuilderRecordStorageChange_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balBuilderRecordStorageChange_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balBuilderRecordStorageChangeFunction_eq_prog :
    balBuilderRecordStorageChangeFunction = "bal_builder_record_storage_change:\n" ++ emitProgramR balBuilderRecordStorageChange_prog balBuilderRecordStorageChange_relocs := rfl

#guard balBuilderRecordStorageChangeFunction.startsWith "bal_builder_record_storage_change:\n"
#guard balBuilderRecordStorageChange_prog.length = 114
def balBuilderAppendNonce_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x10 (8 : BitVec 12),
    .SD .x2 .x11 (16 : BitVec 12),
    .SD .x2 .x12 (24 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_builder_ensure_account (GuestAddrs.bal_builder_append_nonce + 20)),
    .BLT .x10 .x0 (brOff (GuestAddrs.bal_builder_append_nonce + 176) (GuestAddrs.bal_builder_append_nonce + 24)),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_nonce_count (GuestAddrs.bal_builder_append_nonce + 28)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_nonce_count (GuestAddrs.bal_builder_append_nonce + 28)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (9 : BitVec 20),
    .ADDIW .x7 .x7 (-1864 : BitVec 12),
    .BGEU .x6 .x7 (brOff (GuestAddrs.bal_builder_append_nonce + 176) (GuestAddrs.bal_builder_append_nonce + 48)),
    .SLLI .x7 .x6 (2 : BitVec 6),
    .ADD .x7 .x7 .x6,
    .SLLI .x7 .x7 (3 : BitVec 6),
    .AUIPC .x28 (laHi GuestAddrs.bal_builder_nonce_changes (GuestAddrs.bal_builder_append_nonce + 64)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bal_builder_nonce_changes (GuestAddrs.bal_builder_append_nonce + 64)),
    .ADD .x28 .x28 .x7,
    .LD .x29 .x2 (8 : BitVec 12),
    .LI .x30 (20 : Word),
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x29 (0 : BitVec 12),
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x28 (laHi GuestAddrs.bal_builder_nonce_changes (GuestAddrs.bal_builder_append_nonce + 112)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bal_builder_nonce_changes (GuestAddrs.bal_builder_append_nonce + 112)),
    .SLLI .x7 .x6 (2 : BitVec 6),
    .ADD .x7 .x7 .x6,
    .SLLI .x7 .x7 (3 : BitVec 6),
    .ADD .x28 .x28 .x7,
    .LD .x29 .x2 (16 : BitVec 12),
    .SD .x28 .x29 (24 : BitVec 12),
    .LD .x29 .x2 (24 : BitVec 12),
    .SD .x28 .x29 (32 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_nonce_count (GuestAddrs.bal_builder_append_nonce + 156)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_nonce_count (GuestAddrs.bal_builder_append_nonce + 156)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (36 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_nonce_overflow (GuestAddrs.bal_builder_append_nonce + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_nonce_overflow (GuestAddrs.bal_builder_append_nonce + 176)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_overflow (GuestAddrs.bal_builder_append_nonce + 192)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_overflow (GuestAddrs.bal_builder_append_nonce + 192)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balBuilderAppendNonce_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balBuilderAppendNonce_relocs : RelocTable :=
  [ (5, .jal .x1 "bal_builder_ensure_account"),
    (7, .la .x5 "bal_builder_nonce_count"),
    (16, .la .x28 "bal_builder_nonce_changes"),
    (28, .la .x28 "bal_builder_nonce_changes"),
    (39, .la .x5 "bal_builder_nonce_count"),
    (44, .la .x5 "bal_builder_nonce_overflow"),
    (48, .la .x5 "bal_builder_overflow") ]

def balBuilderAppendNonceFunction : String :=
  "bal_builder_append_nonce:\n" ++ emitProgramR balBuilderAppendNonce_prog balBuilderAppendNonce_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balBuilderAppendNonce_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balBuilderAppendNonceFunction_eq_prog :
    balBuilderAppendNonceFunction = "bal_builder_append_nonce:\n" ++ emitProgramR balBuilderAppendNonce_prog balBuilderAppendNonce_relocs := rfl

#guard balBuilderAppendNonceFunction.startsWith "bal_builder_append_nonce:\n"
#guard balBuilderAppendNonce_prog.length = 55
def balBuilderAppendCode_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x10 (8 : BitVec 12),
    .SD .x2 .x11 (16 : BitVec 12),
    .SD .x2 .x12 (24 : BitVec 12),
    .SD .x2 .x13 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_builder_ensure_account (GuestAddrs.bal_builder_append_code + 24)),
    .BLT .x10 .x0 (brOff (GuestAddrs.bal_builder_append_code + 172) (GuestAddrs.bal_builder_append_code + 28)),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_code_count (GuestAddrs.bal_builder_append_code + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_code_count (GuestAddrs.bal_builder_append_code + 32)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (3 : BitVec 20),
    .ADDIW .x7 .x7 (837 : BitVec 12),
    .BGEU .x6 .x7 (brOff (GuestAddrs.bal_builder_append_code + 172) (GuestAddrs.bal_builder_append_code + 52)),
    .SLLI .x7 .x6 (6 : BitVec 6),
    .AUIPC .x28 (laHi GuestAddrs.bal_builder_code_changes (GuestAddrs.bal_builder_append_code + 60)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bal_builder_code_changes (GuestAddrs.bal_builder_append_code + 60)),
    .ADD .x28 .x28 .x7,
    .LD .x29 .x2 (8 : BitVec 12),
    .LI .x30 (20 : Word),
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x29 (0 : BitVec 12),
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x28 (laHi GuestAddrs.bal_builder_code_changes (GuestAddrs.bal_builder_append_code + 108)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bal_builder_code_changes (GuestAddrs.bal_builder_append_code + 108)),
    .SLLI .x7 .x6 (6 : BitVec 6),
    .ADD .x28 .x28 .x7,
    .LD .x29 .x2 (16 : BitVec 12),
    .SD .x28 .x29 (24 : BitVec 12),
    .LD .x29 .x2 (24 : BitVec 12),
    .SD .x28 .x29 (32 : BitVec 12),
    .LD .x29 .x2 (32 : BitVec 12),
    .SD .x28 .x29 (40 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_code_count (GuestAddrs.bal_builder_append_code + 152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_code_count (GuestAddrs.bal_builder_append_code + 152)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (36 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_code_overflow (GuestAddrs.bal_builder_append_code + 172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_code_overflow (GuestAddrs.bal_builder_append_code + 172)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_overflow (GuestAddrs.bal_builder_append_code + 188)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_overflow (GuestAddrs.bal_builder_append_code + 188)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balBuilderAppendCode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balBuilderAppendCode_relocs : RelocTable :=
  [ (6, .jal .x1 "bal_builder_ensure_account"),
    (8, .la .x5 "bal_builder_code_count"),
    (15, .la .x28 "bal_builder_code_changes"),
    (27, .la .x28 "bal_builder_code_changes"),
    (38, .la .x5 "bal_builder_code_count"),
    (43, .la .x5 "bal_builder_code_overflow"),
    (47, .la .x5 "bal_builder_overflow") ]

def balBuilderAppendCodeFunction : String :=
  "bal_builder_append_code:\n" ++ emitProgramR balBuilderAppendCode_prog balBuilderAppendCode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balBuilderAppendCode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balBuilderAppendCodeFunction_eq_prog :
    balBuilderAppendCodeFunction = "bal_builder_append_code:\n" ++ emitProgramR balBuilderAppendCode_prog balBuilderAppendCode_relocs := rfl

#guard balBuilderAppendCodeFunction.startsWith "bal_builder_append_code:\n"
#guard balBuilderAppendCode_prog.length = 54

def blockAccessListBuilderFunctions : String :=
  balSerializerAddrMatchesFunction ++ "\n" ++
  balSerializerAddrMatchesBeFunction ++ "\n" ++
  balSerializerSlotEqFunction ++ "\n" ++
  balSerializerSlotWrittenFunction ++ "\n" ++
  balSerializerSlotSeenBeforeFunction ++ "\n" ++
  balSerializerU64ToFieldFunction ++ "\n" ++
  -- bal_serializer_filter_reads: never jal'd from guest; probe/selftest only.
  balSerializerMeasureReadsFunction ++ "\n" ++
  balSerializerSlotToLeFunction ++ "\n" ++
  balSerializerBalanceToLeFunction ++ "\n" ++
  balSerializerMeasureSlotFunction ++ "\n" ++
  balSerializerMeasureStorageFunction ++ "\n" ++
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
  balSerializerVerifyFunction ++ "\n" ++
  balBuilderEnsureAccountFunction ++ "\n" ++
  balBuilderIncorporateTouchedAccountsFunction ++ "\n" ++
  balBuilderRecordStorageChangeFunction ++ "\n" ++
  balEmitStorageChangesFunction ++ "\n" ++
  balBuilderAppendBalanceFunction ++ "\n" ++
  balBuilderAppendNonceFunction ++ "\n" ++
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
-- `0x80 | 20`. (GH #11054: this used to cite `bal_sort_account_writes`, which passed the
-- same value and has since been deleted as unreachable; the CONSTANT is the contract, not
-- that routine.) The value stays pinned on the BalCanonicalSort.lean side by the width/offset
-- guards there, which are value-level and so survived the deletion. Writing 0x1400 declares a
-- big-endian address little-endian and faults inside the sort on a bad pointer.
#guard (balSerializerRebuildHashFunction.splitOn "li x14, 3").length == 2

-- ALL SEVEN ORDERING RULES, as FIVE sort calls: storage (carrying two rules in one
-- multi-segment pass), reads, balance, nonce, code, accounts. Six of these were missing
-- entirely and no probe could see it, because a one-element list is sorted by definition
-- and every case had one element at every inner level.
#guard (balSerializerRebuildHashFunction.splitOn "jal x1, bal_canonical_sort").length == 7
#guard (balSerializerRebuildHashFunction.splitOn "li x12,").length == 7
#guard (balSerializerRebuildHashFunction.splitOn "li x12, 96").length == 2
#guard (balSerializerRebuildHashFunction.splitOn "li x12, 64").length == 4
#guard (balSerializerRebuildHashFunction.splitOn "li x12, 40").length == 2
#guard (balSerializerRebuildHashFunction.splitOn "li x12, 24").length == 2
-- Every stride 8-ALIGNED: 96, 64, 64, 40, 64, 24.
#guard (balSerializerRebuildHashFunction.splitOn "li x12, 96").length == 2
#guard (balSerializerRebuildHashFunction.splitOn "li x12, 40").length == 2
#guard [96, 64, 40, 24].all (fun w => w % 8 == 0)

-- Stride 24, which is 8-ALIGNED, per the rule on `balBuilderAccountRowBytes`: the sort
-- swaps rows with ld/sd, and AGENTS.md:211 gives those no semantics off an 8-boundary.
#guard (balSerializerRebuildHashFunction.splitOn "li x12, 24").length == 2
#guard balBuilderAccountRowBytes % 8 == 0
-- ...and it must precede the emission, not follow it.
#guard (((balSerializerRebuildHashFunction.splitOn "jal x1, bal_serializer_emit_outer").getD 0 "").splitOn "jal x1, bal_canonical_sort").length == 7

-- A nonzero sort status must abort rather than fall through to emitting an unsorted BAL.
#guard (balSerializerRebuildHashFunction.splitOn "bne x10, x0, .+384").length == 2

-- The converted serializer routines are pinned by their generated Program lengths
-- and per-function fixture byte-identity checks. Their old String split guards
-- depended on raw labels, semicolon grouping, and ABI aliases; `emitProgramR`
-- intentionally emits resolved offsets and canonical register names, so those
-- source-form guards are not applicable after conversion.

/-! ## Guards for the outer accumulation -/

#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_measure_outer:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_outer:").length == 2
-- The outer payload is a sum of ENCODED sizes. Summing the accounts' payloads instead
-- leaves the outer header short by one header per account -- well-formed RLP, wrong
-- hash, and no intermediate check notices. The `list_header_len` call is the conversion.

-- Each account is re-measured immediately before being emitted. The length table holds
-- ONE account, and `measure_outer` leaves it on whichever account it saw last, so
-- emitting without re-measuring would give every account the last one's headers.

-- It does NOT sort. Ordering is `bal_canonical_sort`'s job and must precede this; an
-- unsorted emission is a well-formed BAL with the wrong hash. Pinning the absence keeps
-- the docstring's claim and the code in agreement.

/-! ## `block_access_index` values, verified against the spec

    The spec assigns the index in `fork.py`:

      per transaction   `block_access_index = index + Uint(1)`  (`:1040`), so the 0-based
                        transaction `i` stamps `i + 1`
      post-execution    `ulen(transactions) + Uint(1)`          (`:917`), i.e. N+1
      system            0, the value before any transaction sets it

    The guest realizes all three channels:
    * live begin/end system-call paths pass `0` as an explicit argument to
      `bal_builder_record_storage_change`;
    * user-transaction rows read `current_block_access_index`, which the MTx entry
      paths set to `bv_mtx_i + 1` (`BlockVerdictMtxRuntime.lean:519,547,909`); and
    * post-execution rows use the same global after it is set to `bv_tx_count + 1`
      (`BlockVerdictMtxRuntime.lean:759`, `BlockVerdictStateRoot.lean:875`).

    The explicit-argument channel is intentionally invisible to a census of stores
    to `current_block_access_index`: such a census sees only the user and post-
    execution writers and falsely concludes that BAI 0 has no producer.  The
    system path has no reference to that global, so it cannot accidentally read a
    stale user/post value.  This was the false premise behind #11104; the channel
    distinction, rather than a missing store, is the invariant to preserve.

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
-- #10820: the balance value is now emitted from the LE scratch rather than from `row+32`,
-- so the adjacency is keyed on that buffer instead. The ORDER property being pinned is
-- unchanged -- widened index first, value second. This guard caught the fix: it was pinning
-- the raw `row+32` hand-off, which is exactly the defect, so it failed the moment the
-- hand-off was removed. A guard that pins an emitted form will always do that, and the
-- right response is to re-pin the corrected form rather than to relax the guard.
-- Nonce emits the index and the nonce from the SAME buffer, re-widened between the two,
-- so adjacency cannot separate them; pin the re-widen count instead. Four widens: two to
-- measure the pair, two to re-emit it in order.

-- SlotChanges is `slot` then `changes`: the slot scalar must precede the inner list.

/-! ## Guards for the field emitters and the account emitter -/

#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_reads:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_balance:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_nonce:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_code:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_account:").length == 2

-- The reads emitter uses the REVERSING comparator, matching its measurer. Read rows come
-- from the exec log and hold an LE stack word; builder rows are big-endian. Swapping the
-- two comparators silently matches nothing rather than erroring.
-- ...and every OTHER emitter uses the big-endian one.

-- Nonce widens FOUR times, not two: the scalar field is one shared buffer, so measuring
-- the pair overwrites it and both members must be re-widened before being emitted.
-- Emitting straight after the measure loop sends the nonce twice and drops the index.

-- The account emitter reads SIX table entries and emits six headers; it must never
-- recompute a length. And the address goes through emit_bytes, never emit_address.
-- All five field emitters called, in AccountChanges order.
-- All five field emitters, IN AccountChanges ORDER. An RLP list is positional: swapping
-- two field emitters yields a well-formed account with the fields exchanged, and if both
-- are empty lists it is byte-identical. Order pinned by the sequence below, not by count
-- alone.

/-! ## Guards for the storage emitter -/

#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_emit_storage:").length == 2

-- THREE list headers per slot: SlotChanges, the changes list, and each StorageChange.
-- Same three levels the measurer counts; dropping one leaves well-formed RLP of the
-- wrong shape, and the only symptom is a different digest.

-- Every nested length comes from the SHARED measurer. Emission is streaming, so a header
-- absorbed before its payload cannot be backpatched -- a locally recomputed length is
-- free to drift from the measure pass and nothing but the digest would show it.

-- It must NOT use `bal_rlp_emit_address`, which reverses its input for an LE stack word.
-- Builder rows hold the address big-endian, so that helper would silently reverse it.

-- Same walk shape as the measurer: address filter at both loop levels, dedup at the outer.

/-! ## Guards for the slot byte-order conversion -/

-- `slot_written` compares ACROSS conventions: an LE read slot against a BE row slot, so
-- byte i against byte 31-i. A dword-wise compare matches only palindromic slots.

#guard (blockAccessListBuilderDataSection.splitOn "bal_serializer_slot_le:").length == 2

-- BOTH readers of the slot must go through the reversal. The row's slot is BE32 and the
-- scalar pair reads LE limbs, so a direct `row+32` hand-off is the defect this fixes --
-- and it is invisible to any probe that seeds rows in the reader's convention.

-- #10820: the BALANCE leg has the identical shape to the slot leg above -- a BE32 field
-- handed to the LE-only scalar pair. BOTH readers must go through the reversal, and the
-- direct `row+32` hand-off must not come back. Positive guards pin the reversal; negative
-- guards pin the absence of the raw hand-off, because a reversal that is present while the
-- raw pass ALSO survives would measure one buffer and emit the other.
-- Measure and emit must consume the SAME buffer, or the length prefix and payload diverge.
#guard (blockAccessListBuilderDataSection.splitOn "bal_serializer_balance_le:").length == 2

-- The VALUE is passed verbatim and must NOT be reversed -- same row, opposite convention.

/-! ## Guards for the shared slot measurement -/

#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_measure_slot:").length == 2

-- The whole point of the factoring is that BOTH passes call it. `measure_storage` must
-- not carry its own copy of the inner walk: two copies of this arithmetic drift, and a
-- drifted emit-side copy shows up only as a wrong digest, with the length table, the
-- per-field measurements and every structural check still agreeing.

-- It returns two payloads, not one encoded size. `a1` is the inner changes-list payload,
-- which the emit pass cannot get anywhere else -- the length table holds one entry for
-- the whole field, and the per-slot change count is unbounded.

/-! ## Guards for the storage-change upsert -/

-- Emitted at all.
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_record_storage_change:").length == 2

-- IT MUST BE AN UPSERT. `add_storage_write` (block_access_lists.py:352-367) replaces
-- the value when a row already carries this (address, slot, block_access_index) and
-- appends only on no match. Without the scan this is an append, and a caller invoking
-- it twice for one key gets two rows where the spec keeps one -- a well-formed BAL
-- with the wrong entry count and therefore the wrong hash.
#guard (balBuilderRecordStorageChangeFunction.splitOn "bgeu x29, x6, .+180").length == 2
#guard (balBuilderRecordStorageChangeFunction.splitOn "jal x0, .+220").length == 2

-- The hit path must NOT bump the count -- that is what "keeping only the final write"
-- means. Guard the COUNT STORE specifically: the bare `sd t1, 0(t0)` also appears on
-- the overflow path twice (two flags), so counting that would pass for the wrong
-- reason. The count is stored exactly once, and only on the append path.
#guard (balBuilderRecordStorageChangeFunction.splitOn "la x5, bal_builder_storage_change_count\n  sd x6, 0(x5)").length == 2
-- ...and the hit path returns without reaching it.
#guard (balBuilderRecordStorageChangeFunction.splitOn "jal x0, .+32").length == 2

-- Row offsets must match the documented layout AND balSortBuilderStorageSegments:
-- address@0, BAI@24, slot@32, value@64. A stride or offset drift here is silent --
-- the sorter would key on the wrong bytes and still produce a total order.
#guard (balBuilderRecordStorageChangeFunction.splitOn "sd x7, 24(x30)").length == 2
#guard (balBuilderRecordStorageChangeFunction.splitOn "sd x7, 32(x30)").length == 2
#guard (balBuilderRecordStorageChangeFunction.splitOn "sd x7, 64(x30)").length == 3
#guard (balBuilderRecordStorageChangeFunction.splitOn "li x7, 96").length == 3

-- The prose and the constant must agree on the row size. They did not: the file said
-- "80-byte builder stream" while the constant and the layout said 96, so a walk sized
-- from the prose would read every row after the first at the wrong offset.

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
#guard (balEmitStorageChangesFunction.splitOn "jal x1, slot_at_header_state_root").length == 2

-- Both keys must be reversed to big-endian before either call: tx rows hold LE stack
-- words, the reader wants BE, and the builder row wants BE to match
-- balSortBuilderStorageSegments. Passing a row field straight through names a
-- DIFFERENT slot -- a well-formed 32-byte wrong answer.
#guard (balEmitStorageChangesFunction.splitOn "besc_addr_be").length == 5
#guard (balEmitStorageChangesFunction.splitOn "besc_slot_be").length == 5

-- The net-zero exclusion must compare all four limbs and skip on equality. Comparing
-- fewer would emit entries the spec omits whenever the differing limb is unchecked.
#guard (balEmitStorageChangesFunction.splitOn "bne x7, x31, .+44").length == 2
#guard (balEmitStorageChangesFunction.splitOn "bne x7, x31, .+32").length == 2
#guard (balEmitStorageChangesFunction.splitOn "bne x7, x31, .+20").length == 2
#guard (balEmitStorageChangesFunction.splitOn "bne x7, x31, .+8").length == 3

-- It must call the UPSERT, not append: same (address, slot, BAI) keeps only the final
-- write.
#guard (balEmitStorageChangesFunction.splitOn "jal x0, .+120").length == 2
#guard (balEmitStorageChangesFunction.splitOn "jal x1, bal_builder_record_storage_change").length == 2

-- It must measure the FILTERED list, not the raw read set: measuring the raw set sizes
-- the header for slots emit will not write, and the buffer is well-formed with a long
-- header.
-- It applies BOTH predicates -- the same routines the filter and the emit use -- rather
-- than walking a materialised survivor list, which no longer exists. Re-running one
-- routine cannot diverge from itself, which is what made the list unnecessary.
-- The entry goes in the +16 slot, per the table's pinned layout. A wrong slot is
-- silent: emit reads a plausible number written for another field.
-- Same-layer pair: the scalar measurer whose emitter counterpart is bal_rlp_emit_scalar.

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
#guard (balSerializerU64ToFieldFunction.splitOn "  sd x11, 0(x10)\n").length == 2
#guard (balSerializerU64ToFieldFunction.splitOn "li t4, 31; sub t4, t4, t1").length == 1
-- The widener's DESTINATION must be reserved. A routine referencing a missing data symbol
-- builds fine in Lean and fails only at LINK, with a message naming the symbol rather than
-- the routine -- so the reservation is guarded next to the routine that needs it.
#guard (blockAccessListBuilderDataSection.splitOn "bal_serializer_u64_field:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_serializer_filter_reads:").length == 1
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
-- All five field measurers must be called, or a field contributes zero and its table entry
-- is whatever the previous account left there.
-- The code measurer must use the throwaway route, never a generic measurer.

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
-- ... and the split across the two must stay 2 (StorageChange, changes list) + 1
-- (SlotChanges), since the emit pass reads the inner two from `measure_slot`'s two
-- return values and writes the outer one itself.
-- Two scalars per change (BAI, new_value) plus one per slot.
-- Each distinct slot measured EXACTLY ONCE, or a slot with three changes contributes its
-- SlotChanges three times.
-- Per account at BOTH loop levels: without the inner check, another account's change to
-- the same slot is folded into this account's list.
-- The +8 slot, per the pinned table layout.
-- The seen-before scan must look only at EARLIER rows, or every row reports itself seen
-- and the field measures as empty.

/-! ## Guards for the serializer's scratch -/

-- SIX entries per account, one per header emit writes: the account list plus its five
-- field lists. Storing only the account total would force emit to recompute the five,
-- which is the duplication the table exists to prevent.
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

-- 140000 * 24. Was 1846152 at capacity 76923; +1,513,848 bytes with the
-- GH #10836 resize (six system calls bypass the block gas counters).
#guard balBuilderAccountBytes = 3360000
#guard balBuilderStorageChangeBytes = 4562112
#guard balBuilderBalanceBytes = 6720000
#guard balBuilderNonceBytes = 1400000
#guard balBuilderCodeBytes = 840000
#guard balBuilderPersistentBytes = 16882112
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_ensure_account:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_append_balance:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_append_nonce:").length == 2
#guard (blockAccessListBuilderFunctions.splitOn "bal_builder_append_code:").length == 2

end EvmAsm.Codegen
