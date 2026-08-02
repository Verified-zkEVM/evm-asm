/-
  EvmAsm.Codegen.Programs.AccountReadLog

  GH #10619 — `account_read_record`: the producer for the guest's `account_reads`
  container, mirroring the spec's `account_reads` **set**.

  ## Firing condition: UNCONDITIONAL. This is not the same rule as code reads.

  The three read sets have three *different* recording disciplines, and a single
  recorder parameterised by kind would get one of them wrong:

  * `account_reads` — `state_tracker.py:139` records **as the first statement**,
    *before* the function consults `account_writes`. So an account read is
    recorded on **every** access, even when the value is ultimately served from a
    write. Same at `:199`.
  * `storage_reads` — `:295`, `:578`: also unconditional, recorded at the top.
  * `code_reads` — `:269`: the **opposite**. Recorded only after `code_writes`
    (tx *and* block) miss and the fetch falls through to `pre_state.get_code`,
    and `EMPTY_CODE_HASH` returns at `:263` without recording at all.

  So this routine records unconditionally, and the code-read producer must not
  copy its shape.

  ## Why not reuse `evm_access_account_table`

  That table is the EIP-2929 warm/cold set (`EvmAccessGas.lean`), and it is the
  wrong structure on three independent axes (#10621 ranks it P0 **MISSING**, not
  a counterpart): it is **tx-scoped and reset per transaction**, it is
  **pre-seeded** for protocol gas, and it answers "would this access be cold?"
  rather than "did execution touch this account?". Warmness cannot stand in for
  BAL touching. #10621's P2 row is explicit that the access tables' lifetime and
  semantics must not be merged with BAL/witness access tracking.

  ## Consumer

  `block_access_lists.py:696` iterates `block_state.account_reads` calling
  `add_touched_account` — so this set decides **which accounts appear in the BAL
  at all**. That is a real comparison surface, not future-proofing.

  ## Entry layout

      +0  address (20 B, big-endian) zero-padded to 32 B

  32 B stride over `ACCOUNT_READS_AREA` (`0xa1ea0000`, 16384 entries). The key is
  20 bytes because that is what the guest's own `account_state_find` compares
  (`li t4, 20`, byte-wise); the dedup loop below mirrors that shape deliberately.
  Bytes 20..31 are **explicitly zeroed** rather than left as whatever the slab
  held, so no later consumer can read padding as data — the hazard evm-asm3 hit
  with a mask living in a record's byte 20.

  Block lifetime: nothing here is reset per transaction and nothing is restored on
  rollback, mirroring `restore_tx_state` (`:809-826`) leaving `account_reads`
  alone.
  ## Two levels (GH #10619 review gate 3)

  This recorder targets the **TRANSACTION-level** arena, which is where the spec's
  `.add()` calls point (`tx_state.*_reads.add(...)`). The block-level arena is filled
  only by `read_sets_incorporate_tx`, mirroring `incorporate_tx_into_block`
  (`state_tracker.py:832`): merge up at `:858-861`, then CLEAR the tx set at
  `:879-881`. The clear is load-bearing — a merge without it double-counts across
  transactions in a multi-tx block, which a single-tx smoke test cannot see.

  `fork.py:745-752`'s throwaway `TransactionState`, whose reads are deliberately NOT
  promoted, is expressed by `read_sets_discard_tx` — a named operation rather than an
  absence.

-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

/-! ## `account_read_record`

    Calling convention:
      a0 = 20-byte big-endian address pointer (exactly what
           `account_state_latest_balance` / `_latest_nonce` receive in `a0`)
      ra = return
      no result register.

    Clobbers nothing the caller can see: `t0`-`t6` are saved and restored, and
    `a0` is only read. That matters because the call sites are the *accessors*
    themselves, which are holding caller state in `a0`/`a1` at entry. -/
def accountReadRecordFunction : String :=
  "account_read_record:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)\n" ++
  "  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)\n" ++
  "  la t0, runtime_tx_account_read_suppress; ld t1, 0(t0); bnez t1, .Larr_done\n" ++
  "  la t0, tx_account_reads_count; ld t1, 0(t0)\n" ++          -- t1 = count
  "  li t2, 16384\n" ++
  "  bgeu t1, t2, .Larr_overflow\n" ++
  "  li t2, 0xa1ea0000\n" ++                                 -- t2 = ACCOUNT_READS_AREA
  "  li t3, 0\n" ++                                          -- t3 = i
  ".Larr_scan:\n" ++
  "  bgeu t3, t1, .Larr_append\n" ++
  "  slli t4, t3, 5; add t4, t2, t4\n" ++                     -- t4 = &entry[i]
  -- 20-byte byte-wise compare, mirroring account_state_find's own loop.
  "  li t5, 0\n" ++
  ".Larr_bytes:\n" ++
  "  li t6, 20; beq t5, t6, .Larr_done\n" ++
  "  add t6, t4, t5; lbu t6, 0(t6)\n" ++
  "  add t0, a0, t5; lbu t0, 0(t0)\n" ++
  "  bne t6, t0, .Larr_next\n" ++
  "  addi t5, t5, 1; j .Larr_bytes\n" ++
  ".Larr_next:\n" ++
  "  la t0, tx_account_reads_count\n" ++                         -- t0 was clobbered by the compare
  "  addi t3, t3, 1; j .Larr_scan\n" ++
  ".Larr_append:\n" ++
  "  slli t4, t1, 5; add t4, t2, t4\n" ++                     -- t4 = &entry[count]
  -- zero the whole 32-byte slot first, so bytes 20..31 are padding we WROTE
  -- rather than whatever the slab happened to hold
  "  sd zero, 0(t4); sd zero, 8(t4); sd zero, 16(t4); sd zero, 24(t4)\n" ++
  "  li t5, 0\n" ++
  ".Larr_copy:\n" ++
  "  li t6, 20; beq t5, t6, .Larr_bump\n" ++
  "  add t6, a0, t5; lbu t6, 0(t6)\n" ++
  "  add t0, t4, t5; sb t6, 0(t0)\n" ++
  "  addi t5, t5, 1; j .Larr_copy\n" ++
  ".Larr_bump:\n" ++
  "  la t0, tx_account_reads_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  j .Larr_done\n" ++
  ".Larr_overflow:\n" ++
  "  la t0, tx_account_reads_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Larr_done:\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)\n" ++
  "  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-! ## `account_at_header_state_root_tracked` — the guest's tracked `get_account`

    ### Two entries over one implementation, because the spec has two accessors

    The spec distinguishes the **tracked accessor** `get_account(tx_state, address)`
    (`state_tracker.py:132-160`), which records at `:139`, from the **raw store**
    `pre_state.get_account`, which does not. The guest already had the raw store —
    `account_at_header_state_root` — so this adds the tracked entry rather than a
    flag or a per-caller obligation. Identical shape to `code_read_fetch` over
    `witness_codes_lookup_by_hash` (`CodeReadLog.lean`).

    ### Why not a flag, and why not hook the raw store

    Hooking the raw store would cover all callers with one edit and would record the
    **verification** reads too — `block_verdict` reaches it six times, and
    `bal_code_preimages_valid` once. Those are the guest checking a BAL against
    witnessed state, not execution touching an account, and recording them is the
    over-record that would make the BAL comparison monotone-but-wrong (a false
    ACCEPT, not a false reject). Same objection at 8 of the 21 sites.

    A classification table listing which callers are execution was the alternative,
    and it is the one that failed: four separate instruments mis-counted this exact
    set in one session (a single-call-form grep, a lowercase-only label pattern, a
    hand table that lost three rows, and source-level counting that missed
    `callDescendFallThrough`'s four instantiations). A table is a promise maintained
    by whoever last ran the search; the call graph is not. So the routing lives at
    the call site.

    Calling convention: **identical** to the raw entry, so a retarget is a one-token
    edit at each site.
      a0 = header_rlp ptr, a1 = header_rlp_len, a2 = 20-byte BE address ptr,
      a3 = address byte length, a4 = witness section ptr, a5 = section_len,
      a6 = 104-byte output struct ptr; a0 (output) forwarded unchanged (0=found,
      1=absent, 2..4=parse failures).

    Records **unconditionally and before** the lookup, because `:139` is the first
    statement of `get_account` and runs before `account_writes` is consulted — so an
    absent account (`a0=1`, authenticated absence) is still a read, exactly as the
    spec records one. This is the opposite discipline from `code_read_fetch`, which
    records only on a pre-state fallthrough; the difference is deliberate and is why
    these are separate routines rather than one parameterised by kind.

    All 13 execution call sites pass `a2` as a 20-byte big-endian address and `a3`
    as 20, checked individually, so `mv a0, a2` needs no per-site adaptation. -/
def accountAtHeaderStateRootTrackedFunction : String :=
  "account_at_header_state_root_tracked:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp); sd a2, 24(sp)\n" ++
  "  sd a3, 32(sp); sd a4, 40(sp); sd a5, 48(sp); sd a6, 56(sp)\n" ++
  "  mv a0, a2\n" ++                                          -- 20-byte BE address ptr
  "  jal ra, account_read_record\n" ++
  "  ld ra, 0(sp); ld a0, 8(sp); ld a1, 16(sp); ld a2, 24(sp)\n" ++
  "  ld a3, 32(sp); ld a4, 40(sp); ld a5, 48(sp); ld a6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  -- tail-call the RAW store, unmodified, with the original arguments
  "  j account_at_header_state_root\n"

/-- Cursor + overflow flag for the `account_reads` container. Block-lifetime:
    never reset per transaction, never restored on rollback. -/
def accountReadLogDataSection : String :=
  "tx_account_reads_count:\n  .zero 8\n" ++
  "tx_account_reads_overflow:\n  .zero 8\n"

end EvmAsm.Codegen
