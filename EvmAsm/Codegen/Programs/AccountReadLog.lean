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

  32 B stride over `ACCOUNT_READS_AREA` (`0xa1ca0000`, 16384 entries). The key is
  20 bytes because that is what the guest's own `account_state_find` compares
  (`li t4, 20`, byte-wise); the dedup loop below mirrors that shape deliberately.
  Bytes 20..31 are **explicitly zeroed** rather than left as whatever the slab
  held, so no later consumer can read padding as data — the hazard evm-asm3 hit
  with a mask living in a record's byte 20.

  Block lifetime: nothing here is reset per transaction and nothing is restored on
  rollback, mirroring `restore_tx_state` (`:809-826`) leaving `account_reads`
  alone.
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
  "  la t0, account_reads_count; ld t1, 0(t0)\n" ++          -- t1 = count
  "  li t2, 16384\n" ++
  "  bgeu t1, t2, .Larr_overflow\n" ++
  "  li t2, 0xa1ca0000\n" ++                                 -- t2 = ACCOUNT_READS_AREA
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
  "  la t0, account_reads_count\n" ++                         -- t0 was clobbered by the compare
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
  "  la t0, account_reads_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  j .Larr_done\n" ++
  ".Larr_overflow:\n" ++
  "  la t0, account_reads_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Larr_done:\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)\n" ++
  "  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-- Cursor + overflow flag for the `account_reads` container. Block-lifetime:
    never reset per transaction, never restored on rollback. -/
def accountReadLogDataSection : String :=
  "account_reads_count:\n  .zero 8\n" ++
  "account_reads_overflow:\n  .zero 8\n"

end EvmAsm.Codegen
