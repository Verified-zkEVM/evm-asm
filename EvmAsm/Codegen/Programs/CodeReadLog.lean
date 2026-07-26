/-
  EvmAsm.Codegen.Programs.CodeReadLog

  GH #10619 — the `code_reads` container's producer, plus the **tracked code
  accessor** that mirrors the spec's two-accessor shape.

  ## The firing condition is a FALLTHROUGH, unlike the other two read sets

  `state_tracker.py:233-270` `get_code`:

  * `:263` — `code_hash == EMPTY_CODE_HASH` returns `b""` **without recording**;
  * `:265-268` — a hit in `tx_state.code_writes` or `parent.code_writes` returns
    **without recording**;
  * `:269-270` — only on falling through to `pre_state.get_code` does it
    `code_reads.add((address, code_hash))`, and it records **before** the fetch, so
    a miss records too.

  `account_reads` (`:139`) and `storage_reads` (`:295`) are the opposite — recorded
  unconditionally at the top, before writes are consulted. Three sets, three
  conditions; a single recorder parameterised by kind would over-record here.
  Over-recording is not a harmless surplus: `code_reads` feeds witness code
  selection (`stateless_host_exec_witness.py:182` `get_witness_codes`), so a
  surplus entry invents a witness code the spec never emits.

  ## Two entries over one implementation, because the spec has two accessors

  The spec distinguishes the **tracked accessor** `get_code` from the **raw store**
  `pre_state.get_code`, and only the former records. The guest already had the raw
  store — `witness_codes_lookup_by_hash` — so this file adds the tracked entry
  rather than a flag or a per-caller obligation:

  * `code_read_fetch` — tracked. Skips `EMPTY_CODE_HASH`, records, forwards.
  * `witness_codes_lookup_by_hash` — untouched, non-recording.

  Leaving the raw store untouched matters for a second reason: it is not
  hand-written, it is **derived** by string-renaming `witnessLookupByHashFunction`
  (`WitnessCodeLookup.lean`), so editing it would also have edited the MPT witness
  lookup that *state* lookups use.

  ## Routing (decided by what the spec records, not by which proof survives)

  `vm/instructions/environment.py:399-400` — EXTCODECOPY does
  `get_code(tx_state, code_hash, address)`, i.e. it goes through the **tracked**
  accessor. So execution call sites route here even where they reach the helper
  from a verified Program. BAL preimage verification
  (`BalCodePreimages.lean:942, :972`) is *not* execution reading code and keeps the
  raw entry.

  The `address` argument is not awkward threading: the spec's own accessor takes
  `(tx_state, code_hash, address)` precisely because the `CodeRead` tuple needs
  both.

  ## Entry layout

      +0  address  (20 B big-endian, zero-padded to 32)
      +32 codeHash (32 B)

  64 B stride over `CODE_READS_AREA` (`0xa1d20000`, 8192 entries). All comparisons
  and copies here are **byte-wise** (`lbu`/`sb`): the hash and address pointers come
  from SSZ/witness structures with no guaranteed 8-alignment, and the verified RV64
  semantics require `ld`/`sd` to be 8-aligned.

  Block lifetime: never reset per transaction, never restored on rollback,
  mirroring `restore_tx_state` (`:809-826`) leaving `code_reads` alone.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

/-! ## `code_read_record`

    a0 = 20-byte address ptr, a1 = 32-byte code-hash ptr. Clobbers nothing
    visible: `t0`-`t6` are saved/restored and `a0`/`a1` are only read. -/
def codeReadRecordFunction : String :=
  "code_read_record:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)\n" ++
  "  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)\n" ++
  "  la t0, code_reads_count; ld t1, 0(t0)\n" ++
  "  li t2, 8192\n" ++
  "  bgeu t1, t2, .Lcrr_overflow\n" ++
  "  li t2, 0xa1d20000\n" ++
  "  li t3, 0\n" ++                                          -- i
  ".Lcrr_scan:\n" ++
  "  bgeu t3, t1, .Lcrr_append\n" ++
  "  slli t4, t3, 6; add t4, t2, t4\n" ++                     -- &entry[i]
  "  li t5, 0\n" ++
  ".Lcrr_cmp_addr:\n" ++                                      -- 20-byte address
  "  li t6, 20; beq t5, t6, .Lcrr_cmp_hash\n" ++
  "  add t6, t4, t5; lbu t6, 0(t6)\n" ++
  "  add t0, a0, t5; lbu t0, 0(t0)\n" ++
  "  bne t6, t0, .Lcrr_next\n" ++
  "  addi t5, t5, 1; j .Lcrr_cmp_addr\n" ++
  ".Lcrr_cmp_hash:\n" ++                                      -- 32-byte hash at +32
  "  li t5, 0\n" ++
  ".Lcrr_cmp_hash_loop:\n" ++
  "  li t6, 32; beq t5, t6, .Lcrr_done\n" ++
  "  add t6, t4, t5; lbu t6, 32(t6)\n" ++
  "  add t0, a1, t5; lbu t0, 0(t0)\n" ++
  "  bne t6, t0, .Lcrr_next\n" ++
  "  addi t5, t5, 1; j .Lcrr_cmp_hash_loop\n" ++
  ".Lcrr_next:\n" ++
  "  la t0, code_reads_count\n" ++
  "  addi t3, t3, 1; j .Lcrr_scan\n" ++
  ".Lcrr_append:\n" ++
  "  slli t4, t1, 6; add t4, t2, t4\n" ++
  -- zero the slot so bytes 20..31 are padding we WROTE, not slab contents
  "  sd zero, 0(t4); sd zero, 8(t4); sd zero, 16(t4); sd zero, 24(t4)\n" ++
  "  li t5, 0\n" ++
  ".Lcrr_cp_addr:\n" ++
  "  li t6, 20; beq t5, t6, .Lcrr_cp_hash\n" ++
  "  add t6, a0, t5; lbu t6, 0(t6)\n" ++
  "  add t0, t4, t5; sb t6, 0(t0)\n" ++
  "  addi t5, t5, 1; j .Lcrr_cp_addr\n" ++
  ".Lcrr_cp_hash:\n" ++
  "  li t5, 0\n" ++
  ".Lcrr_cp_hash_loop:\n" ++
  "  li t6, 32; beq t5, t6, .Lcrr_bump\n" ++
  "  add t6, a1, t5; lbu t6, 0(t6)\n" ++
  "  add t0, t4, t5; sb t6, 32(t0)\n" ++
  "  addi t5, t5, 1; j .Lcrr_cp_hash_loop\n" ++
  ".Lcrr_bump:\n" ++
  "  la t0, code_reads_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  j .Lcrr_done\n" ++
  ".Lcrr_overflow:\n" ++
  "  la t0, code_reads_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lcrr_done:\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)\n" ++
  "  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-! ## `code_read_fetch` — the guest's tracked `get_code`

    Same convention as `witness_codes_lookup_by_hash` plus the address:
      a0 = section ptr, a1 = section_len, a2 = 32-byte code-hash ptr,
      a3 = offset out ptr, a4 = length out ptr, a5 = 20-byte address ptr
      a0 (output) = forwarded from the raw store (0 hit, 1 miss).

    Records BEFORE forwarding and regardless of hit/miss, because the spec does
    (`:269` adds, then `:270` returns the fetch). Skips `EMPTY_CODE_HASH`, which
    `:263` returns on without recording — an EOA's empty code is the common case,
    so omitting that skip would enter a witness-code entry on nearly every
    account touch. -/
def codeReadFetchFunction : String :=
  "code_read_fetch:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp); sd a2, 24(sp)\n" ++
  "  sd a3, 32(sp); sd a4, 40(sp); sd a5, 48(sp)\n" ++
  -- EMPTY_CODE_HASH check, byte-wise (the hash ptr has no alignment guarantee)
  "  la t0, ecc_empty_code_hash\n" ++
  "  li t1, 0\n" ++
  ".Lcrf_empty_cmp:\n" ++
  "  li t2, 32; beq t1, t2, .Lcrf_skip\n" ++
  "  add t2, t0, t1; lbu t2, 0(t2)\n" ++
  "  add t3, a2, t1; lbu t3, 0(t3)\n" ++
  "  bne t2, t3, .Lcrf_record\n" ++
  "  addi t1, t1, 1; j .Lcrf_empty_cmp\n" ++
  ".Lcrf_record:\n" ++
  "  mv a0, a5\n" ++                                          -- address ptr
  "  mv a1, a2\n" ++                                          -- code-hash ptr
  "  jal ra, code_read_record\n" ++
  ".Lcrf_skip:\n" ++
  "  ld ra, 0(sp); ld a0, 8(sp); ld a1, 16(sp); ld a2, 24(sp)\n" ++
  "  ld a3, 32(sp); ld a4, 40(sp); ld a5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  -- tail-call the RAW store, unmodified, with the original arguments
  "  j witness_codes_lookup_by_hash\n"

/-- Cursor, overflow flag, and `keccak256(b"")` = EMPTY_CODE_HASH for the skip.
    Block-lifetime: never reset per transaction, never restored on rollback. -/
def codeReadLogDataSection : String :=
  "code_reads_count:\n  .zero 8\n" ++
  "code_reads_overflow:\n  .zero 8\n" ++
  -- NO new EMPTY_CODE_HASH constant here, deliberately.  It would be INITIALIZED
  -- bytes in a NOBITS `.bss` context (which `as` rejects outright), and emitting it
  -- into `.data` instead grows that section and shifts every later data symbol --
  -- which broke pinned data addresses in Bn254FieldMulMod*/Bls12G1Lt* SAsm modules.
  -- The guest already emits this exact 32-byte constant SEVEN times
  -- (`ecc_empty_code_hash`, `chahsr_empty_code_hash`, ...), so `code_read_fetch`
  -- references an existing one rather than adding an eighth copy plus a layout shift.
  ""

end EvmAsm.Codegen
