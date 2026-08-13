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

  64 B stride over `CODE_READS_AREA` (`0xa24b49c0`, 8192 entries). All comparisons
  and copies here are **byte-wise** (`lbu`/`sb`): the hash and address pointers come
  from SSZ/witness structures with no guaranteed 8-alignment, and the verified RV64
  semantics require `ld`/`sd` to be 8-aligned.

  Block lifetime: never reset per transaction, never restored on rollback,
  mirroring `restore_tx_state` (`:809-826`) leaving `code_reads` alone.
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
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## `code_read_record`

    a0 = 20-byte address ptr, a1 = 32-byte code-hash ptr. Clobbers nothing
    visible: `t0`-`t6` are saved/restored and `a0`/`a1` are only read. -/
def codeReadRecord_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x5 (0 : BitVec 12),
    .SD .x2 .x6 (8 : BitVec 12),
    .SD .x2 .x7 (16 : BitVec 12),
    .SD .x2 .x28 (24 : BitVec 12),
    .SD .x2 .x29 (32 : BitVec 12),
    .SD .x2 .x30 (40 : BitVec 12),
    .SD .x2 .x31 (48 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.tx_code_reads_count (GuestAddrs.code_read_record + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_code_reads_count (GuestAddrs.code_read_record + 32)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (2 : BitVec 20),
    .BGEU .x6 .x7 (brOff (GuestAddrs.code_read_record + 300) (GuestAddrs.code_read_record + 48)),
    .LUI .x7 (162 : BitVec 20),
    .ADDIW .x7 .x7 (1205 : BitVec 12),
    .SLLI .x7 .x7 (12 : BitVec 6),
    .ADDI .x7 .x7 (-1600 : BitVec 12),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.code_read_record + 180) (GuestAddrs.code_read_record + 72)),
    .SLLI .x29 .x28 (6 : BitVec 6),
    .ADD .x29 .x7 .x29,
    .LI .x30 (0 : Word),
    .LI .x31 (20 : Word),
    .BEQ .x30 .x31 (32 : BitVec 13),
    .ADD .x31 .x29 .x30,
    .LBU .x31 .x31 (0 : BitVec 12),
    .ADD .x5 .x10 .x30,
    .LBU .x5 .x5 (0 : BitVec 12),
    .BNE .x31 .x5 (52 : BitVec 13),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x30 (0 : Word),
    .LI .x31 (32 : Word),
    .BEQ .x30 .x31 (brOff (GuestAddrs.code_read_record + 316) (GuestAddrs.code_read_record + 132)),
    .ADD .x31 .x29 .x30,
    .LBU .x31 .x31 (32 : BitVec 12),
    .ADD .x5 .x11 .x30,
    .LBU .x5 .x5 (0 : BitVec 12),
    .BNE .x31 .x5 (12 : BitVec 13),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.tx_code_reads_count (GuestAddrs.code_read_record + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_code_reads_count (GuestAddrs.code_read_record + 164)),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.code_read_record + 72) (GuestAddrs.code_read_record + 176)),
    .SLLI .x29 .x6 (6 : BitVec 6),
    .ADD .x29 .x7 .x29,
    .SD .x29 .x0 (0 : BitVec 12),
    .SD .x29 .x0 (8 : BitVec 12),
    .SD .x29 .x0 (16 : BitVec 12),
    .SD .x29 .x0 (24 : BitVec 12),
    .LI .x30 (0 : Word),
    .LI .x31 (20 : Word),
    .BEQ .x30 .x31 (28 : BitVec 13),
    .ADD .x31 .x10 .x30,
    .LBU .x31 .x31 (0 : BitVec 12),
    .ADD .x5 .x29 .x30,
    .SB .x5 .x31 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LI .x30 (0 : Word),
    .LI .x31 (32 : Word),
    .BEQ .x30 .x31 (28 : BitVec 13),
    .ADD .x31 .x11 .x30,
    .LBU .x31 .x31 (0 : BitVec 12),
    .ADD .x5 .x29 .x30,
    .SB .x5 .x31 (32 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.tx_code_reads_count (GuestAddrs.code_read_record + 276)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_code_reads_count (GuestAddrs.code_read_record + 276)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x0 (20 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.tx_code_reads_overflow (GuestAddrs.code_read_record + 300)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_code_reads_overflow (GuestAddrs.code_read_record + 300)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x5 .x2 (0 : BitVec 12),
    .LD .x6 .x2 (8 : BitVec 12),
    .LD .x7 .x2 (16 : BitVec 12),
    .LD .x28 .x2 (24 : BitVec 12),
    .LD .x29 .x2 (32 : BitVec 12),
    .LD .x30 .x2 (40 : BitVec 12),
    .LD .x31 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `codeReadRecord_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def codeReadRecord_relocs : RelocTable :=
  [ (8, .la .x5 "tx_code_reads_count"),
    (41, .la .x5 "tx_code_reads_count"),
    (69, .la .x5 "tx_code_reads_count"),
    (75, .la .x5 "tx_code_reads_overflow") ]

def codeReadRecordFunction : String :=
  "code_read_record:\n" ++ emitProgramR codeReadRecord_prog codeReadRecord_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `codeReadRecord_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem codeReadRecordFunction_eq_prog :
    codeReadRecordFunction = "code_read_record:\n" ++ emitProgramR codeReadRecord_prog codeReadRecord_relocs := rfl

#guard codeReadRecordFunction.startsWith "code_read_record:\n"
#guard codeReadRecord_prog.length = 88
/-! ## `code_read_fetch` — the guest's tracked `get_code`

    Same convention as `witness_codes_lookup_by_hash` plus the address:
      a0 = section ptr, a1 = section_len, a2 = 32-byte code-hash ptr,
      a3 = offset out ptr, a4 = length out ptr, a5 = 20-byte address ptr
      a0 (output) = forwarded from the raw store (0 hit, 1 miss).

    Records BEFORE forwarding and regardless of hit/miss, because the spec does
    (`:269` adds, then `:270` returns the fetch). Skips `EMPTY_CODE_HASH`, which
    `:263` returns on without recording — an EOA's empty code is the common case,
    so omitting that skip would enter a witness-code entry on nearly every
    account touch.

    Same-block CREATE code lives in `exec_code_effect_log` keyed by hash
    (`find_code_effect_by_hash`, GH #11542 / fixture 02274). A hash hit there
    is a successful `get_code` and must NOT fall through to
    `witness_codes_lookup_by_hash` — that miss was being published as cahsr
    status 5, which callers then misread as "unresolved preimage" (#12269).
    Effect-hash hit returns BEFORE `code_read_record` (spec `code_writes`
    exemption). That exemption must be exactly co-extensive with
    execution-produced code: no witness-supplied hash can reach
    `find_code_effect_by_hash` and be answered from it, or the narrowed
    ReceiptsTail ratchet (every non-empty demand recorded unless
    execution-produced) would silently cover forged preimages (#12251). -/
def codeReadFetch_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x10 (8 : BitVec 12),
    .SD .x2 .x11 (16 : BitVec 12),
    .SD .x2 .x12 (24 : BitVec 12),
    .SD .x2 .x13 (32 : BitVec 12),
    .SD .x2 .x14 (40 : BitVec 12),
    .SD .x2 .x15 (48 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.ecc_empty_code_hash (GuestAddrs.code_read_fetch + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ecc_empty_code_hash (GuestAddrs.code_read_fetch + 32)),
    .LI .x6 (0 : Word),
    .LI .x7 (32 : Word),
    .BEQ .x6 .x7 (brOff (GuestAddrs.code_read_fetch + 136) (GuestAddrs.code_read_fetch + 48)),
    .ADD .x7 .x5 .x6,
    .LBU .x7 .x7 (0 : BitVec 12),
    .ADD .x28 .x12 .x6,
    .LBU .x28 .x28 (0 : BitVec 12),
    .BNE .x7 .x28 (12 : BitVec 13),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.exec_code_effect_log (GuestAddrs.code_read_fetch + 80)),
    .ADDI .x10 .x10 (laLo GuestAddrs.exec_code_effect_log (GuestAddrs.code_read_fetch + 80)),
    .AUIPC .x5 (laHi GuestAddrs.exec_code_effect_count (GuestAddrs.code_read_fetch + 88)),
    .ADDI .x5 .x5 (laLo GuestAddrs.exec_code_effect_count (GuestAddrs.code_read_fetch + 88)),
    .LD .x11 .x5 (0 : BitVec 12),
    .LD .x12 .x2 (24 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.find_code_effect_by_hash (GuestAddrs.code_read_fetch + 104)),
    .MV .x6 .x10,
    .BNE .x6 .x0 (60 : BitVec 13),
    .LD .x15 .x2 (48 : BitVec 12),
    .LD .x12 .x2 (24 : BitVec 12),
    .MV .x10 .x15,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.code_read_record (GuestAddrs.code_read_fetch + 132)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x10 .x2 (8 : BitVec 12),
    .LD .x11 .x2 (16 : BitVec 12),
    .LD .x12 .x2 (24 : BitVec 12),
    .LD .x13 .x2 (32 : BitVec 12),
    .LD .x14 .x2 (40 : BitVec 12),
    .LD .x15 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JAL .x0 (jalOff GuestAddrs.witness_codes_lookup_by_hash (GuestAddrs.code_read_fetch + 168)),
    .LD .x7 .x6 (40 : BitVec 12),
    .LD .x28 .x2 (40 : BitVec 12),
    .SD .x28 .x7 (0 : BitVec 12),
    .ADDI .x7 .x6 (48 : BitVec 12),
    .LD .x28 .x2 (8 : BitVec 12),
    .SUB .x7 .x7 .x28,
    .LD .x28 .x2 (32 : BitVec 12),
    .SD .x28 .x7 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `codeReadFetch_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def codeReadFetch_relocs : RelocTable :=
  [ (8, .la .x5 "ecc_empty_code_hash"),
    (20, .la .x10 "exec_code_effect_log"),
    (22, .la .x5 "exec_code_effect_count"),
    (26, .jal .x1 "find_code_effect_by_hash"),
    (33, .jal .x1 "code_read_record"),
    (42, .jal .x0 "witness_codes_lookup_by_hash") ]

def codeReadFetchFunction : String :=
  "code_read_fetch:\n" ++ emitProgramR codeReadFetch_prog codeReadFetch_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `codeReadFetch_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem codeReadFetchFunction_eq_prog :
    codeReadFetchFunction = "code_read_fetch:\n" ++ emitProgramR codeReadFetch_prog codeReadFetch_relocs := rfl

#guard codeReadFetchFunction.startsWith "code_read_fetch:\n"
#guard codeReadFetch_prog.length = 55
/-- Cursor, overflow flag, and `keccak256(b"")` = EMPTY_CODE_HASH for the skip.
    Block-lifetime: never reset per transaction, never restored on rollback. -/
def codeReadLogDataSection : String :=
  "tx_code_reads_count:\n  .zero 8\n" ++
  "tx_code_reads_overflow:\n  .zero 8\n" ++
  -- NO new EMPTY_CODE_HASH constant here, deliberately.  It would be INITIALIZED
  -- bytes in a NOBITS `.bss` context (which `as` rejects outright), and emitting it
  -- into `.data` instead grows that section and shifts every later data symbol --
  -- which broke pinned data addresses in Bn254FieldMulMod*/Bls12G1Lt* SAsm modules.
  -- The guest already emits this exact 32-byte constant SEVEN times
  -- (`ecc_empty_code_hash`, `chahsr_empty_code_hash`, ...), so `code_read_fetch`
  -- references an existing one rather than adding an eighth copy plus a layout shift.
  ""

end EvmAsm.Codegen
