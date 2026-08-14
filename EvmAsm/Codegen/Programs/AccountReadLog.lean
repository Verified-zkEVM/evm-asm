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

  32 B stride over `ACCOUNT_READS_AREA` (`0xa24349c0`, 16384 entries). The key is
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
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## `account_read_record`

    Calling convention:
      a0 = 20-byte big-endian address pointer (exactly what
           `account_state_latest_balance` / `_latest_nonce` receive in `a0`)
      ra = return
      no result register.

    Clobbers nothing the caller can see: `t0`-`t6` are saved and restored, and
    `a0` is only read. That matters because the call sites are the *accessors*
    themselves, which are holding caller state in `a0`/`a1` at entry. -/
def accountReadRecord_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x5 (0 : BitVec 12),
    .SD .x2 .x6 (8 : BitVec 12),
    .SD .x2 .x7 (16 : BitVec 12),
    .SD .x2 .x28 (24 : BitVec 12),
    .SD .x2 .x29 (32 : BitVec 12),
    .SD .x2 .x30 (40 : BitVec 12),
    .SD .x2 .x31 (48 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_account_read_suppress (GuestAddrs.account_read_record + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_account_read_suppress (GuestAddrs.account_read_record + 32)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (brOff (GuestAddrs.account_read_record + 256) (GuestAddrs.account_read_record + 44)),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_reads_count (GuestAddrs.account_read_record + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_reads_count (GuestAddrs.account_read_record + 48)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (4 : BitVec 20),
    .BGEU .x6 .x7 (brOff (GuestAddrs.account_read_record + 240) (GuestAddrs.account_read_record + 64)),
    .LUI .x7 (162 : BitVec 20),
    .ADDIW .x7 .x7 (1077 : BitVec 12),
    .SLLI .x7 .x7 (12 : BitVec 6),
    .ADDI .x7 .x7 (-1600 : BitVec 12),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_read_record + 156) (GuestAddrs.account_read_record + 88)),
    .SLLI .x29 .x28 (5 : BitVec 6),
    .ADD .x29 .x7 .x29,
    .LI .x30 (0 : Word),
    .LI .x31 (20 : Word),
    .BEQ .x30 .x31 (brOff (GuestAddrs.account_read_record + 256) (GuestAddrs.account_read_record + 108)),
    .ADD .x31 .x29 .x30,
    .LBU .x31 .x31 (0 : BitVec 12),
    .ADD .x5 .x10 .x30,
    .LBU .x5 .x5 (0 : BitVec 12),
    .BNE .x31 .x5 (12 : BitVec 13),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_reads_count (GuestAddrs.account_read_record + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_reads_count (GuestAddrs.account_read_record + 140)),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_read_record + 88) (GuestAddrs.account_read_record + 152)),
    .SLLI .x29 .x6 (5 : BitVec 6),
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
    .AUIPC .x5 (laHi GuestAddrs.tx_account_reads_count (GuestAddrs.account_read_record + 216)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_reads_count (GuestAddrs.account_read_record + 216)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x0 (20 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_reads_overflow (GuestAddrs.account_read_record + 240)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_reads_overflow (GuestAddrs.account_read_record + 240)),
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

/-- Reloc side-table for `accountReadRecord_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountReadRecord_relocs : RelocTable :=
  [ (8, .la .x5 "runtime_tx_account_read_suppress"),
    (12, .la .x5 "tx_account_reads_count"),
    (35, .la .x5 "tx_account_reads_count"),
    (54, .la .x5 "tx_account_reads_count"),
    (60, .la .x5 "tx_account_reads_overflow") ]

def accountReadRecordFunction : String :=
  "account_read_record:\n" ++ emitProgramR accountReadRecord_prog accountReadRecord_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountReadRecord_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountReadRecordFunction_eq_prog :
    accountReadRecordFunction = "account_read_record:\n" ++ emitProgramR accountReadRecord_prog accountReadRecord_relocs := rfl

#guard accountReadRecordFunction.startsWith "account_read_record:\n"
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
def accountAtHeaderStateRootTracked_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x10 (8 : BitVec 12),
    .SD .x2 .x11 (16 : BitVec 12),
    .SD .x2 .x12 (24 : BitVec 12),
    .SD .x2 .x13 (32 : BitVec 12),
    .SD .x2 .x14 (40 : BitVec 12),
    .SD .x2 .x15 (48 : BitVec 12),
    .SD .x2 .x16 (56 : BitVec 12),
    .MV .x10 .x12,
    .JAL .x1 (jalOff GuestAddrs.account_read_record (GuestAddrs.account_at_header_state_root_tracked + 40)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x10 .x2 (8 : BitVec 12),
    .LD .x11 .x2 (16 : BitVec 12),
    .LD .x12 .x2 (24 : BitVec 12),
    .LD .x13 .x2 (32 : BitVec 12),
    .LD .x14 .x2 (40 : BitVec 12),
    .LD .x15 .x2 (48 : BitVec 12),
    .LD .x16 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JAL .x0 (jalOff GuestAddrs.account_at_header_state_root (GuestAddrs.account_at_header_state_root_tracked + 80)) ]

/-- Reloc side-table for `accountAtHeaderStateRootTracked_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountAtHeaderStateRootTracked_relocs : RelocTable :=
  [ (10, .jal .x1 "account_read_record"),
    (20, .jal .x0 "account_at_header_state_root") ]

def accountAtHeaderStateRootTrackedFunction : String :=
  "account_at_header_state_root_tracked:\n" ++ emitProgramR accountAtHeaderStateRootTracked_prog accountAtHeaderStateRootTracked_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountAtHeaderStateRootTracked_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountAtHeaderStateRootTrackedFunction_eq_prog :
    accountAtHeaderStateRootTrackedFunction = "account_at_header_state_root_tracked:\n" ++ emitProgramR accountAtHeaderStateRootTracked_prog accountAtHeaderStateRootTracked_relocs := rfl

#guard accountAtHeaderStateRootTrackedFunction.startsWith "account_at_header_state_root_tracked:\n"
/-- Cursor + overflow flag for the `account_reads` container. Block-lifetime:
    never reset per transaction, never restored on rollback. -/
def accountReadLogDataSection : String :=
  "tx_account_reads_count:\n  .zero 8\n" ++
  "tx_account_reads_overflow:\n  .zero 8\n"

end EvmAsm.Codegen
