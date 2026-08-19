/-
Cohesion split from `AccountWriteMapTail.lean` (file-size guardrail, GH #12639):
the two account-resolver quartets (`prog`/`relocs`/`Function`/`eq_prog`) move
here unchanged.  Same defect class lives on in this file: the
`accountResolveExecutionState` block-tier scan base is the last stale
`0xbdb80000` reconstruction (#12614); verify its derivation separately before
fixing.  `AccountWriteMapTail.lean` imports this file, so existing importers
see these definitions transitively.
-/
import EvmAsm.Codegen.Programs.AccountWriteMap
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## account_resolve_pre_state

    Mirrors execution-specs `_get_pre_tx_account` (pinned `e5a8caf1b`,
    `block_access_lists.py:583-600`) — two-tier keyed membership.  The
    execution-specs `account_writes` map stores whole `Optional[Account]`
    values, while its `account_reads` touched-address set is separate
    (`state_tracker.py:69-70, 858-865`; `block_access_lists.py:695-697`).
    The guest's fixed row is therefore decoded by the producer contract below:

        if address in pre_tx_accounts:   # block-cumulative, prior txs only
            return pre_tx_accounts[address]   # may be None
        return pre_state.get_account_optional(address)

    Guest row encoding of that case split.  The row is a representation of the
    whole map entry, not the map's membership bit by itself: a row is a member
    iff its mask has at least one component other than TOUCHED (32).  The
    producer census for this criterion is recorded here because changing it is
    a semantic change, not a decoder cleanup:

      * STATE|EXEC_FLAGS|TOUCHED (56): `CreateFrameDescend` and
        `BlockVerdictCreationStage`;
      * NONCE|CODE|STATE|EXEC_FLAGS|TOUCHED (62): `TxIntrinsicStateGas`;
      * BALANCE|TOUCHED (33), NONCE|TOUCHED (34), or
        BALANCE|NONCE|TOUCHED (35): `NonstorageEffectLog`;
      * NONCE|TOUCHED (34): `BlockVerdictMtxRuntime`;
      * TOUCHED-only (32): `CreateCodeEffectLog`, the pure-touch case.

      For a row with a value-bearing component:
      * STATE valid + `optionalState@72 = 0` → None (zeros); ⛔ do NOT fall
        through to parent (would resurrect a deleted account);
      * STATE valid + nonzero `optionalState@72` → present, but **not** an
        atomic whole Account: producers may publish STATE|CODE|EXEC_FLAGS
        without BALANCE or NONCE (for example, EIP-7702 authorization).  Start
        from the authenticated parent (or zero if it is absent), then overlay
        the row's valid BALANCE and NONCE components;
      * without STATE → use the same parent-fill and BALANCE/NONCE overlay.
        CODE and EXEC_FLAGS still make the row a map member, although this
        resolver's scalar output has no code/flag fields to overlay.  STATE is
        therefore an existence bit, not evidence that the fixed row contains
        every Account field.

      A TOUCHED-only row (mask 32) is not a `pre_tx_accounts` entry and falls
      through to the parent exactly as for a missing key; it is not a recorded
      `None`.  This bridges the guest's fieldwise producer rows to the
      execution-specs whole-`Optional[Account]` map.

    The block map is prior-tx only by construction: its sole writer is
    `account_writes_block_upsert` via `account_writes_incorporate_tx` after a
    tx finishes (`state_tracker.py:864-865`). Current-tx writes live in
    `TX_ACCOUNT_WRITES_AREA` and must not be folded in here (false-accept).

    a0 = canonical address (20 B), a1 = output account scratch (nonce@0,
    balance@8), a2/a3 = parent header RLP ptr/len, a4/a5 = witness ptr/len.
    Returns a0 = 0 on a resolved account (including authenticated absence /
    Present-None, represented as zero nonce/balance), or 1 on malformed
    lookup/error.

    The hybrid membership/overlay path is 118 instructions.  This is an
    intentional emitted-layout change from the 111-instruction predecessor;
    downstream GuestAddrs and RegionMap pins must be regenerated from the final
    linked image rather than hand-maintained.

    A STATE-valid row with nonzero optionalState is copied through the fixed
    account-row layout.  The source balance begins at row +32; optionalState at
    row +72 is only the presence discriminator and is never an output balance.
    The four-byte slot formerly occupied by the skip is reused for that first
    balance load, so the symbol keeps its 118-instruction shape. -/
def accountResolvePreState_prog : Program :=
  [ .ADDI .x2 .x2 (-208 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .SD .x9 .x0 (0 : BitVec 12),
    .SD .x9 .x0 (8 : BitVec 12),
    .SD .x9 .x0 (16 : BitVec 12),
    .SD .x9 .x0 (24 : BitVec 12),
    .SD .x9 .x0 (32 : BitVec 12),
    .LI .x23 (0 : Word),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_resolve_pre_state + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_resolve_pre_state + 92)),
    .LD .x6 .x5 (0 : BitVec 12),
    -- The block-tier writer uses ACCOUNT_WRITES_AREA.  Derive the scan base
    -- from that layout constant instead of reconstructing the stale
    -- 0xbdb80000 address, while retaining the three-instruction shape so the
    -- resolver's linked offsets remain stable.
    .LUI .x7 (((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) : BitVec 20),
    .ADDIW .x7 .x7 (((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) : BitVec 12),
    .SLLI .x7 .x7 (12 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_resolve_pre_state + 256) (GuestAddrs.account_resolve_pre_state + 120)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .LI .x31 (20 : Word),
    .MV .x10 .x30,
    .MV .x11 .x8,
    .BEQ .x31 .x0 (40 : BitVec 13),
    .LBU .x12 .x10 (0 : BitVec 12),
    .LBU .x13 .x11 (0 : BitVec 12),
    .BNE .x12 .x13 (20 : BitVec 13),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .MV .x22 .x30,
    .LD .x5 .x22 (112 : BitVec 12),
    .MV .x23 .x5,
    .ANDI .x6 .x5 (8 : BitVec 12),
    .BEQ .x6 .x0 (56 : BitVec 13),
    .LD .x6 .x22 (72 : BitVec 12),
    .BEQ .x6 .x0 (brOff (GuestAddrs.account_resolve_pre_state + 412) (GuestAddrs.account_resolve_pre_state + 208)),
    -- A nonzero STATE presence marker does not make the row an atomic Account:
    -- STATE|CODE|EXEC_FLAGS rows may omit BALANCE/NONCE.  Reuse the existing
    -- authenticated parent-fill path, then overlay only the row's valid bits.
    .JAL .x0 (jalOff (GuestAddrs.account_resolve_pre_state + 256)
      (GuestAddrs.account_resolve_pre_state + 212)),
    .SD .x9 .x6 (8 : BitVec 12),
    .LD .x6 .x22 (40 : BitVec 12),
    .SD .x9 .x6 (16 : BitVec 12),
    .LD .x6 .x22 (48 : BitVec 12),
    .SD .x9 .x6 (24 : BitVec 12),
    .LD .x6 .x22 (56 : BitVec 12),
    .SD .x9 .x6 (32 : BitVec 12),
    .LD .x6 .x22 (64 : BitVec 12),
    .SD .x9 .x6 (0 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_resolve_pre_state + 404) (GuestAddrs.account_resolve_pre_state + 252)),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .MV .x12 .x8,
    .LI .x13 (20 : Word),
    .MV .x14 .x20,
    .MV .x15 .x21,
    .ADDI .x16 .x2 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_at_header_state_root_tracked (GuestAddrs.account_resolve_pre_state + 284)),
    .LI .x5 (1 : Word),
    .BLTU .x5 .x10 (brOff (GuestAddrs.account_resolve_pre_state + 420) (GuestAddrs.account_resolve_pre_state + 292)),
    .BEQ .x10 .x0 (8 : BitVec 13),
    .JAL .x0 (48 : BitVec 21),
    .ADDI .x5 .x2 (96 : BitVec 12),
    .LD .x6 .x5 (8 : BitVec 12),
    .SD .x9 .x6 (8 : BitVec 12),
    .LD .x6 .x5 (16 : BitVec 12),
    .SD .x9 .x6 (16 : BitVec 12),
    .LD .x6 .x5 (24 : BitVec 12),
    .SD .x9 .x6 (24 : BitVec 12),
    .LD .x6 .x5 (32 : BitVec 12),
    .SD .x9 .x6 (32 : BitVec 12),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x9 .x6 (0 : BitVec 12),
    .ANDI .x6 .x23 (1 : BitVec 12),
    .BEQ .x6 .x0 (36 : BitVec 13),
    .LD .x6 .x22 (32 : BitVec 12),
    .SD .x9 .x6 (8 : BitVec 12),
    .LD .x6 .x22 (40 : BitVec 12),
    .SD .x9 .x6 (16 : BitVec 12),
    .LD .x6 .x22 (48 : BitVec 12),
    .SD .x9 .x6 (24 : BitVec 12),
    .LD .x6 .x22 (56 : BitVec 12),
    .SD .x9 .x6 (32 : BitVec 12),
    .ANDI .x6 .x23 (2 : BitVec 12),
    .BEQ .x6 .x0 (12 : BitVec 13),
    .LD .x6 .x22 (64 : BitVec 12),
    .SD .x9 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .ADDI .x2 .x2 (208 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountResolvePreState_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountResolvePreState_relocs : RelocTable :=
  [ (23, .la .x5 "account_writes_count"),
    (71, .jal .x1 "account_at_header_state_root_tracked") ]

def accountResolvePreStateFunction : String :=
  "account_resolve_pre_state:\n" ++ emitProgramR accountResolvePreState_prog accountResolvePreState_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountResolvePreState_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountResolvePreStateFunction_eq_prog :
    accountResolvePreStateFunction = "account_resolve_pre_state:\n" ++ emitProgramR accountResolvePreState_prog accountResolvePreState_relocs := rfl

#guard accountResolvePreStateFunction.startsWith "account_resolve_pre_state:\n"
#guard accountResolvePreState_prog.length = 118

-- Encoding preconditions for the derived ACCOUNT_WRITES_AREA base above:
-- page alignment, a representable positive LUI construction, and an ADDIW
-- immediate whose sign bit is clear.  These guard the encoding assumptions,
-- not the resolver's runtime result.
#guard EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat % 4096 = 0
#guard EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 43 = 0
#guard (EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096 < 2048
#guard (((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) <<< 12 + (EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) <<< 12 = EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat
/-! ## `account_resolve_execution_state`

    Resolve an execution-time account with the three-tier precedence from
    `state_tracker.py:get_account_optional` (pinned `e5a8caf1b`, lines
    179-203): transaction writes, then the block-cumulative map, then the
    authenticated parent state.  This is deliberately a separate symbol from
    `account_resolve_pre_state`.  The latter implements
    `block_access_lists.py:_get_pre_tx_account` and is called by the BAL builder
    while it is walking `tx_account_writes`; letting that helper see the tx map
    would make the builder compare each row against itself and accept a missing
    BAL entry.

    The resolver records the address before walking its tiers, matching
    Amsterdam's `get_account_optional`; CREATE is the current sole consumer.
    The ABI is:

      a0 = canonical address (20-byte BE)
      a1 = output scratch: nonce@0, balance@8..40, code_ptr@40,
           code_len@48, present@56
      a2/a3 = parent header RLP pointer/length
      a4/a5 = witness.state pointer/length
      a6/a7 = witness.codes pointer/length

    The return is resolver-local state, not an `account_at_header_state_root`
    parser status: 0 absent, 1 live code, 2 present-but-empty, 3 deleted, and
    4 resolver-unavailable (a non-empty code hash missing from witness.codes).
    Status 4 means a valid authenticated account lacks a witness.codes
    preimage: a block may be valid, so a caller's rejection is a false reject
    (FR) caused by witness incompleteness.  A malformed authenticated lookup
    uses 5: that is malformed proof/input evidence, so its rejection is a
    genuine reject rather than a witness-shortfall bail.  Keeping 4 and 5 separate is
    therefore part of the ABI.  A map code row is authoritative and its pointer/length
    is preserved.  Otherwise
    the authenticated account's code_hash is resolved with the RAW
    `witness_codes_lookup_by_hash` helper, never `code_read_fetch`: this path
    materialises state and must not record a code read or alter witness-code
    selection.  Account absence and EMPTY_CODE_HASH are truthful zero-length
    code; a non-empty hash miss is never fabricated as empty.

    EIP-7702 designators are preserved and followed by the existing dispatch
    path, never executed as bytecode.  Marker recognition is by the `ef 01 00`
    prefix after a three-byte length check, not by assuming every 23-byte code
    blob is a marker.  Storage root remains out of scope: the storage path
    derives it with `mpt_bounded_storage_root` (#11385). -/
def accountResolveExecutionState_prog : Program :=
  [ .ADDI .x2 .x2 (-208 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .MV .x23 .x17,
    .LI .x24 (0 : Word),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.account_read_record (GuestAddrs.account_resolve_execution_state + 84)),
    .SD .x9 .x0 (0 : BitVec 12),
    .SD .x9 .x0 (8 : BitVec 12),
    .SD .x9 .x0 (16 : BitVec 12),
    .SD .x9 .x0 (24 : BitVec 12),
    .SD .x9 .x0 (32 : BitVec 12),
    .SD .x9 .x0 (40 : BitVec 12),
    .SD .x9 .x0 (48 : BitVec 12),
    .SD .x9 .x0 (56 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_resolve_execution_state + 120)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_resolve_execution_state + 120)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (2031 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_resolve_execution_state + 340) (GuestAddrs.account_resolve_execution_state + 148)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .LI .x31 (20 : Word),
    .MV .x10 .x30,
    .MV .x11 .x8,
    .BEQ .x31 .x0 (40 : BitVec 13),
    .LBU .x12 .x10 (0 : BitVec 12),
    .LBU .x13 .x11 (0 : BitVec 12),
    .BNE .x12 .x13 (20 : BitVec 13),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .MV .x31 .x30,
    .LD .x5 .x31 (112 : BitVec 12),
    .ANDI .x6 .x5 (1 : BitVec 12),
    .BEQ .x6 .x0 (40 : BitVec 13),
    .LD .x6 .x31 (32 : BitVec 12),
    .SD .x9 .x6 (8 : BitVec 12),
    .LD .x6 .x31 (40 : BitVec 12),
    .SD .x9 .x6 (16 : BitVec 12),
    .LD .x6 .x31 (48 : BitVec 12),
    .SD .x9 .x6 (24 : BitVec 12),
    .LD .x6 .x31 (56 : BitVec 12),
    .SD .x9 .x6 (32 : BitVec 12),
    .ORI .x24 .x24 (1 : BitVec 12),
    .ANDI .x6 .x5 (2 : BitVec 12),
    .BEQ .x6 .x0 (16 : BitVec 13),
    .LD .x6 .x31 (64 : BitVec 12),
    .SD .x9 .x6 (0 : BitVec 12),
    .ORI .x24 .x24 (2 : BitVec 12),
    .ANDI .x6 .x5 (4 : BitVec 12),
    .BEQ .x6 .x0 (32 : BitVec 13),
    .LD .x6 .x31 (80 : BitVec 12),
    .SD .x9 .x6 (40 : BitVec 12),
    .LD .x6 .x31 (88 : BitVec 12),
    .SD .x9 .x6 (48 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x9 .x6 (56 : BitVec 12),
    .ORI .x24 .x24 (4 : BitVec 12),
    .ANDI .x6 .x5 (8 : BitVec 12),
    .BEQ .x6 .x0 (16 : BitVec 13),
    .LD .x6 .x31 (72 : BitVec 12),
    .SD .x9 .x6 (56 : BitVec 12),
    .ORI .x24 .x24 (8 : BitVec 12),
    .ANDI .x5 .x24 (8 : BitVec 12),
    .BEQ .x5 .x0 (12 : BitVec 13),
    .LD .x6 .x9 (56 : BitVec 12),
    .BEQ .x6 .x0 (brOff (GuestAddrs.account_resolve_execution_state + 1024) (GuestAddrs.account_resolve_execution_state + 352)),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_resolve_execution_state + 356)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_resolve_execution_state + 356)),
    .LD .x6 .x5 (0 : BitVec 12),
    -- The block-tier writer uses ACCOUNT_WRITES_AREA.  Reuse the same
    -- symbolic, page-aligned derivation as the pre-state resolver above;
    -- the shared encoding guards immediately above prove its assumptions.
    .LUI .x7 (((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) : BitVec 20),
    .ADDIW .x7 .x7 (((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) : BitVec 12),
    .SLLI .x7 .x7 (12 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_resolve_execution_state + 528) (GuestAddrs.account_resolve_execution_state + 384)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .LI .x31 (20 : Word),
    .MV .x10 .x30,
    .MV .x11 .x8,
    .BEQ .x31 .x0 (40 : BitVec 13),
    .LBU .x12 .x10 (0 : BitVec 12),
    .LBU .x13 .x11 (0 : BitVec 12),
    .BNE .x12 .x13 (20 : BitVec 13),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .MV .x31 .x30,
    .LD .x5 .x31 (112 : BitVec 12),
    .ANDI .x6 .x24 (4 : BitVec 12),
    .BNE .x6 .x0 (40 : BitVec 13),
    .ANDI .x6 .x5 (4 : BitVec 12),
    .BEQ .x6 .x0 (32 : BitVec 13),
    .LD .x6 .x31 (80 : BitVec 12),
    .SD .x9 .x6 (40 : BitVec 12),
    .LD .x6 .x31 (88 : BitVec 12),
    .SD .x9 .x6 (48 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x9 .x6 (56 : BitVec 12),
    .ORI .x24 .x24 (4 : BitVec 12),
    .ANDI .x6 .x24 (8 : BitVec 12),
    .BNE .x6 .x0 (24 : BitVec 13),
    .ANDI .x6 .x5 (8 : BitVec 12),
    .BEQ .x6 .x0 (16 : BitVec 13),
    .LD .x6 .x31 (72 : BitVec 12),
    .SD .x9 .x6 (56 : BitVec 12),
    .ORI .x24 .x24 (8 : BitVec 12),
    .ANDI .x5 .x24 (8 : BitVec 12),
    .BEQ .x5 .x0 (20 : BitVec 13),
    .LD .x6 .x9 (56 : BitVec 12),
    .BEQ .x6 .x0 (brOff (GuestAddrs.account_resolve_execution_state + 1024) (GuestAddrs.account_resolve_execution_state + 540)),
    .ANDI .x5 .x24 (4 : BitVec 12),
    .BNE .x5 .x0 (brOff (GuestAddrs.account_resolve_execution_state + 900) (GuestAddrs.account_resolve_execution_state + 548)),
    .MV .x10 .x8,
    .ADDI .x11 .x2 (96 : BitVec 12),
    .MV .x12 .x18,
    .MV .x13 .x19,
    .MV .x14 .x20,
    .MV .x15 .x21,
    .JAL .x1 (jalOff GuestAddrs.account_resolve_pre_state (GuestAddrs.account_resolve_execution_state + 576)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_resolve_execution_state + 1056) (GuestAddrs.account_resolve_execution_state + 580)),
    .ANDI .x5 .x24 (1 : BitVec 12),
    .BNE .x5 .x0 (44 : BitVec 13),
    .ADDI .x6 .x2 (96 : BitVec 12),
    .LD .x7 .x6 (8 : BitVec 12),
    .SD .x9 .x7 (8 : BitVec 12),
    .LD .x7 .x6 (16 : BitVec 12),
    .SD .x9 .x7 (16 : BitVec 12),
    .LD .x7 .x6 (24 : BitVec 12),
    .SD .x9 .x7 (24 : BitVec 12),
    .LD .x7 .x6 (32 : BitVec 12),
    .SD .x9 .x7 (32 : BitVec 12),
    .ORI .x24 .x24 (1 : BitVec 12),
    .ANDI .x5 .x24 (2 : BitVec 12),
    .BNE .x5 .x0 (20 : BitVec 13),
    .ADDI .x6 .x2 (96 : BitVec 12),
    .LD .x7 .x6 (0 : BitVec 12),
    .SD .x9 .x7 (0 : BitVec 12),
    .ORI .x24 .x24 (2 : BitVec 12),
    .ANDI .x5 .x24 (4 : BitVec 12),
    .BNE .x5 .x0 (brOff (GuestAddrs.account_resolve_execution_state + 900) (GuestAddrs.account_resolve_execution_state + 660)),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .MV .x12 .x8,
    .LI .x13 (20 : Word),
    .MV .x14 .x20,
    .MV .x15 .x21,
    .ADDI .x16 .x2 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_at_header_state_root_tracked (GuestAddrs.account_resolve_execution_state + 692)),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.account_resolve_execution_state + 992) (GuestAddrs.account_resolve_execution_state + 704)),
    .JAL .x0 (jalOff (GuestAddrs.account_resolve_execution_state + 1056) (GuestAddrs.account_resolve_execution_state + 708)),
    .ANDI .x5 .x24 (8 : BitVec 12),
    .BNE .x5 .x0 (60 : BitVec 13),
    .ADDI .x28 .x2 (96 : BitVec 12),
    .LD .x6 .x28 (0 : BitVec 12),
    .SD .x9 .x6 (0 : BitVec 12),
    .LD .x6 .x28 (8 : BitVec 12),
    .SD .x9 .x6 (8 : BitVec 12),
    .LD .x6 .x28 (16 : BitVec 12),
    .SD .x9 .x6 (16 : BitVec 12),
    .LD .x6 .x28 (24 : BitVec 12),
    .SD .x9 .x6 (24 : BitVec 12),
    .LD .x6 .x28 (32 : BitVec 12),
    .SD .x9 .x6 (32 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x9 .x6 (56 : BitVec 12),
    .ORI .x24 .x24 (3 : BitVec 12),
    .ADDI .x28 .x2 (96 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.chahsr_empty_code_hash (GuestAddrs.account_resolve_execution_state + 780)),
    .ADDI .x5 .x5 (laLo GuestAddrs.chahsr_empty_code_hash (GuestAddrs.account_resolve_execution_state + 780)),
    .LD .x6 .x28 (72 : BitVec 12),
    .LD .x7 .x5 (0 : BitVec 12),
    .BNE .x6 .x7 (44 : BitVec 13),
    .LD .x6 .x28 (80 : BitVec 12),
    .LD .x7 .x5 (8 : BitVec 12),
    .BNE .x6 .x7 (32 : BitVec 13),
    .LD .x6 .x28 (88 : BitVec 12),
    .LD .x7 .x5 (16 : BitVec 12),
    .BNE .x6 .x7 (20 : BitVec 13),
    .LD .x6 .x28 (96 : BitVec 12),
    .LD .x7 .x5 (24 : BitVec 12),
    .BNE .x6 .x7 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.account_resolve_execution_state + 976) (GuestAddrs.account_resolve_execution_state + 836)),
    .MV .x10 .x22,
    .MV .x11 .x23,
    .ADDI .x12 .x2 (168 : BitVec 12),
    .ADDI .x13 .x2 (80 : BitVec 12),
    .ADDI .x14 .x2 (88 : BitVec 12),
    .SD .x2 .x0 (80 : BitVec 12),
    .SD .x2 .x0 (88 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.witness_codes_lookup_by_hash (GuestAddrs.account_resolve_execution_state + 868)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_resolve_execution_state + 1040) (GuestAddrs.account_resolve_execution_state + 872)),
    .LD .x5 .x2 (80 : BitVec 12),
    .ADD .x5 .x22 .x5,
    .SD .x9 .x5 (40 : BitVec 12),
    .LD .x6 .x2 (88 : BitVec 12),
    .SD .x9 .x6 (48 : BitVec 12),
    .JAL .x0 (4 : BitVec 21),
    .LD .x5 .x9 (48 : BitVec 12),
    .LI .x6 (3 : Word),
    .BLTU .x5 .x6 (52 : BitVec 13),
    .LD .x5 .x9 (40 : BitVec 12),
    .LBU .x6 .x5 (0 : BitVec 12),
    .LI .x7 (239 : Word),
    .BNE .x6 .x7 (36 : BitVec 13),
    .LBU .x6 .x5 (1 : BitVec 12),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (24 : BitVec 13),
    .LBU .x6 .x5 (2 : BitVec 12),
    .BNE .x6 .x0 (16 : BitVec 13),
    .JAL .x0 (4 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.account_resolve_execution_state + 1068) (GuestAddrs.account_resolve_execution_state + 956)),
    .LD .x5 .x9 (48 : BitVec 12),
    .BEQ .x5 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.account_resolve_execution_state + 1068) (GuestAddrs.account_resolve_execution_state + 972)),
    .SD .x9 .x0 (40 : BitVec 12),
    .SD .x9 .x0 (48 : BitVec 12),
    .LI .x10 (2 : Word),
    .JAL .x0 (jalOff (GuestAddrs.account_resolve_execution_state + 1068) (GuestAddrs.account_resolve_execution_state + 988)),
    .ANDI .x5 .x24 (8 : BitVec 12),
    .BEQ .x5 .x0 (12 : BitVec 13),
    .LD .x6 .x9 (56 : BitVec 12),
    .BNE .x6 .x0 (-28 : BitVec 13),
    .SD .x9 .x0 (40 : BitVec 12),
    .SD .x9 .x0 (48 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (48 : BitVec 21),
    .SD .x9 .x0 (40 : BitVec 12),
    .SD .x9 .x0 (48 : BitVec 12),
    .LI .x10 (3 : Word),
    .JAL .x0 (32 : BitVec 21),
    .SD .x9 .x0 (40 : BitVec 12),
    .SD .x9 .x0 (48 : BitVec 12),
    .LI .x10 (4 : Word),
    .JAL .x0 (16 : BitVec 21),
    .SD .x9 .x0 (40 : BitVec 12),
    .SD .x9 .x0 (48 : BitVec 12),
    .LI .x10 (5 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .ADDI .x2 .x2 (208 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountResolveExecutionState_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountResolveExecutionState_relocs : RelocTable :=
  [ (21, .jal .x1 "account_read_record"),
    (30, .la .x5 "tx_account_writes_count"),
    (89, .la .x5 "account_writes_count"),
    (144, .jal .x1 "account_resolve_pre_state"),
    (173, .jal .x1 "account_at_header_state_root_tracked"),
    (195, .la .x5 "chahsr_empty_code_hash"),
    (217, .jal .x1 "witness_codes_lookup_by_hash") ]

def accountResolveExecutionStateFunction : String :=
  "account_resolve_execution_state:\n" ++ emitProgramR accountResolveExecutionState_prog accountResolveExecutionState_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountResolveExecutionState_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountResolveExecutionStateFunction_eq_prog :
    accountResolveExecutionStateFunction = "account_resolve_execution_state:\n" ++ emitProgramR accountResolveExecutionState_prog accountResolveExecutionState_relocs := rfl

#guard accountResolveExecutionStateFunction.startsWith "account_resolve_execution_state:\n"
#guard accountResolveExecutionState_prog.length = 279
end EvmAsm.Codegen
