/-
  EvmAsm.Codegen.Programs.Storage

  M24 Option A storage handlers (SLOAD, SSTORE, TLOAD, TSTORE).
  Supersedes M22's `(slotKey, value)` 64-byte-entry slot-table
  approach with the Option A spec from issue #7130: a 128-byte
  per-entry append-only log keyed by `(addrHash, slotKey)` with
  separate `original` and `current` value cells.

  Two logs live in `STATE_TRACKER_AREA`:
    0xa0630000  persistent storage log (SLOAD / SSTORE)
    0xa0830000  transient  storage log (TLOAD / TSTORE)

  Each entry is 128 bytes, 8-byte aligned:
    +0..32   addrHash   (the executing frame's env.ADDRESS (env+0) — per-contract
                          keying so a nested callee's slots are isolated from the
                          caller's. Both the persistent (SLOAD/SSTORE) and the
                          transient (TLOAD/TSTORE) logs key on it.)
    +32..64  slotKey    (EVM-stack byte order: 4 LE u64 limbs, low first)
    +64..96  original   (slot's pre-tx value; 0 for cold non-preloaded)
    +96..128 current    (most recent committed value during this tx)

  Log lengths live in env:
    env+448  persistentLogLengthOff  (live counter; SSTORE increments)
    env+456  persistentLogCheckpointOff  (set at prologue end; restored on REVERT)
    env+464  transientLogLengthOff  (live counter; TSTORE increments; reset on REVERT)

  ## Semantics

  **SLOAD (0x54)** — scan persistent log from end (last-write-
  wins); copy matching `current` to the stack-top slot. On a MISS,
  resolve the value on demand (GH #10874: block-committed map, then the
  witness by key, then zero) and SEED it into the log so the verified
  scan finds it. Net stack delta = 0.

  **SSTORE (0x55)** — scan from end; append a new entry preserving
  the prior `original` on match (or 0 on miss). **Always appends**
  (never mutates existing entries) — this is what makes REVERT a
  single log-length truncation instead of a journal replay.
  Net stack delta = +64 (pops key + value).

  **TLOAD (0x5c)** — same shape as SLOAD against the transient log.

  **TSTORE (0x5d)** — append-only (no scan; transient storage has
  no gas refund logic, so we never need to read the prior
  `original`). Net stack delta = +64.

  ## Inline asm conventions

  Numeric local labels (`1:`, `1b`, `1f`, …) — unique-per-use,
  reusable across handlers without collision. Scratch registers
  x14–x19 are caller-saved per the dispatcher convention.

  ## Known limitations (documented in CODEGEN.md M24)

  - Persistent SLOAD/SSTORE and transient TLOAD/TSTORE key on the frame's
    env.ADDRESS (multi-contract isolated).
  - GH #10874: cold reads are DEMAND-DRIVEN. A persistent-log miss is resolved
    through the three-tier chain (`storagePrestateResolveAsm`): the block-committed
    map, then the witness BY KEY against the parent header, then zero. It used to
    read `original = 0` unconditionally, which made a slot readable only if
    something had PRELOADED it from the declared BAL.
  - 4 MiB per log = ~32K entries each — well past any test workload.
  - Inline asm, not verified bodies. Verified-loop bodies follow later.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Stateless.SpecRef.Gas
import EvmAsm.Codegen.Programs.StaticContext
import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Evm64.Transient.StoreProgram
import EvmAsm.Evm64.Transient.LoadProgram
import EvmAsm.Evm64.Storage.LoadProgram

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Additional SSTORE gas after the dispatcher warm floor and storage-access
    helper have run.

    Inputs:
    - `x12`: stack pointer. `[x12+0..32]` is key, `[x12+32..64]` is new value.
    - `x18`: pointer to found log entry's original value (`entry+64`), or zero.
    - `x19`: storage-access status (`0` warm, `1` cold).

    Clobbers `x5`, `x6`, `x9`, `x14`-`x17`. Jumps to `.exit_outofgas` if the
    additional debit cannot be paid. The static dispatch table already charged
    100 gas for SSTORE, and `evm_storage_access_charge_key` already charged the
    2900 cold delta, so this computes the remaining debit to match Amsterdam's
    `vm/instructions/storage.py`:

    - clean-changing (original == current ≠ new): +10000 STORAGE_WRITE; when

      the original is zero this is a state CREATION, so it additionally charges
      the EIP-8037 state gas STATE_BYTES_PER_STORAGE_SET(64) ×
      COST_PER_STATE_BYTE(1530) = 97,920 via the charge_state_gas rule: drain
      `evm_state_gas_left` first, spill the remainder into env.gasRemaining,
      OOG when both are short; `evm_state_gas_used` accumulates the charge.

    - dirty/noop branch: +0; the access charge is already fully covered by the
      dispatch warm floor plus storage-access helper.

    Refund-counter updates are handled by `sstore_gas_refund_outcome` below. -/
def sstoreValueTransitionGasAsm : String :=
  -- x14 = OR of the new value limbs. For a missing slot, original=current=0.
  "  mv x14, x0\n" ++
  "  ld x15, 32(x12)\n" ++
  "  or x14, x14, x15\n" ++
  "  ld x15, 40(x12)\n" ++
  "  or x14, x14, x15\n" ++
  "  ld x15, 48(x12)\n" ++
  "  or x14, x14, x15\n" ++
  "  ld x15, 56(x12)\n" ++
  "  or x14, x14, x15\n" ++
  "  beqz x18, .Lsstore_missing_slot\n" ++
  -- Found slot: x15 = original_or, x16 = original/current diff,
  -- x17 = current/new diff.
  "  mv x15, x0\n" ++
  "  mv x16, x0\n" ++
  "  mv x17, x0\n" ++
  "  ld x5, 0(x18)\n" ++
  "  or x15, x15, x5\n" ++
  "  ld x6, 32(x18)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x16, x16, x6\n" ++
  "  ld x5, 32(x18)\n" ++
  "  ld x6, 32(x12)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x17, x17, x6\n" ++
  "  ld x5, 8(x18)\n" ++
  "  or x15, x15, x5\n" ++
  "  ld x6, 40(x18)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x16, x16, x6\n" ++
  "  ld x5, 40(x18)\n" ++
  "  ld x6, 40(x12)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x17, x17, x6\n" ++
  "  ld x5, 16(x18)\n" ++
  "  or x15, x15, x5\n" ++
  "  ld x6, 48(x18)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x16, x16, x6\n" ++
  "  ld x5, 48(x18)\n" ++
  "  ld x6, 48(x12)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x17, x17, x6\n" ++
  "  ld x5, 24(x18)\n" ++
  "  or x15, x15, x5\n" ++
  "  ld x6, 56(x18)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x16, x16, x6\n" ++
  "  ld x5, 56(x18)\n" ++
  "  ld x6, 56(x12)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x17, x17, x6\n" ++
  "  bnez x16, .Lsstore_dirty_or_noop\n" ++
  "  beqz x17, .Lsstore_dirty_or_noop\n" ++
  "  li x9, 0\n" ++                  -- x9 = needs_state_gas (zero-origin creation)
  "  bnez x15, .Lsstore_clean_changing\n" ++
  "  li x9, 1\n" ++
  ".Lsstore_clean_changing:\n" ++
  s!"  li x14, {EvmAsm.Stateless.SpecRef.GasCosts.STORAGE_WRITE}\n" ++
  "  j .Lsstore_charge_delta\n" ++
  ".Lsstore_missing_slot:\n" ++
  "  li x9, 0\n" ++
  "  bnez x14, .Lsstore_missing_nonzero\n" ++
  "  j .Lsstore_gas_done\n" ++
  ".Lsstore_missing_nonzero:\n" ++   -- missing slot = original = current = 0: creation
  "  li x9, 1\n" ++

  s!"  li x14, {EvmAsm.Stateless.SpecRef.GasCosts.STORAGE_WRITE}\n" ++

  "  j .Lsstore_charge_delta\n" ++
  ".Lsstore_dirty_or_noop:\n" ++
  "  li x9, 0\n" ++
  "  j .Lsstore_gas_done\n" ++
  ".Lsstore_charge_delta:\n" ++
  "  ld x15, 568(x20)\n" ++
  "  bltu x15, x14, .exit_outofgas\n" ++
  "  sub x15, x15, x14\n" ++
  "  sd x15, 568(x20)\n" ++
  -- EIP-8037 state gas for a zero-origin set (charge AFTER the regular debit so
  -- a regular-gas OOG never drains the reservoir, matching the spec's "charge
  -- regular gas before state gas" ordering in storage.py sstore).
  "  beqz x9, .Lsstore_gas_done\n" ++
  "  la x15, evm_state_gas_left\n" ++
  "  ld x16, 0(x15)\n" ++
  liStateGasRuntime "x14" 64 ++             -- STATE_BYTES_PER_STORAGE_SET(64) × COST_PER_STATE_BYTE(1530)
  "  bgeu x16, x14, .Lsstore_state_from_reservoir\n" ++
  "  sub x14, x14, x16\n" ++         -- spill = charge - reservoir
  "  ld x17, 568(x20)\n" ++
  "  bltu x17, x14, .exit_outofgas\n" ++
  "  sd x0, 0(x15)\n" ++
  "  sub x17, x17, x14\n" ++
  "  sd x17, 568(x20)\n" ++
  "  la x15, evm_state_gas_spilled\n" ++
  "  ld x16, 0(x15)\n" ++
  "  add x16, x16, x14\n" ++
  "  sd x16, 0(x15)\n" ++
  "  j .Lsstore_state_charged\n" ++
  ".Lsstore_state_from_reservoir:\n" ++
  "  sub x16, x16, x14\n" ++
  "  sd x16, 0(x15)\n" ++
  ".Lsstore_state_charged:\n" ++
  "  la x15, evm_state_gas_used\n" ++
  "  ld x16, 0(x15)\n" ++
  liStateGasRuntime "x14" 64 ++
  "  add x16, x16, x14\n" ++
  "  sd x16, 0(x15)\n" ++
  ".Lsstore_gas_done:\n"

/-- GH #10874: reverse scan of the persistent storage log for the executing
    frame's `(env.ADDRESS, stack key)`, setting `x18 = &found.original`
    (`entry+64`) or leaving it `0` on a miss.

    Extracted verbatim from `h_SSTORE`'s inline scan so `h_SLOAD` determines
    "absent from the log" the SAME way rather than by a second implementation.
    Numeric local labels (`1:`/`2:`/`3:`) are unique-per-use, so both
    instantiations coexist without a prefix parameter.

    Register convention -- identical at both sites, which is what makes this
    shareable at all: `x20` = env base (`env.ADDRESS` at `+0..32`, log length at
    `+448`), `x12` = stack pointer with the 32-byte slot key at `[x12+0..32]`.
    Clobbers `x14`-`x18`; falls through to `2:` in both the hit and miss case. -/
def storagePersistentLogFindAsm : String :=
  "  li x18, 0\n" ++                -- x18 = "found.original ptr" (0 = not found)
  "  ld x15, 448(x20)\n" ++         -- x15 = log_length
  "  beqz x15, 2f\n" ++             -- empty log → skip scan
  "  li x14, 0xa0630000\n" ++       -- x14 = log base
  "  slli x16, x15, 7\n" ++
  "  add x14, x14, x16\n" ++        -- x14 = past last entry
  "1:\n" ++                         -- scan loop iter
  "  addi x14, x14, -128\n" ++
  -- Per-frame addrHash compare: isolate this contract's slots.
  "  ld x16, 0(x14)\n" ++
  "  ld x17, 0(x20)\n" ++
  "  bne x16, x17, 3f\n" ++
  "  ld x16, 8(x14)\n" ++
  "  ld x17, 8(x20)\n" ++
  "  bne x16, x17, 3f\n" ++
  "  ld x16, 16(x14)\n" ++
  "  ld x17, 16(x20)\n" ++
  "  bne x16, x17, 3f\n" ++
  "  ld x16, 24(x14)\n" ++
  "  ld x17, 24(x20)\n" ++
  "  bne x16, x17, 3f\n" ++
  "  ld x16, 32(x14)\n" ++
  "  ld x17, 0(x12)\n" ++
  "  bne x16, x17, 3f\n" ++
  "  ld x16, 40(x14)\n" ++
  "  ld x17, 8(x12)\n" ++
  "  bne x16, x17, 3f\n" ++
  "  ld x16, 48(x14)\n" ++
  "  ld x17, 16(x12)\n" ++
  "  bne x16, x17, 3f\n" ++
  "  ld x16, 56(x14)\n" ++
  "  ld x17, 24(x12)\n" ++
  "  bne x16, x17, 3f\n" ++
  -- Match: x18 = &found.original (= x14 + 64)
  "  addi x18, x14, 64\n" ++
  "  j 2f\n" ++
  "3:\n" ++                         -- no match this entry — advance
  "  addi x15, x15, -1\n" ++
  "  bnez x15, 1b\n" ++
  "2:\n"

/-- GH #10874: resolve a persistent-log MISS to its authenticated pre-state
    value, in the THREE-TIER order execution-specs requires. Entered with
    `x18 = 0` (miss) or nonzero (hit, in which case it is a no-op); on success
    sets `x18` to a 64-byte `(original, current)` pair in LE-limb order.

    The tiers, and why the order is load-bearing:

    1. the per-tx persistent log — already decided by the caller's scan;
    2. `bv_mtx_committed_chunked_latest_value`, which is execution-specs'
       `BlockState.storage_writes`: a prior successful transaction's committed
       value is the next transaction's `original` AND `current` alike;
    3. `slot_at_header_state_root` against the PARENT header — the witness,
       read BY KEY on demand, matching `WitnessState.get_storage`;
    4. otherwise zero (an absent account or slot is implicitly zero).

    ⚠️ Skipping tier 2 and going straight to the witness would return the
    PRE-BLOCK value wherever a prior transaction in this block already wrote the
    slot. That is why `h_SLOAD` reuses this chain instead of calling
    `sload_at_header_state_root`, which resolves the witness tier ALONE.

    `p` prefixes the named labels so both handlers can instantiate it.
    `out` is a 64-byte scratch buffer, also used to stage the canonical
    big-endian address and key the witness lookup needs.

    Returns via `x18`; clobbers `x14`-`x17` and `a0`-`a7`. The caller must save
    `x1`/`x10`/`x12`/`x13`/`x19` around it (there are `jal`s inside). -/
def storagePrestateResolveAsm (p : String) (out : String) : String :=
  ".L" ++ p ++ "_prestate_normal:\n" ++
  -- A persistent-log miss is not necessarily an all-zero pre-state slot: an
  -- untouched nonzero slot need not occur in the BAL-derived seed set, yet the
  -- read still needs its authenticated value. Resolve the cold value from the
  -- block-committed map, then the parent-state witness, before falling back to
  -- zero. An absent account/slot or an unresolved witness preimage retains the
  -- existing cold-zero behavior.
  "  bnez x18, .L" ++ p ++ "_prestate_done\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd x1, 0(sp); sd x10, 8(sp); sd x12, 16(sp); sd x13, 24(sp); sd x19, 32(sp)\n" ++
  -- env.ADDRESS is the EVM little-endian stack-word representation;
  -- slot_at_header_state_root takes a canonical 20-byte big-endian address.
  "  la x15, " ++ out ++ "; sd zero, 0(x15); sd zero, 8(x15); sd zero, 16(x15); sd zero, 24(x15)\n" ++
  "  addi x14, x20, 19; la x15, " ++ out ++ "; li x16, 20\n" ++
  ".L" ++ p ++ "_prestate_addr_rev:\n" ++
  "  lbu x17, 0(x14); sb x17, 0(x15); addi x14, x14, -1; addi x15, x15, 1; addi x16, x16, -1; bnez x16, .L" ++ p ++ "_prestate_addr_rev\n" ++
  -- The stack key is likewise little-endian; use the adjacent scratch as the
  -- canonical big-endian lookup key.
  "  addi x14, x12, 31; la x15, " ++ out ++ "; addi x15, x15, 32; li x16, 32\n" ++
  ".L" ++ p ++ "_prestate_key_rev:\n" ++
  "  lbu x17, 0(x14); sb x17, 0(x15); addi x14, x14, -1; addi x15, x15, 1; addi x16, x16, -1; bnez x16, .L" ++ p ++ "_prestate_key_rev\n" ++
  -- Tier 2: the block-committed map (execution-specs' BlockState.storage_writes).
  "  la x14, sstore_committed_hit; sd zero, 0(x14)\n" ++
  "  la x14, bv_mtx_committed_chunk_count; ld a3, 0(x14); beqz a3, .L" ++ p ++ "_committed_done\n" ++
  "  mv a0, x20; la a1, " ++ out ++ "; addi a1, a1, 32\n" ++
  "  la a2, bv_mtx_committed_chunked; li a4, " ++ toString bvMtxCommittedChunkCapacity ++ "; la a5, sstore_committed_current; la a6, dtrc_recipkey; la a7, dtrc_slotkey_le\n" ++
  -- ⚠️ Pre-existing and deliberately PRESERVED: this leaves for `.exit_outofgas`
  -- with `sp` still 40 bytes low. Harmless because that exit terminates the
  -- frame, and kept verbatim so the extraction is byte-identical at the SSTORE
  -- site rather than "behaviour-neutral as far as I can tell".
  "  jal ra, bv_mtx_committed_chunked_latest_value\n" ++
  "  li x14, 2; beq a0, x14, .exit_outofgas\n" ++
  "  la x14, sstore_committed_hit; sd a0, 0(x14)\n" ++
  ".L" ++ p ++ "_committed_done:\n" ++
  "  la x14, sstore_committed_hit; ld x14, 0(x14); beqz x14, .L" ++ p ++ "_prestate_header\n" ++
  "  la x14, sstore_committed_current; la x15, " ++ out ++ "\n" ++
  "  ld x17, 0(x14); sd x17, 0(x15); sd x17, 32(x15); ld x17, 8(x14); sd x17, 8(x15); sd x17, 40(x15)\n" ++
  "  ld x17, 16(x14); sd x17, 16(x15); sd x17, 48(x15); ld x17, 24(x14); sd x17, 24(x15); sd x17, 56(x15)\n" ++
  "  la x18, " ++ out ++ "; j .L" ++ p ++ "_prestate_restore\n" ++
  -- Tier 3: the witness, BY KEY, against the parent header.
  ".L" ++ p ++ "_prestate_header:\n" ++
  "  ld a0, 576(x20); ld a1, 584(x20); la a2, " ++ out ++ "; addi a3, a2, 32\n" ++
  "  ld a4, 592(x20); ld a5, 600(x20); ld a6, 592(x20); ld a7, 600(x20)\n" ++
  "  jal ra, slot_at_header_state_root\n" ++
  "  beqz a0, .L" ++ p ++ "_prestate_found\n" ++
  "  j .L" ++ p ++ "_prestate_zero\n" ++
  ".L" ++ p ++ "_prestate_found:\n" ++
  -- sahsr_u256 is canonical big-endian. Materialize both original and current
  -- in the exec-log's little-endian-limb order in the pair buffer.
  "  la x14, sahsr_u256; la x15, " ++ out ++ "; addi x15, x15, 31; li x16, 32\n" ++
  ".L" ++ p ++ "_prestate_value_rev:\n" ++
  "  lbu x17, 0(x14); sb x17, 0(x15); addi x14, x14, 1; addi x15, x15, -1; addi x16, x16, -1; bnez x16, .L" ++ p ++ "_prestate_value_rev\n" ++
  "  la x15, " ++ out ++ "; ld x14, 0(x15); sd x14, 32(x15); ld x14, 8(x15); sd x14, 40(x15); ld x14, 16(x15); sd x14, 48(x15); ld x14, 24(x15); sd x14, 56(x15)\n" ++
  "  la x18, " ++ out ++ "\n" ++
  ".L" ++ p ++ "_prestate_zero:\n" ++
  ".L" ++ p ++ "_prestate_restore:\n" ++
  "  ld x1, 0(sp); ld x10, 8(sp); ld x12, 16(sp); ld x13, 24(sp); ld x19, 32(sp); addi sp, sp, 40\n" ++
  ".L" ++ p ++ "_prestate_done:\n"

/-- M24 Option A storage handlers. -/
def storageHandlers : List OpcodeHandlerSpec :=
  [ -- M24 real SLOAD. Scan persistent log from end (last-write-
    -- wins); copy matching current to stack top; default 0 on miss.
    { label   := "h_SLOAD"
    , opcodes := [0x54]
    , preBody :=
        stackUnderflowGuardAsm 1 ++ "\n" ++
        -- GH #10619: record the storage READ into the block-lifetime read
        -- container.  The spec records a read on both paths -- get_storage for
        -- SLOAD, and get_storage_original/get_storage for SSTORE -- and
        -- storage_reads survives rollback (state_tracker.py:90-93, :809-826),
        -- so this must NOT be conditional on the frame committing.
        -- EIP-7928's "a slot both read and written appears only in the
        -- changes list" is discharged where the spec discharges it: the BAL
        -- builder's dedup against storage_changes, not by suppressing this.
        "  addi sp, sp, -24\n" ++
        "  sd x1, 0(sp); sd x10, 8(sp); sd x11, 16(sp)\n" ++
        "  mv a0, x20\n" ++
        "  mv a1, x12\n" ++
        "  jal ra, storage_read_record\n" ++
        "  ld x1, 0(sp); ld x10, 8(sp); ld x11, 16(sp)\n" ++
        "  addi sp, sp, 24\n" ++
        -- EIP-2929 storage-key access gas. The dispatch table already
        -- charged SLOAD's 100 warm floor, so the helper only charges the
        -- 2900 cold delta on first touch. Preserve handler return address
        -- plus dispatcher PC / stack registers across the ABI a0/a1/a2 call.
        "  mv x17, x1\n" ++
        "  mv x18, x10\n" ++
        "  mv x19, x12\n" ++
        -- a0 = &env.ADDRESS (env+0): per-contract EIP-2929 access-list token, so
        -- the same slot in two contracts is tracked as two distinct cold keys
        -- (x20 = env base, preserved across the helper call). Matches the
        -- per-contract addrHash keying of the storage value log.
        "  mv a0, x20\n" ++
        "  mv a1, x12\n" ++
        "  addi a2, x20, 568\n" ++
        "  jal ra, evm_storage_access_charge_key\n" ++
        "  mv x14, a0\n" ++
        "  mv x1, x17\n" ++
        "  mv x10, x18\n" ++
        "  mv x12, x19\n" ++
        "  li x15, 2\n" ++
        "  beq x14, x15, .exit_outofgas\n" ++
        "  li x15, 3\n" ++
        "  beq x14, x15, .exit_outofgas\n" ++
        -- GH #10874: DEMAND-DRIVEN COLD READ. Until now an SLOAD of a slot absent
        -- from the persistent log returned 0 unconditionally, so the only way a
        -- predeploy or a nested callee could read its real storage was for
        -- something to have PRELOADED the slot first -- and the slot SET came from
        -- the declared BAL (`stage_predeploy_storage_preload`,
        -- `seed_callee_storage`). That is a BAL echo into readable state: what the
        -- oracle omitted, the guest could not read.
        --
        -- execution-specs has no slot enumerator and needs none.
        -- `WitnessState.get_storage` walks the witness node DB BY KEY and returns
        -- zero when the leaf is absent, so a demand-driven miss path IS the spec
        -- model. Resolve the miss here, through the SAME three-tier chain h_SSTORE
        -- already uses, then SEED the resolved value into the log so the verified
        -- scan core below finds it.
        --
        -- Seeding rather than patching the returned value is what keeps the
        -- verified body untouched: `evm_sload` is witnessed at tier `.conditional`
        -- and pinned byte-identical by the `#guard`, so the miss cannot be handled
        -- inside it. The seeded entry has original == current (no net change),
        -- exactly the shape `seed_callee_storage` already appends.
        storagePersistentLogFindAsm ++
        -- x11 = a1 is clobbered by the resolve chain's calls and is live here (the
        -- storage_read_record call above saves it for the same reason). The chain
        -- saves x1/x10/x12/x13/x19 itself.
        "  addi sp, sp, -8\n" ++
        "  sd x11, 0(sp)\n" ++
        storagePrestateResolveAsm "sload" "sstore_prestate_pair" ++
        "  ld x11, 0(sp); addi sp, sp, 8\n" ++
        "  beqz x18, .Lsload_seed_done\n" ++
        -- Capacity: 16384 entries of 128 B in [0xa0630000, 0xa0830000).
        -- ⚠️ Deliberately NOT h_SSTORE's `.exit_outofgas` halt. An SSTORE MUST
        -- append -- dropping a write corrupts state -- but a SLOAD seed is only a
        -- cache of an authenticated read, so on a full log we skip the seed and
        -- degrade to the previous cold-zero behavior instead of killing the block.
        "  ld x15, 448(x20)\n" ++
        "  li x14, 16384\n" ++
        "  bgeu x15, x14, .Lsload_seed_done\n" ++
        "  li x14, 0xa0630000\n" ++
        "  slli x16, x15, 7\n" ++
        "  add x14, x14, x16\n" ++          -- x14 = &new entry
        -- addrHash = env.ADDRESS (env+0..32), keyed exactly as the scan compares.
        "  ld x16, 0(x20); sd x16, 0(x14); ld x16, 8(x20); sd x16, 8(x14)\n" ++
        "  ld x16, 16(x20); sd x16, 16(x14); ld x16, 24(x20); sd x16, 24(x14)\n" ++
        -- slotKey = stack[0..32]
        "  ld x16, 0(x12); sd x16, 32(x14); ld x16, 8(x12); sd x16, 40(x14)\n" ++
        "  ld x16, 16(x12); sd x16, 48(x14); ld x16, 24(x12); sd x16, 56(x14)\n" ++
        -- original = pair[0..32], current = pair[32..64] (both LE-limb)
        "  ld x16, 0(x18); sd x16, 64(x14); ld x16, 8(x18); sd x16, 72(x14)\n" ++
        "  ld x16, 16(x18); sd x16, 80(x14); ld x16, 24(x18); sd x16, 88(x14)\n" ++
        "  ld x16, 32(x18); sd x16, 96(x14); ld x16, 40(x18); sd x16, 104(x14)\n" ++
        "  ld x16, 48(x18); sd x16, 112(x14); ld x16, 56(x18); sd x16, 120(x14)\n" ++
        "  addi x15, x15, 1; sd x15, 448(x20)\n" ++
        ".Lsload_seed_done:\n"
      -- Verified reverse-scan core (byte-identical re-encoding of the former
      -- inline label-based scan on the persistent log; see the `#guard` pin
      -- below). Witnessed at tier `.conditional` by
      -- `EvmAsm.Evm64.Storage.evm_sload_stack_spec_within`.
    , body    := EvmAsm.Evm64.Storage.evm_sload .x20
    , tail    := .advanceAndRet 1 }
  , -- M24 real SSTORE. Scan persistent log from end; if found, save
    -- &found.original for the append step. Then ALWAYS append a new
    -- 128-byte entry at log[log_length] with (addrHash=0,
    -- slotKey=stack[0..32], original=found_or_zero,
    -- current=stack[32..64]). Increment log_length. Body's
    -- `ADDI x12, x12, 64` does the net -2 stack pop.
    --
    -- Append-only is load-bearing: REVERT rolls back via log-length
    -- truncation, which requires existing entries to be immutable.
    { label   := "h_SSTORE"
    , opcodes := [0x55]
    , preBody :=
        stackUnderflowGuardAsm 2 ++ "\n" ++
        staticContextWriteGuardAsm ++
        -- Amsterdam SSTORE stipend guard: `check_gas(evm, CALL_STIPEND + 1)`
        -- (storage.py) fails the op when gas_left < 2301 at instruction entry,
        -- WITHOUT charging. The dispatch loop already deducted the 100 static
        -- floor, so the equivalent post-deduction threshold here is 2201.
        "  ld x14, 568(x20)\n" ++
        "  li x15, 2201\n" ++
        "  bltu x14, x15, .exit_outofgas\n" ++
        -- Placed AFTER the stipend guard on purpose: storage.py runs
        -- `check_gas(evm, CALL_STIPEND + 1)` BEFORE `get_storage_original`, so an
        -- SSTORE that fails it records NO read in the spec.  Recording first
        -- would invent a read the spec never makes.
        -- GH #10619: record the storage READ into the block-lifetime read
        -- container.  The spec records a read on both paths -- get_storage for
        -- SLOAD, and get_storage_original/get_storage for SSTORE -- and
        -- storage_reads survives rollback (state_tracker.py:90-93, :809-826),
        -- so this must NOT be conditional on the frame committing.
        -- EIP-7928's "a slot both read and written appears only in the
        -- changes list" is discharged where the spec discharges it: the BAL
        -- builder's dedup against storage_changes, not by suppressing this.
        "  addi sp, sp, -24\n" ++
        "  sd x1, 0(sp); sd x10, 8(sp); sd x11, 16(sp)\n" ++
        "  mv a0, x20\n" ++
        "  mv a1, x12\n" ++
        "  jal ra, storage_read_record\n" ++
        "  ld x1, 0(sp); ld x10, 8(sp); ld x11, 16(sp)\n" ++
        "  addi sp, sp, 24\n" ++
        -- EIP-2929 storage-key access gas. The dispatch table already
        -- charged SSTORE's 100 warm floor, so this helper only charges
        -- the 2900 cold delta on first key touch. Run before the scan /
        -- append path so out-of-gas cannot mutate the storage log.
        "  mv x17, x1\n" ++
        "  mv x18, x10\n" ++
        "  mv x19, x12\n" ++
        -- a0 = &env.ADDRESS (env+0): per-contract EIP-2929 access-list token, so
        -- the same slot in two contracts is tracked as two distinct cold keys
        -- (x20 = env base, preserved across the helper call). Matches the
        -- per-contract addrHash keying of the storage value log.
        "  mv a0, x20\n" ++
        "  mv a1, x12\n" ++
        "  addi a2, x20, 568\n" ++
        "  jal ra, evm_storage_access_charge_key\n" ++
        "  mv x14, a0\n" ++
        "  mv x1, x17\n" ++
        "  mv x10, x18\n" ++
        "  mv x12, x19\n" ++
        "  li x15, 2\n" ++
        "  beq x14, x15, .exit_outofgas\n" ++
        "  li x15, 3\n" ++
        "  beq x14, x15, .exit_outofgas\n" ++
        "  mv x19, x14\n" ++            -- x19 = access status (0 warm, 1 cold)
        -- execution-specs gives fresh-created accounts a transaction-local
        -- zero *original* view. `get_storage` still observes a prior write in
        -- this transaction, so a matching log row must remain visible for the
        -- current half of a later SSTORE. `create_frame_flag` alone is too broad:
        -- it describes a depth, while helper/refund activity at that depth can
        -- address another account. Require the current env.ADDRESS (LE) to be
        -- exactly this depth's CREATE address (BE) before taking the zero arm.
        "  la x14, sstore_created_original_zero; sd zero, 0(x14)\n" ++
        "  la x14, evm_call_depth; ld x14, 0(x14)\n" ++
        "  slli x15, x14, 3; la x16, create_frame_flag; add x16, x16, x15; ld x16, 0(x16)\n" ++
        "  beqz x16, .Lsstore_created_original_scan\n" ++
        "  slli x15, x14, 5; la x16, create_address_by_depth; add x16, x16, x15\n" ++
        "  addi x17, x20, 19; li x15, 20\n" ++
        ".Lsstore_created_addr_cmp:\n" ++
        "  beqz x15, .Lsstore_created_original_zero\n" ++
        "  lbu x14, 0(x17); lbu x18, 0(x16); bne x14, x18, .Lsstore_created_original_scan\n" ++
        "  addi x17, x17, -1; addi x16, x16, 1; addi x15, x15, -1; j .Lsstore_created_addr_cmp\n" ++
        ".Lsstore_created_original_zero:\n" ++
        -- Preserve original=0, but keep scanning so a later write sees the
        -- current value established by an earlier same-transaction write.
        "  li x14, 1; la x16, sstore_created_original_zero; sd x14, 0(x16); j .Lsstore_created_original_scan\n" ++
        ".Lsstore_created_original_scan:\n" ++
        -- GH #10874: shared with h_SLOAD's miss determination (see
        -- `storagePersistentLogFindAsm`). Falls through to the append step at `2:`.
        storagePersistentLogFindAsm ++
        -- `created_accounts` changes only get_storage_original. When this
        -- exact created account already has a log row, synthesize
        -- {original = 0, current = row.current}; a first touch retains {0,0}.
        "  la x14, sstore_created_original_zero; ld x14, 0(x14); beqz x14, .Lsstore_prestate_normal\n" ++
        "  beqz x18, .Lsstore_created_original_done\n" ++
        "  la x14, sstore_prestate_pair; sd zero, 0(x14); sd zero, 8(x14); sd zero, 16(x14); sd zero, 24(x14)\n" ++
        "  ld x15, 32(x18); sd x15, 32(x14); ld x15, 40(x18); sd x15, 40(x14); ld x15, 48(x18); sd x15, 48(x14); ld x15, 56(x18); sd x15, 56(x14)\n" ++
        "  la x18, sstore_prestate_pair; j .Lsstore_created_original_done\n" ++
        -- GH #10874: shared three-tier cold resolution, now also used by h_SLOAD
        -- (see `storagePrestateResolveAsm`). SSTORE needs the authenticated
        -- original/current for Amsterdam state-gas classification.
        storagePrestateResolveAsm "sstore" "sstore_prestate_pair" ++
        ".Lsstore_created_original_done:\n" ++
        -- The persistent exec-log arena is [0xa0630000, 0xa0830000), i.e.
        -- 16384 entries of 128 bytes. Never append past it into the
        -- transient-log region; halt conservatively before any append-path
        -- gas/refund bookkeeping mutates state.
        "  ld x15, 448(x20)\n" ++
        "  li x14, 16384\n" ++
        "  bgeu x15, x14, .exit_outofgas\n" ++
        sstoreValueTransitionGasAsm ++
        -- bmvmx.1.6.3: accumulate this SSTORE's EIP-3529 refund delta into evm_refund_acc
        -- (signed). x18 = &found.original (or 0 -> original==current==0). sstore_gas_refund_outcome
        -- clobbers a0-a4 (= x10/x12/x13/...) + ra, so save the dispatcher regs x10/x12/x13 + x1.
        -- Keep x18 (&found.original) stable across the local zero-restore state-gas refund path too.
        "  addi sp, sp, -48\n" ++
        "  sd x1, 0(sp); sd x10, 8(sp); sd x12, 16(sp); sd x13, 24(sp); sd x18, 32(sp)\n" ++
        "  beqz x18, 8f\n" ++
        "  mv a0, x18; addi a1, x18, 32\n" ++          -- original = entry+64, current = entry+96
        "  j 9f\n" ++
        "8:\n" ++
        "  la a0, srfd_zero; la a1, srfd_zero\n" ++    -- missing slot: original = current = 0
        "9:\n" ++
        "  addi a2, x12, 32\n" ++                      -- new = stack[32..64]
        "  seqz a3, x19\n" ++                          -- warm flag (1 if x19 == 0 warm)
        "  la a4, srfd_out\n" ++
        "  jal ra, sstore_gas_refund_outcome\n" ++
        "  la x14, srfd_out; ld x15, 8(x14)\n" ++      -- signed refund delta
        "  la x14, evm_refund_acc; ld x16, 0(x14); add x16, x16, x15; sd x16, 0(x14)\n" ++
        -- EIP-8037 zero-restore credit (storage.py: original == new == 0 with a
        -- change → credit_state_gas_refund(STATE_BYTES_PER_STORAGE_SET ×
        -- COST_PER_STATE_BYTE)): apply min(97920, evm_state_gas_used) back into
        -- evm_state_gas_left. The cross-frame `state_gas_refund_pending`
        -- remainder is dropped (single-frame state-gas model; the clamp keeps
        -- the credit sound — it can never exceed what this tx charged).
        "  la x14, srfd_out; ld x15, 32(x14)\n" ++     -- zero-restore credit flag
        "  beqz x15, 11f\n" ++
        "  la x14, evm_state_gas_used; ld x15, 0(x14)\n" ++
        liStateGasRuntime "x16" 64 ++
        "  bleu x15, x16, 10f\n" ++
        "  mv x15, x16\n" ++                            -- applied = min(97920, used)
        "10:\n" ++
        "  ld x16, 0(x14); sub x16, x16, x15; sd x16, 0(x14)\n" ++
        "  la x14, evm_state_gas_spilled; ld x18, 0(x14)\n" ++
        "  mv x17, x15\n" ++
        "  bleu x18, x17, .Lsstore_refund_spill_le\n" ++
        "  mv x16, x17\n" ++
        "  j .Lsstore_refund_spill_have\n" ++
        ".Lsstore_refund_spill_le:\n" ++
        "  mv x16, x18\n" ++
        ".Lsstore_refund_spill_have:\n" ++
        "  sub x18, x18, x16; sd x18, 0(x14)\n" ++
        "  ld x18, 568(x20); add x18, x18, x16; sd x18, 568(x20)\n" ++
        "  sub x17, x17, x16\n" ++
        "  beqz x17, 11f\n" ++
        "  la x14, evm_state_gas_left; ld x16, 0(x14); add x16, x16, x17; sd x16, 0(x14)\n" ++
        "11:\n" ++
        "  ld x1, 0(sp); ld x10, 8(sp); ld x12, 16(sp); ld x13, 24(sp); ld x18, 32(sp); addi sp, sp, 48\n" ++
        -- Value-unchanged rewrites (found entry's current == new) append nothing:
        -- the found entry already records exactly this state, so last-write-wins
        -- reads, the end-of-tx commit, and the BAL change-set are all identical
        -- without a new entry. Skipping the append keeps long loops that rewrite
        -- the same value (e.g. a success flag per CALL iteration) from exhausting
        -- the 16384-entry exec-log arena and halting on the capacity guard.
        "  beqz x18, .Lsstore_append_entry\n" ++
        "  ld x16, 32(x18); ld x17, 32(x12); bne x16, x17, .Lsstore_append_entry\n" ++
        "  ld x16, 40(x18); ld x17, 40(x12); bne x16, x17, .Lsstore_append_entry\n" ++
        "  ld x16, 48(x18); ld x17, 48(x12); bne x16, x17, .Lsstore_append_entry\n" ++
        "  ld x16, 56(x18); ld x17, 56(x12); bne x16, x17, .Lsstore_append_entry\n" ++
        "  j .Lsstore_append_done\n" ++
        ".Lsstore_append_entry:\n" ++
        "  ld x15, 448(x20)\n" ++         -- reload current log_length
        "  li x14, 0xa0630000\n" ++
        "  slli x16, x15, 7\n" ++
        "  add x14, x14, x16\n" ++        -- x14 = &log[log_length] (append target)
        -- addrHash = current frame env.ADDRESS [x20+0..x20+32] (per-frame keying).
        "  ld x16, 0(x20)\n  sd x16, 0(x14)\n" ++
        "  ld x16, 8(x20)\n  sd x16, 8(x14)\n" ++
        "  ld x16, 16(x20)\n  sd x16, 16(x14)\n" ++
        "  ld x16, 24(x20)\n  sd x16, 24(x14)\n" ++
        -- slotKey from stack [x12+0..x12+32] → [x14+32..x14+64]
        "  ld x16, 0(x12)\n" ++
        "  sd x16, 32(x14)\n" ++
        "  ld x16, 8(x12)\n" ++
        "  sd x16, 40(x14)\n" ++
        "  ld x16, 16(x12)\n" ++
        "  sd x16, 48(x14)\n" ++
        "  ld x16, 24(x12)\n" ++
        "  sd x16, 56(x14)\n" ++
        -- original: copy from x18 if found; else write zeros
        "  beqz x18, 6f\n" ++
        "  ld x16, 0(x18)\n" ++
        "  sd x16, 64(x14)\n" ++
        "  ld x16, 8(x18)\n" ++
        "  sd x16, 72(x14)\n" ++
        "  ld x16, 16(x18)\n" ++
        "  sd x16, 80(x14)\n" ++
        "  ld x16, 24(x18)\n" ++
        "  sd x16, 88(x14)\n" ++
        "  j 7f\n" ++
        "6:\n" ++
        "  sd x0, 64(x14)\n" ++
        "  sd x0, 72(x14)\n" ++
        "  sd x0, 80(x14)\n" ++
        "  sd x0, 88(x14)\n" ++
        "7:\n" ++
        -- current from stack [x12+32..x12+64] → [x14+96..x14+128]
        "  ld x16, 32(x12)\n" ++
        "  sd x16, 96(x14)\n" ++
        "  ld x16, 40(x12)\n" ++
        "  sd x16, 104(x14)\n" ++
        "  ld x16, 48(x12)\n" ++
        "  sd x16, 112(x14)\n" ++
        "  ld x16, 56(x12)\n" ++
        "  sd x16, 120(x14)\n" ++
        -- bmvmx.1.6.6 enabler: stamp this entry's block_access_index (parallel array,
        -- indexed by the old log_length x15) for the future per-tx tuple-sequence check.
        -- x16/x17/x18 are dead post-append (the tail only uses x10).
        "  la x16, current_block_access_index\n  ld x17, 0(x16)\n" ++
        "  la x16, exec_log_txindex\n  slli x18, x15, 3\n  add x16, x16, x18\n  sd x17, 0(x16)\n" ++
        -- A new SSTORE row supersedes any stale provenance byte at this slot.
        "  la x16, exec_log_seed_flag\n  add x16, x16, x15\n  sb x0, 0(x16)\n" ++
        -- increment log_length
        "  addi x15, x15, 1\n" ++
        "  sd x15, 448(x20)\n" ++
        ".Lsstore_append_done:\n" ++
        -- r59nm S2b: record the storage WRITE into the tx-level storage_writes
        -- map, mirroring `set_storage` (state_tracker.py:489):
        -- `tx_state.storage_writes[address][key] = value`.
        --
        -- Placed HERE, not in the read recorder's slot at the top of preBody,
        -- because a write is conditional where a read is not: the spec calls
        -- set_storage after the gas checks, and every failing path above
        -- (the stipend guard, the 2929 charge, the 16384-row capacity guard)
        -- leaves via `.exit_outofgas` without reaching this label.
        --
        -- Both the append and the value-unchanged skip converge here, and the
        -- recorder is called on BOTH.  That is spec-faithful rather than
        -- sloppy: `set_storage` assigns unconditionally, and an upsert of the
        -- same value is idempotent, so mirroring the exec log's
        -- append-skipping optimisation here would be the reconstruction.
        --
        -- x12 still points at the pre-pop stack (the verified body's
        -- `ADDI x12, x12, 64` has not run), so key = x12[0..32] and the new
        -- value = x12[32..64].  a2 IS x12, so x12 is saved and restored around
        -- the call.  The verified body is untouched.
        "  addi sp, sp, -32\n" ++
        "  sd x1, 0(sp); sd x10, 8(sp); sd x11, 16(sp); sd x12, 24(sp)\n" ++
        "  mv a0, x20\n" ++
        "  mv a1, x12\n" ++
        "  addi a2, x12, 32\n" ++
        -- a6 = pre-tx baseline ptr, which is exactly what x18 already is: the
        -- handler maintains it as `&found.original` (:382, `x14 + 64`) or 0 meaning
        -- original == current == 0 (:465) -- the SAME pointer-or-zero convention
        -- `storage_write_record` documents for a6, so no conversion is needed.
        --
        -- WHY x18 AND NOT `sstore_prestate_pair`: that buffer is MULTIPLEXED -- it
        -- holds (address, key) for the committed-log lookup at :411-415 and only
        -- afterwards (original, current). On the ZERO path nothing overwrites +0, so
        -- it still holds the REVERSED 20-BYTE ADDRESS: byte-plausible, 32 bytes wide,
        -- and an address rather than a value.
        --
        -- WHY x18 IS LIVE HERE, verified rather than assumed: it is clobbered at :496
        -- as a scratch for `evm_state_gas_spilled` inside the zero-restore credit
        -- path, but the refund block saved it at :469 and RESTORES it at :510, and
        -- nothing between :510 and here writes it -- :517-550 only read it.
        --
        -- And it is uniform across every path that reaches this point. Where the
        -- append runs, :543-551 copies the original from x18 into the new row's +64
        -- (or zeros when x18 is 0); where the append is skipped as a value-unchanged
        -- rewrite, x18 already points at the found row's +64. Either way x18 is a
        -- valid pointer to this slot's transaction-start value.
        -- a6 = 0 -- the documented placeholder, RESTORED after `mv a6, x18` was
        -- measured to fault the guest. x18 is NOT a valid pointer here: the fixtures
        -- take a load access fault (mcause=0x5) at mtval=0xd8 inside
        -- storage_write_record, i.e. a6 = 216 -- neither a pointer nor the zero the
        -- ABI defines. The source-level liveness argument (saved :469, restored :510,
        -- read-only :517-550) was WRONG on at least one reachable path.
        --
        -- Control, same fixtures, same base: a6 = 0 gives ran=2 full-match=2;
        -- mv a6, x18 gives errored=2 ran=0.
        --
        -- ## THIS ZERO IS NOT A BASELINE, AND A FILTER MUST NOT TRUST IT
        --
        -- It is safe only because nothing reads the captured field. The moment a
        -- net-zero filter consumes it, IT IS WRONG IN THE FALSE-ACCEPT DIRECTION:
        --
        --   On a VALUE-UNCHANGED REWRITE the true baseline EQUALS the value being
        --   written, so the spec emits nothing (`block_access_lists.py:667-676`
        --   requires `pre_value != post_value`). With a baseline of zero and a
        --   nonzero post value, the filter concludes "changed" and EMITS A BAL ENTRY
        --   THE SPEC OMITS. The list stays well-formed, the entry count is wrong,
        --   and the hash is simply wrong — nothing faults and nothing complains.
        --
        -- The value-unchanged case is reachable at this call site: `:522`
        -- (`j .Lsstore_append_done`) jumps past the exec-log append while still
        -- reaching this call, so a rewrite of the same value arrives here.
        --
        -- So baseline acquisition belongs WITH the filter, not before it. Four
        -- attempts failed by trying to obtain the value without a consumer to
        -- constrain the choice: a carried register (`x18`) faulted, a dedicated
        -- global needed the same unreconstructable control flow to prove
        -- non-reentrancy, a recompute turned out to be half a lookup
        -- (`bv_mtx_committed_chunked_latest_value` answers only on a match, with the
        -- prestate-header fallback separate), and reading the exec-log row failed
        -- because the exec-log append and this write-map append are DIFFERENT events.
        --
        -- What survives, for whoever writes the filter: `x18` IS valid and holds the
        -- resolved original at `:517-521`, where the comparison reads it to decide the
        -- jump — upstream of everything that defeated the four attempts. And the two
        -- paths have a natural answer each: on the append path the exec-log row
        -- carries it; on the skip path the baseline IS the value being written, by
        -- definition of value-unchanged. Handled separately, neither branch needs a
        -- carried pointer or a control-flow argument.
        "  li a6, 0\n" ++
        "  jal ra, storage_write_record\n" ++
        "  ld x1, 0(sp); ld x10, 8(sp); ld x11, 16(sp); ld x12, 24(sp)\n" ++
        "  addi sp, sp, 32\n"
    , body    := ADDI .x12 .x12 (BitVec.ofNat 12 64)
    , tail    := .advanceAndRet 1 }
  , -- M24 real TLOAD. Scan transient log from end; copy matching
    -- current to stack top; default 0 on miss. Same shape as SLOAD
    -- but base 0xa0830000 and length env+464.
    { label   := "h_TLOAD"
    , opcodes := [0x5c]
    , preBody := stackUnderflowGuardAsm 1
      -- Verified reverse-scan core (byte-identical re-encoding of the former
      -- inline label-based scan; see the `#guard` pin below). Witnessed by
      -- `EvmAsm.Evm64.Transient.evm_tload_stack_spec_within`.
    , body    := EvmAsm.Evm64.Transient.evm_tload .x20
    , tail    := .advanceAndRet 1 }
  , -- M24 real TSTORE. Append-only (no scan). Transient storage has
    -- no gas refund logic, so we never need to track / preserve
    -- `original` — every TSTORE just appends a fresh entry. Subsequent
    -- TLOADs scan from end and find the most-recent (correct) value.
    { label   := "h_TSTORE"
    , opcodes := [0x5d]
    , preBody :=
        stackUnderflowGuardAsm 2 ++ "\n" ++
        staticContextWriteGuardAsm
      -- Verified append core (byte-identical reorder of the former inline
      -- preBody append text + the `addi x12, x12, 64` pop). Witnessed by
      -- `EvmAsm.Evm64.Transient.evm_tstore_stack_spec_within`.
    , body    := EvmAsm.Evm64.Transient.evm_tstore .x20
    , tail    := .advanceAndRet 1 } ]

/- **Byte-identity pin for the TSTORE body-as-Program rewire.**

   The verified `evm_tstore` body emits exactly the append instruction stream
   that used to live inline in the `h_TSTORE` `preBody`, followed by the
   `addi x12, x12, 64` pop that used to be the handler `body`. This `#guard`
   pins that emission so any future change to `evm_tstore` is caught. The only
   textual difference from the former inline text is the transient-log-base
   `li` immediate, now rendered in decimal (`2692939776`) rather than hex
   (`0xa0830000`) — the same numeric value, so the assembler produces
   byte-identical machine code (region map / symbol addresses unchanged). -/
#guard emitProgram (EvmAsm.Evm64.Transient.evm_tstore .x20) =
  "  ld x15, 464(x20)\n" ++
  "  li x14, 2692939776\n" ++
  "  slli x16, x15, 7\n" ++
  "  add x14, x14, x16\n" ++
  "  ld x16, 0(x20)\n  sd x16, 0(x14)\n" ++
  "  ld x16, 8(x20)\n  sd x16, 8(x14)\n" ++
  "  ld x16, 16(x20)\n  sd x16, 16(x14)\n" ++
  "  ld x16, 24(x20)\n  sd x16, 24(x14)\n" ++
  "  ld x16, 0(x12)\n  sd x16, 32(x14)\n" ++
  "  ld x16, 8(x12)\n  sd x16, 40(x14)\n" ++
  "  ld x16, 16(x12)\n  sd x16, 48(x14)\n" ++
  "  ld x16, 24(x12)\n  sd x16, 56(x14)\n" ++
  "  sd x0, 64(x14)\n  sd x0, 72(x14)\n  sd x0, 80(x14)\n  sd x0, 88(x14)\n" ++
  "  ld x16, 32(x12)\n  sd x16, 96(x14)\n" ++
  "  ld x16, 40(x12)\n  sd x16, 104(x14)\n" ++
  "  ld x16, 48(x12)\n  sd x16, 112(x14)\n" ++
  "  ld x16, 56(x12)\n  sd x16, 120(x14)\n" ++
  "  addi x15, x15, 1\n" ++
  "  sd x15, 464(x20)\n" ++
  "  addi x12, x12, 64"

/- **Byte-identity pin for the TLOAD body-as-Program rewire.**

   The verified `evm_tload` body emits exactly the scan instruction stream
   that used to live inline in the `h_TLOAD` `preBody`, with two purely
   textual re-encodings that assemble to byte-identical machine code
   (verified against `riscv64-elf-as`: both forms produce the same `.text`):

   - the numeric local labels (`1:`/`3:`/`4:`/`5:`) become the PC-relative
     offsets the assembler resolved them to (`.+N`/`.-N`; `beqz`/`bnez`/`j`
     are the canonical `beq`/`bne`/`jal x0` spellings of the same encodings);
   - `li x14, 0xa0830000` becomes its exact GNU-as expansion
     `lui x14, 0xa ; addiw x14, x14, 131 ; slli x14, x14, 16`, so the Lean
     `Program` layout (4 bytes/instruction) equals the machine layout and
     every branch offset is the real encoded offset.

   This `#guard` pins that emission so any future change to `evm_tload` is
   caught (region map / symbol addresses unchanged). -/
#guard emitProgram (EvmAsm.Evm64.Transient.evm_tload .x20) =
  "  ld x15, 464(x20)\n" ++
  "  beq x15, x0, .+168\n" ++
  "  lui x14, 0xa\n" ++
  "  addiw x14, x14, 131\n" ++
  "  slli x14, x14, 16\n" ++
  "  slli x16, x15, 7\n" ++
  "  add x14, x14, x16\n" ++
  "  addi x14, x14, -128\n" ++
  "  ld x16, 0(x14)\n  ld x17, 0(x20)\n  bne x16, x17, .+124\n" ++
  "  ld x16, 8(x14)\n  ld x17, 8(x20)\n  bne x16, x17, .+112\n" ++
  "  ld x16, 16(x14)\n  ld x17, 16(x20)\n  bne x16, x17, .+100\n" ++
  "  ld x16, 24(x14)\n  ld x17, 24(x20)\n  bne x16, x17, .+88\n" ++
  "  ld x16, 32(x14)\n  ld x17, 0(x12)\n  bne x16, x17, .+76\n" ++
  "  ld x16, 40(x14)\n  ld x17, 8(x12)\n  bne x16, x17, .+64\n" ++
  "  ld x16, 48(x14)\n  ld x17, 16(x12)\n  bne x16, x17, .+52\n" ++
  "  ld x16, 56(x14)\n  ld x17, 24(x12)\n  bne x16, x17, .+40\n" ++
  "  ld x16, 96(x14)\n  sd x16, 0(x12)\n" ++
  "  ld x16, 104(x14)\n  sd x16, 8(x12)\n" ++
  "  ld x16, 112(x14)\n  sd x16, 16(x12)\n" ++
  "  ld x16, 120(x14)\n  sd x16, 24(x12)\n" ++
  "  jal x0, .+28\n" ++
  "  addi x15, x15, -1\n" ++
  "  bne x15, x0, .-140\n" ++
  "  sd x0, 0(x12)\n" ++
  "  sd x0, 8(x12)\n" ++
  "  sd x0, 16(x12)\n" ++
  "  sd x0, 24(x12)"

/- **Byte-identity pin for the SLOAD body-as-Program rewire.**

   The verified `evm_sload` body emits exactly the persistent-log scan
   instruction stream that used to live inline in the `h_SLOAD` `preBody`, with
   the same two purely textual re-encodings as the TLOAD pin (numeric local
   labels → PC-relative offsets; `li x14, 0xa0630000` → its exact GNU-as
   expansion `lui x14, 0xa ; addiw x14, x14, 99 ; slli x14, x14, 16`), which
   assemble to byte-identical machine code (region map / symbol addresses
   unchanged). The scan is structurally identical to TLOAD's; only the log base
   (`0xa0630000` vs `0xa0830000`) and length-cell offset (`448` vs `464`)
   differ. -/
#guard emitProgram (EvmAsm.Evm64.Storage.evm_sload .x20) =
  "  ld x15, 448(x20)\n" ++
  "  beq x15, x0, .+168\n" ++
  "  lui x14, 0xa\n" ++
  "  addiw x14, x14, 99\n" ++
  "  slli x14, x14, 16\n" ++
  "  slli x16, x15, 7\n" ++
  "  add x14, x14, x16\n" ++
  "  addi x14, x14, -128\n" ++
  "  ld x16, 0(x14)\n  ld x17, 0(x20)\n  bne x16, x17, .+124\n" ++
  "  ld x16, 8(x14)\n  ld x17, 8(x20)\n  bne x16, x17, .+112\n" ++
  "  ld x16, 16(x14)\n  ld x17, 16(x20)\n  bne x16, x17, .+100\n" ++
  "  ld x16, 24(x14)\n  ld x17, 24(x20)\n  bne x16, x17, .+88\n" ++
  "  ld x16, 32(x14)\n  ld x17, 0(x12)\n  bne x16, x17, .+76\n" ++
  "  ld x16, 40(x14)\n  ld x17, 8(x12)\n  bne x16, x17, .+64\n" ++
  "  ld x16, 48(x14)\n  ld x17, 16(x12)\n  bne x16, x17, .+52\n" ++
  "  ld x16, 56(x14)\n  ld x17, 24(x12)\n  bne x16, x17, .+40\n" ++
  "  ld x16, 96(x14)\n  sd x16, 0(x12)\n" ++
  "  ld x16, 104(x14)\n  sd x16, 8(x12)\n" ++
  "  ld x16, 112(x14)\n  sd x16, 16(x12)\n" ++
  "  ld x16, 120(x14)\n  sd x16, 24(x12)\n" ++
  "  jal x0, .+28\n" ++
  "  addi x15, x15, -1\n" ++
  "  bne x15, x0, .-140\n" ++
  "  sd x0, 0(x12)\n" ++
  "  sd x0, 8(x12)\n" ++
  "  sd x0, 16(x12)\n" ++
  "  sd x0, 24(x12)"

end EvmAsm.Codegen
