/-
  EvmAsm.Codegen.Programs.Storage

  M24 Option A storage handlers (SLOAD, SSTORE, TLOAD, TSTORE).
  The transient log uses 128-byte entries keyed by `(addrHash, slotKey)`;
  canonical persistent reads and writes resolve through the transaction write
  map and authenticated fallbacks.

  The transient storage log lives at `0xa0830000` in `STATE_TRACKER_AREA`.

  Each entry is 128 bytes, 8-byte aligned:
    +0..32   addrHash   (the executing frame's env.ADDRESS (env+0) — per-contract
                          keying so a nested callee's slots are isolated from the
                          caller's. The transient log keys on it; persistent
                          SLOAD/SSTORE maps use the same frame address key.)
    +32..64  slotKey    (EVM-stack byte order: 4 LE u64 limbs, low first)
    +64..96  original   (transient slot's initial value)
    +96..128 current    (transient slot's latest value)

  Log lengths live in env:
    env+448  retired persistent-log counter (kept for env-layout compatibility)
    env+456  retired (GH #10981; REVERT reads body_state_snapshot slab +40)
    env+464  transientLogLengthOff  (live counter; TSTORE increments; reset on REVERT)

  ## Semantics

  **SLOAD (0x54)** — resolve the current value from the transaction write
  map, then the committed map or authenticated state on a miss. Net stack
  delta = 0.

  **SSTORE (0x55)** — resolve the transaction-start `original` and current
  value from the write maps or authenticated state, charge EIP-2200 gas, and
  upsert the transaction write map. Rollback is handled by its undo journal.
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

  - Persistent SLOAD/SSTORE maps and transient TLOAD/TSTORE key on the frame's
    env.ADDRESS (multi-contract isolated); only the transient side has a live
    append-only log.
  - Cold `SLOAD` misses are resolved through the authenticated state path;
    genuinely absent slots produce zero. The legacy input format may still
    carry preload rows for standalone callers, but runtime setup skips those
    rows because the canonical map/state path is authoritative. ⛔ The earlier
    claim that a BAL preload stages every
    slot is refuted: measured cold-miss resolution runs in production. What a
    demand-driven `SLOAD` read still needs is a **present-slot** case — every
    measured cold miss resolved a genuinely-absent slot, so the found path is
    unexercised. See `storagePrestateResolveAsm` below for the full funnel.
  - The transient log is capped at 16384 128-byte entries (2 MiB), well past
    any test workload.
  - Inline asm, not verified bodies. Verified-loop bodies follow later.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Stateless.SpecRef.Gas
import EvmAsm.Codegen.Programs.StaticContext
import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Codegen.Programs.CreateCodeEffectLog
import EvmAsm.Evm64.Transient.StoreProgram
import EvmAsm.Evm64.Transient.LoadProgram

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Additional SSTORE gas after the dispatcher warm floor and storage-access
    helper have run.

    Inputs:
    - `x12`: stack pointer. `[x12+0..32]` is key, `[x12+32..64]` is new value.
    - `x18`: pointer to the resolved transaction-map `(original,current)` pair,
      or zero for an absent slot.
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

/-! The tx-level write map is the live same-transaction storage reader.  Its
    rows use the exact little-endian key bytes written by `storage_write_record`.
    On a hit this helper returns `x18 = out`, with `out[0..32]` equal to the
    transaction-start original (`+96`) and `out[32..64]` equal to current
    (`+64`).  On a miss it returns `x18 = 0`. -/
def storageTxMapFindAsm (p : String) (out : String) : String :=
  "  la x14, tx_storage_writes_count; ld x15, 0(x14)\n" ++
  "  li x16, 16384; bgtu x15, x16, .exit_outofgas\n" ++
  "  li x14, 0xa21a0000; li x16, 0\n" ++
  ".L" ++ p ++ "_txmap_scan:\n" ++
  "  bgeu x16, x15, .L" ++ p ++ "_txmap_miss\n" ++
  "  slli x17, x16, 7; add x17, x14, x17\n" ++
  "  ld x18, 0(x17); ld x19, 0(x20); bne x18, x19, .L" ++ p ++ "_txmap_next\n" ++
  "  ld x18, 8(x17); ld x19, 8(x20); bne x18, x19, .L" ++ p ++ "_txmap_next\n" ++
  "  ld x18, 16(x17); ld x19, 16(x20); bne x18, x19, .L" ++ p ++ "_txmap_next\n" ++
  "  ld x18, 24(x17); ld x19, 24(x20); bne x18, x19, .L" ++ p ++ "_txmap_next\n" ++
  "  ld x18, 32(x17); ld x19, 0(x12); bne x18, x19, .L" ++ p ++ "_txmap_next\n" ++
  "  ld x18, 40(x17); ld x19, 8(x12); bne x18, x19, .L" ++ p ++ "_txmap_next\n" ++
  "  ld x18, 48(x17); ld x19, 16(x12); bne x18, x19, .L" ++ p ++ "_txmap_next\n" ++
  "  ld x18, 56(x17); ld x19, 24(x12); bne x18, x19, .L" ++ p ++ "_txmap_next\n" ++
  "  la x14, " ++ out ++ "\n" ++
  "  ld x19, 96(x17); sd x19, 0(x14); ld x19, 104(x17); sd x19, 8(x14)\n" ++
  "  ld x19, 112(x17); sd x19, 16(x14); ld x19, 120(x17); sd x19, 24(x14)\n" ++
  "  ld x19, 64(x17); sd x19, 32(x14); ld x19, 72(x17); sd x19, 40(x14)\n" ++
  "  ld x19, 80(x17); sd x19, 48(x14); ld x19, 88(x17); sd x19, 56(x14)\n" ++
  "  la x18, " ++ out ++ "; j .L" ++ p ++ "_txmap_done\n" ++
  ".L" ++ p ++ "_txmap_next:\n" ++
  "  addi x16, x16, 1; j .L" ++ p ++ "_txmap_scan\n" ++
  ".L" ++ p ++ "_txmap_miss:\n" ++
  "  li x18, 0\n" ++
  ".L" ++ p ++ "_txmap_done:\n"

/-- GH #10874: resolve a storage-key MISS to its authenticated pre-state
    value, in the THREE-TIER order execution-specs requires. Entered with
    `x18 = 0` (miss) or nonzero (hit, in which case it is a no-op); on success
    sets `x18` to a 64-byte `(original, current)` pair in LE-limb order.

    The tiers, and why the order is load-bearing:

    1. the transaction write map, carrying current and the transaction-start
       original;
    2. `storage_writes_block_latest_value`, which reads the canonical
       execution-specs `BlockState.storage_writes` map: a prior successful
       transaction's committed value is the next transaction's `original` AND
       `current` alike;
    3. `slot_at_header_state_root` against the PARENT header — the witness,
       read BY KEY on demand, matching `WitnessState.get_storage`;
    4. otherwise zero (an absent account or slot is implicitly zero).

    ⚠️ Skipping tier 2 and going straight to the witness would return the
    PRE-BLOCK value wherever a prior transaction in this block already wrote the
    slot. That is why a demand-driven `h_SLOAD` must reuse this chain rather than
    call `sload_at_header_state_root`, which resolves the witness tier ALONE.

    ✅ TIER 3 WORKS, AND IT RUNS IN PRODUCTION. Measured on the UNMODIFIED guest
    (`main` `d97788890`, ELF `fbb83b69...`), counting PCs from the objdump:

    | row | tier-3 entries | header len (`env+584`) | status-4 header fails |
    |---|---|---|---|
    | `00000_test_sstore_xto_y_...d4-g0__b0` | **16** | `0x27c` at all 16 | **0** |
    | `00163_test_sstore_xto_x_...d1-g0__b0` | **17** | `0x27c` at all 17 | **0** |

    Every production call gets a well-formed header, resolves the account, walks the
    storage trie, and correctly reports not-found -- because on these rows the
    accounts looked up have **zero pre-state `storage` entries** in the fixture, so an
    empty storage root is the right answer and the fallback to value 0 is correct.

    ⛔ FOUR CLAIMS THAT USED TO BE HERE WERE REFUTED BY MEASUREMENT (GH #11105,
    GH #11122 closed invalid). Recorded so nobody re-derives them:
    * *"tier 3 does not work / returns status 4 on every call"* -- it works. The
      82-call funnel that produced that reading came from a probe build whose log was
      ⚠️ **CORRUPTED, not starved** -- an earlier revision of this note said "the
      preload starved" and that was wrong about its own instrument. The probe zeroed
      only the scan bound (`env+448`); the legacy preload count is guarded by the count
      REGISTER `x6` and still wrote all 16 arena entries, which each SSTORE then
      appended over from index 0. That is a state production cannot reach, and it is
      what manufactured the 16 zero-length-header calls -- production has **zero**.
      The tell was that `h_SSTORE` ran **312 times in both builds**: an intervention
      that leaves a downstream count identical did not land. See PLAN.md
      "Probe discipline" before building another one.
    * *"this chain never executes in production, the preload means SSTORE never sees
      a cold miss"* -- it executes 16 times on a single row of the unmodified guest.
      Production does see cold misses.
    * *"the former eager seed / `stage_predeploy_storage_preload` are WORKING
      callers"* -- unsupported; both BAL-sourced producers have been retired
      from the production verdict path. Request predeploys use the authenticated
      state path instead.
    * *"the raw slot key needs keccak-hashing first"* -- `mpt_lookup_by_key` calls
      `zkvm_keccak256` itself, and `account_at_address` reaches the trie through the
      SAME routine.

    ⚠️ WHAT IS STILL NOT SHOWN: that tier 3 returns the right value for a slot that
    **is** in the pre-state. Every measured call resolved a genuinely-absent slot, so
    the not-found path is exercised and the found path is not. A present-slot case is
    the open gate for GH #10874 -- and note that every non-zero status is flattened to
    value 0, so a broken authenticated read would be indistinguishable from an absent
    slot.

    ✅ AND ONE OPERAND QUESTION IS SETTLED: `ExecutionWitness`
    (`execution-specs/.../stateless.py`) has exactly three fields -- `state`, `codes`,
    `headers`. There is **no separate storage-node container**; `state` is one flat
    pool of trie-node preimages. So passing the same pointer for both the state and
    storage arguments below is CORRECT, not a two-containers defect.

    `p` prefixes the named labels so both handlers can instantiate it.
    `out` is a 64-byte scratch buffer, also used to stage the canonical
    big-endian address and key the witness lookup needs.

    Returns via `x18`; clobbers `x14`-`x17` and `a0`-`a7`. The caller must save
    `x1`/`x10`/`x12`/`x13`/`x19` around it (there are `jal`s inside). -/
def storagePrestateResolveAsm (p : String) (out : String) : String :=
  ".L" ++ p ++ "_prestate_normal:\n" ++
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
  -- Tier 1: same-transaction current plus the transaction-start original.
  storageTxMapFindAsm p out ++
  "  bnez x18, .L" ++ p ++ "_prestate_restore\n" ++
  -- Tier 2: the block-committed map (execution-specs' BlockState.storage_writes).
  "  la x14, sstore_committed_hit; sd zero, 0(x14)\n" ++
  "  la x14, storage_writes_count; ld a3, 0(x14); beqz a3, .L" ++ p ++ "_committed_done\n" ++
  "  mv a0, x20; la a1, " ++ out ++ "; addi a1, a1, 32\n" ++
  "  li a2, 0xa1fa0000; li a4, 16384; la a5, sstore_committed_current; la a6, dtrc_recipkey; la a7, dtrc_slotkey_le\n" ++
  -- ⚠️ Pre-existing and deliberately PRESERVED: this leaves for `.exit_outofgas`
  -- with `sp` still 40 bytes low. Harmless because that exit terminates the
  -- frame, and kept verbatim so the extraction is byte-identical at the SSTORE
  -- site rather than "behaviour-neutral as far as I can tell".
  "  jal ra, storage_writes_block_latest_value\n" ++
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
  -- GH #11162 / #10874: classify tier-3 witness statuses WITHOUT changing the
  -- resolved value (every non-zero arm still falls to `_prestate_zero`). Spec
  -- `witness_state.py` flattens absent account → EMPTY_TRIE_ROOT → U256(0) and
  -- absent slot → U256(0); both are legitimate zeros, not integrity failures.
  -- Unified `slot_at_header_state_root` enum (StateCompose):
  --   0 found
  --   1 account not in state trie  → sstore_witness_absent_account  (#11162)
  --   5 slot not in storage trie   → sstore_witness_absent          (slot)
  --   2/3/4/6/7 real faults        → sstore_witness_integrity_fail + last_status
  -- Counters only: no verdict consumer (#11138 policy unset). Do NOT fold 1 into
  -- 5 — that would fix the false-positive by creating a smaller over-report.
  "  li x14, 1; beq a0, x14, .L" ++ p ++ "_prestate_absent_account\n" ++
  "  li x14, 5; beq a0, x14, .L" ++ p ++ "_prestate_absent_slot\n" ++
  "  j .L" ++ p ++ "_prestate_integrity\n" ++
  ".L" ++ p ++ "_prestate_absent_account:\n" ++
  "  la x14, sstore_witness_absent_account; ld x15, 0(x14); addi x15, x15, 1; sd x15, 0(x14)\n" ++
  "  j .L" ++ p ++ "_prestate_zero\n" ++
  ".L" ++ p ++ "_prestate_absent_slot:\n" ++
  "  la x14, sstore_witness_absent; ld x15, 0(x14); addi x15, x15, 1; sd x15, 0(x14)\n" ++
  "  j .L" ++ p ++ "_prestate_zero\n" ++
  ".L" ++ p ++ "_prestate_integrity:\n" ++
  "  la x14, sstore_witness_integrity_fail; ld x15, 0(x14); addi x15, x15, 1; sd x15, 0(x14)\n" ++
  "  la x14, sstore_witness_last_status; sd a0, 0(x14)\n" ++
  "  j .L" ++ p ++ "_prestate_zero\n" ++
  ".L" ++ p ++ "_prestate_found:\n" ++
  -- sahsr_u256 is canonical big-endian. Materialize both original and current
  -- in the exec-log's little-endian-limb order in the pair buffer.
  "  la x14, sahsr_u256; la x15, " ++ out ++ "; addi x15, x15, 31; li x16, 32\n" ++
  ".L" ++ p ++ "_prestate_value_rev:\n" ++
  "  lbu x17, 0(x14); sb x17, 0(x15); addi x14, x14, 1; addi x15, x15, -1; addi x16, x16, -1; bnez x16, .L" ++ p ++ "_prestate_value_rev\n" ++
  "  la x15, " ++ out ++ "; ld x14, 0(x15); sd x14, 32(x15); ld x14, 8(x15); sd x14, 40(x15); ld x14, 16(x15); sd x14, 48(x15); ld x14, 24(x15); sd x14, 56(x15)\n" ++
  "  la x18, " ++ out ++ "; j .L" ++ p ++ "_prestate_restore\n" ++
  ".L" ++ p ++ "_prestate_zero:\n" ++
  "  la x14, " ++ out ++ "; sd zero, 0(x14); sd zero, 8(x14); sd zero, 16(x14); sd zero, 24(x14); sd zero, 32(x14); sd zero, 40(x14); sd zero, 48(x14); sd zero, 56(x14)\n" ++
  "  li x18, 0\n" ++
  ".L" ++ p ++ "_prestate_restore:\n" ++
  "  ld x1, 0(sp); ld x10, 8(sp); ld x12, 16(sp); ld x13, 24(sp); ld x19, 32(sp); addi sp, sp, 40\n" ++
  ".L" ++ p ++ "_prestate_done:\n"

/-- M24 Option A storage handlers. -/
def storageHandlers : List OpcodeHandlerSpec :=
  [ -- M24 real SLOAD. Resolve through the transaction write map and the
    -- authenticated fallback.
    { label   := "h_SLOAD"
    , opcodes := [0x54]
    , preBody :=
        stackUnderflowGuardAsm 1 ++ "\n" ++
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
        -- GH #10619: record the storage READ into the block-lifetime read
        -- container.  This is deliberately AFTER the access-cost check:
        -- execution-specs charges SLOAD before get_storage, so a cold-access
        -- OOG must not leave a durable storage-read row behind.  The read is
        -- still unconditional after a successful access check and survives
        -- rollback, matching state_tracker.py:90-93, :809-826.
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
        -- Resolve the current value from the tx write map, then the committed
        -- block map, then the authenticated parent state.  The resolver also
        -- returns the tx-start original needed by SSTORE; SLOAD uses only the
        -- current half of its pair.
        "  addi sp, sp, -8\n" ++
        "  sd x11, 0(sp)\n" ++
        -- Read the canonical tx map first. A miss is resolved through the
        -- block map or authenticated state.
        storageTxMapFindAsm "sload_live" "sstore_prestate_pair" ++
        "  bnez x18, .Lsload_live_use\n" ++
        storagePrestateResolveAsm "sload" "sstore_prestate_pair" ++
        "  j .Lsload_live_use\n" ++
        ".Lsload_live_use:\n" ++
        "  ld x11, 0(sp); addi sp, sp, 8\n" ++
        "  beqz x18, .Lsload_map_zero\n" ++
        "  ld x16, 32(x18); sd x16, 0(x12)\n" ++
        "  ld x16, 40(x18); sd x16, 8(x12)\n" ++
        "  ld x16, 48(x18); sd x16, 16(x12)\n" ++
        "  ld x16, 56(x18); sd x16, 24(x12)\n" ++
        "  j .Lsload_map_done\n" ++
        ".Lsload_map_zero:\n" ++
        "  sd x0, 0(x12); sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)\n" ++
        ".Lsload_map_done:\n"
      -- The map lookup above is the live SLOAD body; no persistent-log scanner
      -- is linked from the handler.
    , body    := []
    , tail    := .advanceAndRet 1 }
  , -- M24 real SSTORE. Resolve the transaction-start original and current
    -- value through the transaction write map, committed map, and authenticated
    -- fallback, then upsert the transaction write map. Body's
    -- `ADDI x12, x12, 64` does the net -2 stack pop.
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
        -- EIP-2929 storage-key access gas. The dispatch table already
        -- charged SSTORE's 100 warm floor, so this helper only charges
        -- the 2900 cold delta on first key touch. Run before the resolver /
        -- write-map path so out-of-gas cannot mutate persistent storage state.
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
        -- GH #10619: record the storage READ after the access-cost check but
        -- before SSTORE's value-dependent gas pricing.  The prestate read is
        -- required to price the write, while execution-specs' cold-access
        -- `check_gas` must run first; otherwise a cold-access OOG leaves a
        -- durable read row that the spec never records.
        "  addi sp, sp, -24\n" ++
        "  sd x1, 0(sp); sd x10, 8(sp); sd x11, 16(sp)\n" ++
        "  mv a0, x20\n" ++
        "  mv a1, x12\n" ++
        "  jal ra, storage_read_record\n" ++
        "  ld x1, 0(sp); ld x10, 8(sp); ld x11, 16(sp)\n" ++
        "  addi sp, sp, 24\n" ++
        -- execution-specs gives every address in transaction-local
        -- `created_accounts` a zero original storage view, even when a later
        -- CALL reaches that account after its CREATE frame returned. Query the
        -- shared AccountState set directly; a frame-local CREATE flag misses
        -- that later-call case and is not the semantic predicate.
        "  la x14, sstore_created_original_zero; sd zero, 0(x14)\n" ++
        "  la x14, sstore_prestate_pair; mv x15, x20\n" ++
        runtimeAccessWordToBe20Asm "sstore_created" "x15" "x14" "x16" "x17" ++
        "  addi sp, sp, -48\n" ++
        "  sd x1, 0(sp); sd x10, 8(sp); sd x11, 16(sp); sd x12, 24(sp); sd x13, 32(sp)\n" ++
        "  la a0, sstore_prestate_pair; jal ra, account_writes_created_contains\n" ++
        "  la x14, sstore_created_original_zero; sd a0, 0(x14)\n" ++
        "  ld x1, 0(sp); ld x10, 8(sp); ld x11, 16(sp); ld x12, 24(sp); ld x13, 32(sp); addi sp, sp, 48\n" ++
        "  la x14, sstore_created_original_zero; ld x14, 0(x14); beqz x14, .Lsstore_created_original_scan\n" ++
        "  j .Lsstore_created_original_zero\n" ++
        ".Lsstore_created_original_zero:\n" ++
        -- Preserve original=0, but keep scanning so a later write sees the
        -- current value established by an earlier same-transaction write.
        "  li x14, 1; la x16, sstore_created_original_zero; sd x14, 0(x16); j .Lsstore_created_original_scan\n" ++
        ".Lsstore_created_original_scan:\n" ++
        -- Resolve tx current + tx-start original from the canonical map, then
        -- block state / parent witness on a tx-map miss.
        storagePrestateResolveAsm "sstore" "sstore_prestate_pair" ++
        -- CREATE's original-value rule is transaction-local zero even if the
        -- generic fallback found a pre-existing account value.  Preserve the
        -- current half from a same-tx map hit while replacing only original.
        "  la x14, sstore_created_original_zero; ld x14, 0(x14); beqz x14, .Lsstore_created_original_done\n" ++
        "  beqz x18, .Lsstore_created_original_done\n" ++
        "  sd zero, 0(x18); sd zero, 8(x18); sd zero, 16(x18); sd zero, 24(x18)\n" ++
        ".Lsstore_created_original_done:\n" ++
        -- The tx map is bounded independently of the retained compatibility log.
        -- The recorder performs the authoritative upsert/capacity check; this
        -- fast guard rejects malformed counts before gas/refund work.
        "  la x14, tx_storage_writes_count; ld x15, 0(x14)\n" ++
        "  li x14, 16384\n" ++
        "  bgtu x15, x14, .exit_outofgas\n" ++
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
        -- The append-only execution log is no longer consulted or mutated.
        -- The canonical tx map below is the sole write-side update.
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
        -- same value is idempotent, so skipping the map update here would be a
        -- reconstruction rather than the specified unconditional assignment.
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
        -- `x18` is either the resolver's pair (original at +0) or zero for
        -- an absent slot.  `storage_write_record` captures this tx-start
        -- original at map-row +96 on APPEND and ignores it on a hit.
        "  mv a6, x18\n" ++
        "  jal ra, storage_write_record\n" ++
        -- #11329 TOUCHED producer: every set_storage also marks the account in
        -- account_writes so map-root enumeration sees storage-only touches
        -- (entry6 digests 51e4b462 / 84e7a559). Frame: +0..24 saved regs,
        -- +32..51 BE20 scratch (LE env.ADDRESS reversed). Then
        -- account_write_touch_current (AccountState snapshot + TOUCHED).
        "  addi sp, sp, -64\n" ++
        "  sd x1, 0(sp); sd x10, 8(sp); sd x11, 16(sp); sd x12, 24(sp)\n" ++
        "  sd zero, 32(sp); sd zero, 40(sp); sd zero, 48(sp); sd zero, 56(sp)\n" ++
        "  li t5, 0\n" ++
        ".Lsstore_touch_rev:\n" ++
        "  li t0, 20; beq t5, t0, .Lsstore_touch_call\n" ++
        "  li t0, 19; sub t0, t0, t5; add t0, x20, t0; lbu t1, 0(t0)\n" ++
        "  addi t0, sp, 32; add t0, t0, t5; sb t1, 0(t0)\n" ++
        "  addi t5, t5, 1; j .Lsstore_touch_rev\n" ++
        ".Lsstore_touch_call:\n" ++
        "  addi a0, sp, 32; jal ra, account_write_touch_current\n" ++
        "  ld x1, 0(sp); ld x10, 8(sp); ld x11, 16(sp); ld x12, 24(sp)\n" ++
        "  addi sp, sp, 64\n" ++
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

end EvmAsm.Codegen
