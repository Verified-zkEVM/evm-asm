/-
  EvmAsm.Stateless.MemoryLayout

  ############################################################################
  ##  STATUS: ASPIRATIONAL (scheme A) — NOT the emitted guest's layout.     ##
  ##                                                                        ##
  ##  These "working-RAM anchors" are the layout contract for the           ##
  ##  in-progress `EvmAsm/Stateless/` port, which does NOT drive the        ##
  ##  emitted `stateless_guest` today. With one partial exception           ##
  ##  (`STATE_TRACKER_AREA`, wired into the M24 storage exec-logs), NO      ##
  ##  emitted guest instruction references any anchor below; the guest's    ##
  ##  real EVM memory / value stack / node & code tables live in `.data`    ##
  ##  (`-Tdata=0xa3000000`) and in place in the INPUT blob. Worse, the      ##
  ##  live RV64 call stack (`_start`: `li sp, 0xa0050000`, grows down)      ##
  ##  OCCUPIES `[0xa0020000, 0xa0050000)` — i.e. `SSZ_INPUT_DECODED` and    ##
  ##  the bottom of `EXECUTION_WITNESS_AREA` are stack memory in the        ##
  ##  current build. Both facts are kernel-checked in                       ##
  ##  `EvmAsm/Codegen/RegionMap.lean`                                       ##
  ##  (`guestStack_overlaps_executionWitnessArea`,                          ##
  ##  `guestStack_not_disjoint_from_schemeA`); the reflow is bead           ##
  ##  `evm-asm-0z5qy` (P1).                                                 ##
  ##                                                                        ##
  ##  For the EMITTED-REALITY region map — what routine triples must        ##
  ##  frame against — use `EvmAsm/Codegen/RegionMap.lean`                   ##
  ##  (`guestRegionMap`, pairwise-disjoint, ELF-drift-guarded by            ##
  ##  `scripts/check-region-map.sh`). Do NOT derive assertions or specs     ##
  ##  from the anchors below; see the per-anchor notes for where each       ##
  ##  structure actually lives today.                                       ##
  ############################################################################

  Single source of truth for the address-space layout INTENDED by the
  stateless-guest port of `run_stateless_guest`
  (`execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py`).

  All RISC-V modules under `EvmAsm/Stateless/` agree on the constants
  declared here. Treat this file as the (aspirational) port contract: any
  new module must document, in its file header, which regions it reads,
  writes, and leaves untouched, plus which exit ECALLs it can take.
  Mirrors the "memory layout + side effects" convention already used by
  `EvmAsm/Evm64/DivMod/AddrNorm.lean` and the Keccak ECALL bridge.

  ## Top-level map (RV64IM, ZisK host-IO compatible)

  Authoritative ziskemu addresses (see `EvmAsm/Codegen/Driver.lean:68-82`
  for the linker flags and `EvmAsm/Codegen/Programs.lean` for the
  `INPUT_ADDR`/`OUTPUT_ADDR` constants):

  ```
  0x00000020 .. 0x78000000   legacy verified zone (low-scratch)
  0x40000000 .. 0x40002000   INPUT_ADDR  (8 KiB, host-supplied SSZ input)
                               [+ 0..8]   ZisK metadata (zero)
                               [+ 8..16]  LE u64 length of first record
                               [+16..]    SSZ-encoded SszStatelessInput
  0x80000000 .. 0xa0000000   .text + .rodata + .bss (ELF `-Ttext=0x80000000`)
  0xa3000000 .. 0xbf980000   .data (`-Tdata=0xa3000000`; static tables,
                             fixed data, and 1G-cap BSR/BAL arenas)
  0xa0010000 .. 0xa0020000   OUTPUT_ADDR (64 KiB, public output)
                               [+ 0..N]   SSZ-encoded
                                          SszStatelessValidationResult
  0xa0020000 .. 0xa3000000   working RAM (decoded structures, DBs,
                             frames) -- the Stateless guest claims this
                             lower tail of ziskemu's RAM region.
  0xbf980000 .. 0xc0000000   .sszscratch NOBITS merkleization scratch
  ```

  `INPUT_ADDR`, `INPUT_DATA_OFFSET`, and `OUTPUT_ADDR` mirror the
  constants in `EvmAsm/Codegen/Programs.lean`; do not duplicate the
  numeric values here -- the working-RAM sub-region anchors below are
  the new contribution.

  All three observable zones (legacy, input, RAM) are recognised by
  the verified `isValidMemAddr` predicate as of issue #5164 -- see
  `EvmAsm/Rv64/Basic.lean` for the disjunctive definition.

  ## Working-RAM sub-regions (0xa0020000 .. 0xa3000000)

  Each anchor is the start of a region whose size is sized at codegen
  time. Sizes will be tightened as modules land; for now we reserve
  generous slabs so successive PRs do not have to reflow addresses.
  Total reserved through `SHA256_SCRATCH` end is ~28 MiB; ziskemu's
  RAM region carries ~512 MiB of headroom past `0xa0020000`.

  | Anchor                       | Address          | Size budget |
  |------------------------------|------------------|-------------|
  | `STATELESS_WORK_BASE`        | `0xa0020000`     | base ref    |
  | `SSZ_INPUT_DECODED`          | `0xa0020000`     | 64 KiB      |
  | `EXECUTION_WITNESS_AREA`     | `0xa0030000`     | 1 MiB       |
  | `NODE_DB_BUCKETS`            | `0xa0130000`     | 4 MiB       |
  | `CODE_DB_BUCKETS`            | `0xa0530000`     | 1 MiB       |
  | `STATE_TRACKER_AREA`         | `0xa0630000`     | 4 MiB       |
  | `EVM_FRAME_STACK`            | `0xa0a30000`     | 256 KiB     |
  | `EVM_VALUE_STACK`            | `0xa0a70000`     | 1 MiB       |
  | `EVM_MEMORY_AREA`            | `0xa0b70000`     | 16 MiB      |
  | `KECCAK_SCRATCH`             | `0xa1b70000`     | 64 KiB      |
  | `ECRECOVER_SCRATCH`          | `0xa1b80000`     | 64 KiB      |
  | `SHA256_SCRATCH`             | `0xa1b90000`     | 64 KiB      |
  | `STORAGE_READS_AREA`         | `0xa1ba0000`     | 1 MiB       |
  | `ACCOUNT_READS_AREA`         | `0xa1ca0000`     | 512 KiB     |
  | `CODE_READS_AREA`            | `0xa1d20000`     | 512 KiB     |

  (`EVM_MEMORY_AREA` budget is per-frame nominal; with max call depth
  1024 the precise per-frame slicing is tracked in `Stateless/VM/`.)

  ## Calling convention (non-leaf stateless code)

  The existing opcode handlers are leaf functions. The stateless guest
  is deeply nested, so non-leaf code in `EvmAsm/Stateless/` follows a
  standard RV64 ABI:

  - `x1 (ra)`           : return address
  - `x2 (sp)`           : RV64 call stack pointer (distinct from EVM
                          value-stack `x12`)
  - `x10..x17 (a0..a7)` : args / returns
  - `x12`               : EVM value-stack pointer (preserved across
                          opcode handler calls, saved/restored at
                          message-frame boundaries)
  - `x18..x27 (s2..s11)`: callee-saved
  - Each non-leaf entry sets up an explicit `sp` adjust; the per-module
    frame size is documented at the top of that module's `Program.lean`.
-/

import EvmAsm.Rv64.Word

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-! ## Working-RAM anchors (see table above)

**Every anchor below is ASPIRATIONAL unless its note says otherwise** —
see the header status block. Each note names the emitted structure that
actually plays the role today, so no future reader derives layout facts
from a dead anchor. The `def`s are kept (values unchanged) because
`Codegen/RegionMap.lean` pins them (`schemeA_matches_layout`) and the
scheme-A port contract still targets them post-reflow (`evm-asm-0z5qy`). -/

/-- ASPIRATIONAL — and currently **inside the live RV64 stack**
    `[0xa0020000, 0xa0050000)`. Unusable until the `evm-asm-0z5qy` reflow. -/
def STATELESS_WORK_BASE     : Word := 0xa0020000
/-- ASPIRATIONAL — **collides with the live RV64 stack** (kernel-checked:
    `RegionMap.guestStack_not_disjoint_from_schemeA`). Emitted reality:
    nothing is decoded out of the input; the SSZ blob is navigated in
    place at `SSZ_BASE = INPUT + 18`
    (`Codegen/Programs/StatelessVerdict.lean`). -/
def SSZ_INPUT_DECODED       : Word := 0xa0020000
/-- ASPIRATIONAL — its bottom `[0xa0030000, 0xa0050000)` is **live RV64
    stack** (kernel-checked:
    `RegionMap.guestStack_overlaps_executionWitnessArea`). Emitted
    reality: witness sections stay in place in INPUT as `(ptr, len)`
    views (`extract_witness_state_section`,
    `Codegen/Programs/SszWitnessState.lean`); assertion vocabulary in
    `EvmAsm/Evm64/WitnessAssertions.lean`. -/
def EXECUTION_WITNESS_AREA  : Word := 0xa0030000
/-- ASPIRATIONAL — no emitted instruction references it
    (`Stateless/Witness/NodeDb/*` are scaffolds). Emitted reality: the
    node DB is the `mset_db_*` append log in `.data` (8 MiB,
    `Codegen/Programs/MptSetAcc.lean`); assertion vocabulary in
    `EvmAsm/Evm64/MptAssertions.lean`. -/
def NODE_DB_BUCKETS         : Word := 0xa0130000
/-- ASPIRATIONAL — no emitted instruction references it
    (`Stateless/Witness/CodeDb/*` are scaffolds). Emitted reality: the
    code DB is the `wcidx_*` sorted 48-byte-record index over the
    in-place SSZ codes section (`Codegen/Programs/MptWitnessIndex.lean`,
    `WitnessCodeLookup.lean`); assertion vocabulary in
    `EvmAsm/Evm64/WitnessAssertions.lean`. -/
def CODE_DB_BUCKETS         : Word := 0xa0530000
/-- **LIVE (the one wired-in anchor)**: the M24 storage exec-logs —
    persistent log at `0xa0630000`, transient at `0xa0830000`, 128-byte
    entries, 2 MiB live extent (`Codegen/Programs/Storage.lean`,
    `RegionMap.lean` `state_tracker_live`); assertion vocabulary in
    `EvmAsm/Evm64/StorageAssertions.lean`. The remaining 2 MiB of the
    4 MiB budget is unused. -/
def STATE_TRACKER_AREA      : Word := 0xa0630000
/-- ASPIRATIONAL — `Stateless/VM/Message.lean` is scaffold-only. Emitted
    reality: per-frame slots live in `call_frame_arena` in `.data`
    (~164 MiB, `Codegen/CallFrameLayout.lean`), with the Phase-H/Phase-D
    ownership model in `Codegen/CallFramePhase.lean` /
    `Codegen/CallFrameWindows.lean`. -/
def EVM_FRAME_STACK         : Word := 0xa0a30000
/-- ASPIRATIONAL — emitted reality: the operand stack is per-frame inside
    `call_frame_arena` (32 KiB window per slot,
    `Codegen/CallFrameLayout.lean`). -/
def EVM_VALUE_STACK         : Word := 0xa0a70000
/-- ASPIRATIONAL — emitted reality: EVM memory is per-frame inside
    `call_frame_arena` (64 KiB window per slot,
    `Codegen/CallFrameLayout.lean`; dispatcher-era global `evm_memory`
    lives in `.data`). The `evmMemoryIs` assertion
    (`EvmAsm/Evm64/StateAssertions.lean`) is base-parametrized; only its
    `..._evmMemoryArea` convenience corollary targets this anchor and is
    therefore a port-contract statement, not an emitted-guest one. -/
def EVM_MEMORY_AREA         : Word := 0xa0b70000
/-- ASPIRATIONAL — emitted reality: keccak inputs are staged in `.data`
    scratch (`wlh_scratch_hash`, `mset_db_hash`, …) and via the ZisK
    keccak ECALL. -/
def KECCAK_SCRATCH          : Word := 0xa1b70000
/-- ASPIRATIONAL — emitted reality: ecrecover staging is `.data` scratch
    around the ZisK ECALL bridges. -/
def ECRECOVER_SCRATCH       : Word := 0xa1b80000
/-- ASPIRATIONAL — emitted reality: sha256 staging is `.data` scratch
    around the ZisK ECALL bridges. -/
def SHA256_SCRATCH          : Word := 0xa1b90000

/-! ## Read containers — the spec's three read sets (GH #10619)

    `state_tracker.py` keeps reads and writes in **separate containers with
    different lifetimes**, deliberately: at the pin `e5a8caf1b`, `BlockState`
    (`:67-77`) and `TransactionState` (`:96-104`) each carry

      `account_reads : Set[Address]`
      `storage_reads : Set[Tuple[Address, Bytes32]]`
      `code_reads    : Set[CodeRead]`

    and `restore_tx_state` (`:809-826`) restores **only** the write structures.
    The `TransactionState` docstring (`:90-93`) states the consequence in the
    spec's own words: these are *"shared references that survive rollback (reads
    from failed calls still appear in the Block Access List)"*.

    The guest previously had **no read container at all** — one array of
    128-byte rows (`STATE_TRACKER_AREA`) where a read was the *derived* case
    `current == original`. That collapse is what these regions remove: rollback
    truncates writes, and reads live here where rollback does not reach.

    **Three regions, not one merged set**, because the spec has three and the
    point of the change is to look the same. They are *not* parallel in purpose,
    which matters when wiring consumers:

      * `storage_reads` → `block_access_lists.py:692` `add_storage_read`
        → the BAL's `storage_reads` list.
      * `account_reads` → `block_access_lists.py:696` `add_touched_account`
        → decides **which accounts appear in the BAL at all**.
      * `code_reads`    → NOT the BAL. `stateless_host_exec_witness.py:182`
        `get_witness_codes` → execution-witness generation.

    Entry widths mirror the spec's tuples: a storage read is
    `addrHash(32) ++ slotKey(32)`, an account read is `addrHash(32)`, a code
    read is `addrHash(32) ++ codeHash(32)`. Capacities match the write log's
    16384 rows so a read container cannot overflow before the write log does. -/

/-- `storage_reads` — 16384 × 64 B (`addrHash ++ slotKey`). -/
def STORAGE_READS_AREA      : Word := 0xa1ba0000
/-- `account_reads` — 16384 × 32 B (`addrHash`). -/
def ACCOUNT_READS_AREA      : Word := 0xa1ca0000
/-- `code_reads` — 8192 × 64 B (`addrHash ++ codeHash`). -/
def CODE_READS_AREA         : Word := 0xa1d20000

/-! ## SSZ merkleization scratch region (large, NOBITS)

    The SSZ hash_tree_root buffers (merkleize scratch/padded, the byte
    packer, the list child-roots, and the versioned_hashes staging
    buffer) cannot live in the linked `.data` segment at `0xa0000000`:
    `.data` grows up into `OUTPUT_ADDR = 0xa0010000` (only ~64 KiB of
    headroom), which capped a single hashed element at 1024 B and
    blocked correct NewPayloadRequest roots for blocks with large
    transactions (~1 MiB) or block_access_list (~90 KiB).

    They are instead emitted into a dedicated NOBITS section placed by
    the linker at `SSZ_SCRATCH_BASE` (see `Driver.lean`'s
    `--section-start=.sszscratch=...`). NOBITS keeps the multi-MiB
    reservation out of the ELF file. The region sits above `.data`, clear of
    the working-RAM anchors and the stack, and fully inside the verified
    RAM zone `RAM_MEM_START..RAM_MEM_END` (`0xa0000000..0xc0000000`),
    so `isValidMemAddr` already accepts it (no proof changes). -/
def SSZ_SCRATCH_BASE        : Word := 0xbf980000
def SSZ_SCRATCH_SIZE        : Nat  := 0x00680000  -- 6.5 MiB (0xbf980000..0xc0000000)

end EvmAsm.Stateless
