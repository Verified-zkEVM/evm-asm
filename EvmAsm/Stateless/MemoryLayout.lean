/-
  EvmAsm.Stateless.MemoryLayout

  Single source of truth for the address-space layout used by the
  stateless-guest port of `run_stateless_guest`
  (`execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py`).

  All RISC-V modules under `EvmAsm/Stateless/` agree on the constants
  declared here. Treat this file as the contract: any new module must
  document, in its file header, which regions it reads, writes, and
  leaves untouched, plus which exit ECALLs it can take. Mirrors the
  "memory layout + side effects" convention already used by
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
  0xa3000000 .. 0xbf500000   .data (`-Tdata=0xa3000000`; static tables,
                             fixed data, and 1G-cap BSR/BAL arenas)
  0xa0010000 .. 0xa0020000   OUTPUT_ADDR (64 KiB, public output)
                               [+ 0..N]   SSZ-encoded
                                          SszStatelessValidationResult
  0xa0020000 .. 0xa3000000   working RAM (decoded structures, DBs,
                             frames) -- the Stateless guest claims this
                             lower tail of ziskemu's RAM region.
  0xbf500000 .. 0xbfb80000   .sszscratch NOBITS merkleization scratch
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

  (`EVM_MEMORY_AREA` budget is per-frame nominal; with max call depth
  1024 the precise per-frame slicing is tracked in `Stateless/VM/`.)

  ## EVM value-stack frame geometry (opcode scratch slack)

  The below-`sp` scratch opcodes (`EvmAsm/Evm64/{DivMod,SDiv,SMod,
  AddMod,Multiply}/`) place their workspace at negative offsets from
  `x12` (the EVM value-stack pointer): DivMod's call path reaches
  `sp - 152` (`divScratchValuesCallNoX1`,
  `EvmAsm/Evm64/DivMod/Compose/Base.lean:608-791`). For such `sp - K`
  scratch to be a valid in-frame address at *any* legal stack depth --
  including a full stack (`ptr = 1024`), where `sp` sits at the lowest
  slot -- each value-stack frame statically reserves a **scratch slack**
  margin (`STACK_SCRATCH_SLACK`, 256 B) immediately below its lowest
  slot. This closes the underflow caveat of #9450 by construction:
  `sp - STACK_SCRATCH_SLACK` is always a valid in-frame address.

  The EVM value stack is reset on each message CALL, so a single
  `EVM_VALUE_STACK_FRAME_BYTES` arena (`slack + 1024 x 32` = 33 024 B)
  is reused per frame; the parent's `x12` is saved on `EVM_FRAME_STACK`
  across the call. The slack therefore costs a single 256 B margin, not
  `max_call_depth x slack`. (The alternative full-nesting reservation
  `max_call_depth x EVM_VALUE_STACK_FRAME_BYTES` ~= 32 MiB does not fit
  the working-RAM window below `.data` at `0xa3000000`; see issue #9450.)

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

import EvmAsm.Rv64.Basic

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-! ## Working-RAM anchors (see table above). -/

def STATELESS_WORK_BASE     : Word := 0xa0020000
def SSZ_INPUT_DECODED       : Word := 0xa0020000
def EXECUTION_WITNESS_AREA  : Word := 0xa0030000
def NODE_DB_BUCKETS         : Word := 0xa0130000
def CODE_DB_BUCKETS         : Word := 0xa0530000
def STATE_TRACKER_AREA      : Word := 0xa0630000
def EVM_FRAME_STACK         : Word := 0xa0a30000
def EVM_VALUE_STACK         : Word := 0xa0a70000
def EVM_MEMORY_AREA         : Word := 0xa0b70000
def KECCAK_SCRATCH          : Word := 0xa1b70000
def ECRECOVER_SCRATCH       : Word := 0xa1b80000
def SHA256_SCRATCH          : Word := 0xa1b90000

/-! ## EVM value-stack frame geometry (opcode scratch slack, #9450)

   These constants parametrise the per-frame value-stack arena so that
   below-`sp` opcode scratch never underflows into a neighbour region.
   See the layout table above for the full rationale. The per-frame
   slicing / `sp` helpers built on these live in
   `EvmAsm/Stateless/VM/Stack.lean`. -/

/-- Number of 256-bit value-stack slots per EVM frame (Yellow Paper
    upper bound; `1024`). -/
def EVM_VALUE_STACK_SLOTS : Nat := 1024

/-- Bytes per value-stack slot -- a 256-bit word stored as 4 little-endian
    64-bit limbs. -/
def EVM_VALUE_SLOT_BYTES : Nat := 32

/-- Below-`sp` opcode scratch headroom, in bytes. Sized to the deepest
    below-`sp` reach of any opcode (DivMod call path: `sp - 152`,
    `divScratchValuesCallNoX1`) and rounded up to a 256-byte margin so
    that every scratch address stays dword-aligned and future opcodes
    that dig a little deeper than DivMod need no layout reflow. Change
    this single number to resize the slack. -/
def STACK_SCRATCH_SLACK : Nat := 256

/-- One value-stack frame: scratch slack (low) ++ `EVM_VALUE_STACK_SLOTS`
    slots (high). This is the per-frame arena that is reused across CALL
    boundaries. -/
def EVM_VALUE_STACK_FRAME_BYTES : Nat :=
  STACK_SCRATCH_SLACK + EVM_VALUE_STACK_SLOTS * EVM_VALUE_SLOT_BYTES

/-- Per-frame save-record slot count on `EVM_FRAME_STACK` (mirrors the
    256 B-per-frame reservation already documented in
    `Stateless/VM/Message.lean`). Kept here so disjointness lemmas can
    name the frame-stack extent. -/
def EVM_FRAME_STACK_RECORD_BYTES : Nat := 256

/-- Number of message-call frames the layout reserves room for
    (EIP-150 max call depth). -/
def EVM_MAX_CALL_DEPTH : Nat := 1024

/-! ## Working-RAM disjointness (#9450)

   `decide`-checked witnesses that the value-stack arena (slack + 1024
   slots) is inside the verified RAM zone and clear of its two working-RAM
   neighbours (`EVM_FRAME_STACK` below, `EVM_MEMORY_AREA` above). These
   are the load-bearing facts the per-frame `sp - STACK_SCRATCH_SLACK`
   guard in `Stateless/VM/Stack.lean` reduces to. -/

/-- The value-stack arena (slack + 1024 slots) fits inside the verified
    RAM zone `RAM_MEM_START .. RAM_MEM_END`. -/
theorem EVM_VALUE_STACK_arena_in_ram :
    RAM_MEM_START ≤ EVM_VALUE_STACK.toNat ∧
    EVM_VALUE_STACK.toNat + EVM_VALUE_STACK_FRAME_BYTES ≤ RAM_MEM_END := by
  decide

/-- The frame-stack region (`EVM_FRAME_STACK` + 256 KiB of per-frame
    save records) ends where the value-stack arena begins, so the two
    never overlap. -/
theorem EVM_FRAME_STACK_disjoint_VALUE_STACK :
    EVM_FRAME_STACK.toNat +
      EVM_MAX_CALL_DEPTH * EVM_FRAME_STACK_RECORD_BYTES ≤ EVM_VALUE_STACK.toNat := by
  decide

/-- The value-stack arena (slack + 1024 slots) stays clear of the EVM
    memory area above it. -/
theorem EVM_VALUE_STACK_arena_disjoint_MEMORY_AREA :
    EVM_VALUE_STACK.toNat + EVM_VALUE_STACK_FRAME_BYTES ≤ EVM_MEMORY_AREA.toNat := by
  decide

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
def SSZ_SCRATCH_BASE        : Word := 0xbf500000
def SSZ_SCRATCH_SIZE        : Nat  := 0x00680000  -- 6.5 MiB (0xbf500000..0xbfb80000)

end EvmAsm.Stateless
