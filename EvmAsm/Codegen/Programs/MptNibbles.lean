/-
  EvmAsm.Codegen.Programs.MptNibbles

  Nibble ↔ compact-encoding helpers carved out of
  `EvmAsm.Codegen.Programs.MptInternal` per the file-size hard
  cap. Hosts:

    K109  mpt_nibbles_to_compact
    K110  mpt_compact_to_nibbles

  Self-contained byte-level helpers — no external Function
  dependencies beyond `Rv64.Program` and `Codegen.Layout`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## mpt_nibbles_to_compact -- PR-K109

    Pack a nibble-list into the MPT compact (hex-prefix) encoding
    used in leaf and extension node first fields.

    Matches `nibble_list_to_compact(nibbles, is_leaf)` in
    `forks/amsterdam/trie.py`.

    The output's first byte has its high nibble structured as:

        +---+---+----------+--------+
        | _ | _ | is_leaf | parity |
        +---+---+----------+--------+
          3   2      1         0

    The low nibble of the prefix is either:
    - 0 when the input has even length
    - the first nibble of the input when odd length

    Remaining nibbles are then packed two-per-byte, high nibble
    first.

    Output length = `nibble_count / 2 + 1`, regardless of parity:
    - `nibble_count=0` → 1 byte (prefix only)
    - `nibble_count=1` → 1 byte (prefix carries the lone nibble)
    - `nibble_count=2` → 2 bytes
    - `nibble_count=3` → 2 bytes
    - …

    Calling convention:
      a0 (input)  : nibbles ptr (each byte 0..15)
      a1 (input)  : nibble count
      a2 (input)  : is_leaf flag (0 or 1)
      a3 (input)  : output bytes ptr (caller supplies space)
      a4 (input)  : u64 out ptr (writes output byte length)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function).

    Pure-leaf semantics: no scratch memory, no transitive calls.
    Callers are responsible for ensuring each input byte is in
    `[0, 15]`; out-of-range bytes get truncated to their low
    nibble. -/
def mptNibblesToCompact_prog : Program :=
  [ .ANDI .x5 .x11 (1 : BitVec 12),
    .SLLI .x6 .x12 (1 : BitVec 6),
    .OR .x6 .x6 .x5,
    .BEQ .x5 .x0 (32 : BitVec 13),
    .LBU .x28 .x10 (0 : BitVec 12),
    .SLLI .x7 .x6 (4 : BitVec 6),
    .ANDI .x28 .x28 (15 : BitVec 12),
    .OR .x7 .x7 .x28,
    .ADDI .x29 .x10 (1 : BitVec 12),
    .ADDI .x30 .x11 (-1 : BitVec 12),
    .JAL .x0 (16 : BitVec 21),
    .SLLI .x7 .x6 (4 : BitVec 6),
    .MV .x29 .x10,
    .MV .x30 .x11,
    .SB .x13 .x7 (0 : BitVec 12),
    .ADDI .x31 .x13 (1 : BitVec 12),
    .BEQ .x30 .x0 (48 : BitVec 13),
    .LBU .x5 .x29 (0 : BitVec 12),
    .LBU .x6 .x29 (1 : BitVec 12),
    .ANDI .x5 .x5 (15 : BitVec 12),
    .ANDI .x6 .x6 (15 : BitVec 12),
    .SLLI .x5 .x5 (4 : BitVec 6),
    .OR .x5 .x5 .x6,
    .SB .x31 .x5 (0 : BitVec 12),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADDI .x29 .x29 (2 : BitVec 12),
    .ADDI .x30 .x30 (-2 : BitVec 12),
    .JAL .x0 (-44 : BitVec 21),
    .SRLI .x5 .x11 (1 : BitVec 6),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .SD .x14 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def mptNibblesToCompactFunction : String :=
  "mpt_nibbles_to_compact:\n" ++ emitProgram mptNibblesToCompact_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `mptNibblesToCompact_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem mptNibblesToCompactFunction_eq_prog :
    mptNibblesToCompactFunction = "mpt_nibbles_to_compact:\n" ++ emitProgram mptNibblesToCompact_prog := rfl

#guard mptNibblesToCompactFunction.startsWith "mpt_nibbles_to_compact:\n"
/-- `zisk_mpt_nibbles_to_compact`: probe BuildUnit. Reads
    (nibble_count, is_leaf, nibble_bytes) from host input, writes
    (status, output_len, compact_bytes...) to OUTPUT.
    Input layout:
      bytes  0.. 8 : nibble count
      bytes  8..16 : is_leaf flag (0/1)
      bytes 16..   : nibble bytes (one nibble per byte)
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : output_len
      bytes 16..   : compact-encoded bytes -/
def ziskMptNibblesToCompactPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # nibble count\n" ++
  "  ld a2, 16(a5)               # is_leaf\n" ++
  "  addi a0, a5, 24             # nibbles ptr\n" ++
  "  li a3, 0xa0010010           # output bytes\n" ++
  "  li a4, 0xa0010008           # output_len out\n" ++
  "  jal ra, mpt_nibbles_to_compact\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmnc_pdone\n" ++
  mptNibblesToCompactFunction ++ "\n" ++
  ".Lmnc_pdone:"

def ziskMptNibblesToCompactDataSection : String :=
  ".section .data\n" ++
  "mnc_scratch:\n" ++
  "  .zero 8"


/-! ## mpt_compact_to_nibbles -- PR-K110

    Decode the MPT compact (hex-prefix) encoding back to a nibble
    list and an `is_leaf` flag. The inverse of PR-K109
    `mpt_nibbles_to_compact`.

    Matches `compact_to_nibbles` in
    `forks/amsterdam/incremental_mpt.py`.

    The compact form's first byte high nibble structure:

        +---+---+----------+--------+
        | _ | _ | is_leaf | parity |
        +---+---+----------+--------+
          3   2      1         0

    Parity = 1 → first nibble of the path lives in the low nibble
    of the prefix byte; parity = 0 → prefix's low nibble is 0 and
    the path is fully packed in bytes 1..end.

    Output nibble count:
    - even-parity input of byte-length L → 2 × (L - 1) nibbles
    - odd-parity input of byte-length L → 2 × L - 1 nibbles

    Calling convention:
      a0 (input)  : compact bytes ptr
      a1 (input)  : compact byte length
      a2 (input)  : nibbles output ptr (≥ 2×L bytes of space)
      a3 (input)  : u64 out ptr (nibble count)
      a4 (input)  : u64 out ptr (is_leaf flag: 0 or 1)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty input (L = 0; no prefix byte to read)

    Pure-leaf semantics: no scratch memory, no transitive calls.
    Counter and flag outputs are zeroed on failure. -/
def mptCompactToNibbles_prog : Program :=
  [ .SD .x13 .x0 (0 : BitVec 12),
    .SD .x14 .x0 (0 : BitVec 12),
    .BEQ .x11 .x0 (120 : BitVec 13),
    .LBU .x5 .x10 (0 : BitVec 12),
    .SRLI .x6 .x5 (4 : BitVec 6),
    .ANDI .x7 .x6 (2 : BitVec 12),
    .SRLI .x7 .x7 (1 : BitVec 6),
    .SD .x14 .x7 (0 : BitVec 12),
    .ANDI .x28 .x6 (1 : BitVec 12),
    .MV .x29 .x12,
    .LI .x30 (0 : Word),
    .BEQ .x28 .x0 (20 : BitVec 13),
    .ANDI .x31 .x5 (15 : BitVec 12),
    .SB .x29 .x31 (0 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x31 .x10 (1 : BitVec 12),
    .ADDI .x6 .x11 (-1 : BitVec 12),
    .BEQ .x6 .x0 (44 : BitVec 13),
    .LBU .x5 .x31 (0 : BitVec 12),
    .SRLI .x7 .x5 (4 : BitVec 6),
    .ANDI .x28 .x5 (15 : BitVec 12),
    .SB .x29 .x7 (0 : BitVec 12),
    .SB .x29 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (2 : BitVec 12),
    .ADDI .x30 .x30 (2 : BitVec 12),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-40 : BitVec 21),
    .SD .x13 .x30 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def mptCompactToNibblesFunction : String :=
  "mpt_compact_to_nibbles:\n" ++ emitProgram mptCompactToNibbles_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `mptCompactToNibbles_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem mptCompactToNibblesFunction_eq_prog :
    mptCompactToNibblesFunction = "mpt_compact_to_nibbles:\n" ++ emitProgram mptCompactToNibbles_prog := rfl

#guard mptCompactToNibblesFunction.startsWith "mpt_compact_to_nibbles:\n"
/-- `zisk_mpt_compact_to_nibbles`: probe BuildUnit. Reads
    (compact_len, compact_bytes) from host input, writes
    (status, nibble_count, is_leaf, nibbles...) to OUTPUT.
    Input layout:
      bytes  0.. 8 : compact byte length
      bytes  8..   : compact-encoded bytes
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : nibble count
      bytes 16..24 : is_leaf flag
      bytes 24..   : N nibble bytes -/
def ziskMptCompactToNibblesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # compact length\n" ++
  "  addi a0, a5, 16             # compact bytes\n" ++
  "  li a2, 0xa0010018           # nibbles output (OUTPUT + 0x18)\n" ++
  "  li a3, 0xa0010008           # nibble count out\n" ++
  "  li a4, 0xa0010010           # is_leaf out\n" ++
  "  jal ra, mpt_compact_to_nibbles\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmctn_pdone\n" ++
  mptCompactToNibblesFunction ++ "\n" ++
  ".Lmctn_pdone:"

def ziskMptCompactToNibblesDataSection : String :=
  ".section .data\n" ++
  "mctn_scratch:\n" ++
  "  .zero 8"



end EvmAsm.Codegen
