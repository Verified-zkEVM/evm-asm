/-
  EvmAsm.Evm64.MStore.Program

  256-bit EVM `MSTORE`: pop a 32-byte `offset` and a 32-byte `value` from
  the EVM stack, then write `value` (big-endian) to 32 contiguous bytes
  of EVM memory starting at byte address `memBase + offset_lo`. Net EVM
  stack movement: `+64` (two 32-byte pops, no push).

  This slice is **program-only**, mirroring the shape of
  `EvmAsm/Evm64/MLoad/Program.lean`. The byte-extract identity, per-byte
  / per-limb composition specs, and the eventual
  `evm_mstore_stack_spec_within` land in follow-up sub-slices per
  `docs/99-mstore-design.md` §6 (sub-slices 4b..4f).

  Layout (98 instructions = 392 bytes):

    prologue (2 instr):
      LD   offReg     x12  0           -- low limb of `offset` (high 3
                                       -- limbs assumed 0 by the spec
                                       -- precondition; see design §3.5)
      ADD  addrReg    memBaseReg offReg
                                       -- base byte address of the
                                       -- 32-byte write window

    per limb j ∈ {0, 1, 2, 3} (23 instr each — 92 total):
      LD   accReg     x12   (8 * j + 32)             -- load limb j of value
      SRLI byteReg    accReg ((7 - 0) * 8)
      SB   addrReg    byteReg (8 * (3 - j) + 0)      -- write MSB of limb j
      SRLI byteReg    accReg ((7 - 1) * 8)
      SB   addrReg    byteReg (8 * (3 - j) + 1)
      ...                                            -- 7 more (SRLI + SB)
      SRLI byteReg    accReg 0  ;; SB addrReg byteReg (8 * (3 - j) + 7)

    epilogue (1 instr):
      ADDI .x12 .x12 64                              -- pop both 32-byte words

  Big-endian per-limb ordering (`offset+0` is the MSB of EVM word):

    EVM memory byte `off + k` (`k = 0..31`) receives the byte at
    position `7 - k%8` of RV64 limb `3 - k/8`. That is, the high RV64
    limb (`sp_evm + 24 + 32`) carries the most-significant 8 bytes of
    the EVM word and the low limb (`sp_evm + 0 + 32`) carries the
    least-significant 8 bytes (little-endian limbs of a big-endian
    word). See `docs/99-mstore-design.md` §3.1.

  Per-byte instruction pattern is **(a) shift-then-store** per design
  §3.2: `acc` stays invariant for the whole limb; `byteReg` is the
  per-byte SRLI scratch. This matches MLOAD's load-then-shift-then-OR
  shape so the per-byte specs share a uniform `runBlock` structure.

  Register convention (all caller-saved temporaries per LP64; see
  `AGENTS.md` "Calling Convention (LP64)"):

    `offReg`     — receives the low 64 bits of the popped `offset`.
    `valReg`     — currently unused at the program level (the per-limb
                   loads go directly into `accReg`); reserved for a
                   future variant that pre-loads all four value limbs.
    `byteReg`    — scratch for the per-byte `SRLI` result.
    `accReg`     — running per-limb value, freshly loaded for each
                   limb.
    `addrReg`    — scratch holding `memBaseReg + offReg`.
    `memBaseReg` — caller-supplied EVM memory buffer base address.

  The caller is expected to choose distinct registers for the scratch
  roles and to keep `memBaseReg` alive across the call. The spec slice
  (`evm_mstore_stack_spec_within`) will pin down the exact disjointness
  side conditions.

  Memory-expansion bookkeeping (`evmMemSizeIs` update) is **not**
  performed by this program; it will either be lifted to the spec
  precondition or added in a later sub-slice (cf.
  `docs/99-mstore-design.md` §4 and the parallel MLOAD discussion).

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Unpack `k+1` bytes of `accReg` (the current limb value) into EVM
    memory starting at `addrReg + limbStart`, big-endian.

    `limbStart` is the byte-offset, inside the 32-byte write window, of
    the most-significant byte of the limb being disassembled (i.e.
    `8 * (3 - j)` for limb `j`). For byte index `i` (`0 ≤ i ≤ k`) the
    pattern is

      SRLI byteReg accReg ((7 - i) * 8)
      SB   addrReg byteReg (limbStart + i)

    so byte `0` (the MSB of the limb) lands at `limbStart` and byte `k`
    lands at `limbStart + k`. The recursion shape mirrors
    `Evm64.MLoad.mload_byte_pack`: emitting one byte at a time so a
    single uniform per-byte block can be unfolded by the spec slices.

    `accReg` must differ from `byteReg`; the spec slice will enforce
    this via a `Reg` disjointness hypothesis. -/
private def mstore_byte_unpack
    (addrReg byteReg accReg : Reg) (limbStart : Nat) : Nat → Program
  | 0     =>
      SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 0) * 8)) ;;
      SB addrReg byteReg (BitVec.ofNat 12 (limbStart + 0))
  | k + 1 =>
      mstore_byte_unpack addrReg byteReg accReg limbStart k ;;
      SRLI byteReg accReg (BitVec.ofNat 6 ((7 - (k + 1)) * 8)) ;;
      SB addrReg byteReg (BitVec.ofNat 12 (limbStart + (k + 1)))

/-- Load one EVM-stack input limb (`limb j` of `value`) and unpack its 8
    bytes (big-endian) into EVM memory at the canonical write window
    offset `8 * (3 - j)`.

    For `j = 0` (the low limb) the MSB lives at byte `(off + 24)` of the
    EVM word (so `limbStart = 24`); for `j = 3` (the high limb) the MSB
    lives at byte `(off + 0)`, i.e. `limbStart = 0`. The general
    formula is `limbStart = 8 * (3 - j)`. The value limb is read from
    `x12 + 8 * j + 32` (top-of-stack `value` lives 32 bytes below
    `offset`). -/
private def mstore_one_limb
    (addrReg byteReg accReg : Reg) (j : Nat) : Program :=
  LD accReg .x12 (BitVec.ofNat 12 (8 * j + 32)) ;;
  mstore_byte_unpack addrReg byteReg accReg (8 * (3 - j)) 7

/-- 256-bit EVM `MSTORE` program.

    Pops a 32-byte `offset` from the EVM stack at `x12 + 0`, a 32-byte
    `value` at `x12 + 32`, and writes `value` (big-endian) to 32 bytes
    of EVM memory starting at `memBaseReg + offset_lo`. The high three
    limbs of `offset` must be zero (spec precondition; no runtime
    check). The EVM-stack pointer is advanced by 64 (both 32-byte words
    popped).

    `valReg` is currently a placeholder (not emitted) — the per-limb
    loads target `accReg` directly. It is kept in the parameter list to
    match the design-note signature so spec slices can introduce it
    without changing call sites. -/
def evm_mstore (offReg valReg byteReg accReg addrReg memBaseReg : Reg) :
    Program :=
  let _ := valReg
  LD offReg .x12 0 ;;
  ADD addrReg memBaseReg offReg ;;
  mstore_one_limb addrReg byteReg accReg 0 ;;
  mstore_one_limb addrReg byteReg accReg 1 ;;
  mstore_one_limb addrReg byteReg accReg 2 ;;
  mstore_one_limb addrReg byteReg accReg 3 ;;
  ADDI .x12 .x12 (BitVec.ofNat 12 64)

/-- `CodeReq` for `evm_mstore` placed at `base`. -/
abbrev evm_mstore_code
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    CodeReq :=
  CodeReq.ofProg base (evm_mstore offReg valReg byteReg accReg addrReg memBaseReg)

end EvmAsm.Evm64
