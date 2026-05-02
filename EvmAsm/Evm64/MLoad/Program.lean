/-
  EvmAsm.Evm64.MLoad.Program

  256-bit EVM `MLOAD`: read 32 contiguous bytes from EVM memory at byte
  offset `offset` and push the resulting big-endian 256-bit word onto
  the EVM stack (replacing the popped `offset` operand — net zero stack
  movement).

  This slice is **program-only**, mirroring the shape of
  `EvmAsm/Evm64/MStore8/Program.lean`. The spec proof, byte-pack
  identity (`bytePack8_eq`), per-byte/per-limb composition specs, and
  the eventual `evm_mload_stack_spec_within` land in follow-up
  sub-slices per `docs/99-mload-design.md` §6 (sub-slices 3b..3f).

  Layout (94 instructions = 376 bytes):

    prologue (2 instr):
      LD   offReg     x12  0           -- low limb of `offset` (high 3
                                       -- limbs assumed 0 by the spec
                                       -- precondition; see §3.5 of the
                                       -- design note)
      ADD  addrReg    memBaseReg offReg
                                       -- base byte address of the
                                       -- 32-byte read

    per limb j ∈ {0, 1, 2, 3} (23 instr each — 92 total):
      LBU  accReg     addrReg  (8*(3-j) + 0)         -- MSB of limb j
      LBU  byteReg    addrReg  (8*(3-j) + 1)
      SLLI accReg     accReg   8 ;; OR accReg accReg byteReg
      ...                                            -- 7 (LBU+SLLI+OR)
      LBU  byteReg    addrReg  (8*(3-j) + 7)
      SLLI accReg     accReg   8 ;; OR accReg accReg byteReg
      SD   x12        accReg   (8 * j)               -- store packed limb

    epilogue: none (`x12` unchanged: pop offset + push value of equal width).

  Big-endian per-limb ordering (`offset+0` is the MSB of EVM word):

    EVM memory byte `off + k` (`k = 0..31`) goes into RV64 limb `3 - k/8`
    at byte-position `7 - k%8`, i.e. limb `lo = sp+0` carries the
    least-significant 8 bytes of the EVM word and `hi = sp+24` carries
    the most-significant 8 bytes (little-endian limbs of a big-endian
    word). See `docs/99-mload-design.md` §3.1.

  Register convention (all caller-saved temporaries per LP64; see
  `AGENTS.md` "Calling Convention (LP64)"):

    `offReg`     — receives the low 64 bits of the popped `offset`.
    `byteReg`    — scratch for the per-byte LBU result.
    `accReg`     — running per-limb accumulator; freshly overwritten by
                   the limb-leading LBU (no zero-init needed).
    `addrReg`    — scratch holding `memBaseReg + offReg`.
    `memBaseReg` — caller-supplied EVM memory buffer base address.

  The caller is expected to choose distinct registers for the four
  scratch roles and to keep `memBaseReg` alive across the call. The
  spec slice (`evm_mload_stack_spec_within`) will pin down the exact
  disjointness side conditions.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Pack `k+1` bytes from EVM memory (starting at `addrReg + limbStart`
    big-endian) into `accReg`.

    `limbStart` is the byte-offset, inside the 32-byte read window, of
    the most-significant byte of the limb being assembled (i.e.
    `8 * (3 - j)` for limb `j`).

    The recursion shape mirrors `Evm64.Push.push_bytes`: building one
    byte at a time so a single uniform per-byte block can be unfolded
    by the spec slices. Byte index `0` is the MSB of the limb, so it
    initialises `accReg` directly via `LBU` (no shift required); each
    subsequent byte left-shifts the running accumulator by 8 and ORs in
    the next byte.

    `accReg` must differ from `byteReg`; the spec slice will enforce
    this via a `Reg` disjointness hypothesis. -/
private def mload_byte_pack
    (addrReg byteReg accReg : Reg) (limbStart : Nat) : Nat → Program
  | 0     =>
      LBU accReg addrReg (BitVec.ofNat 12 limbStart)
  | k + 1 =>
      mload_byte_pack addrReg byteReg accReg limbStart k ;;
      LBU byteReg addrReg (BitVec.ofNat 12 (limbStart + (k + 1))) ;;
      SLLI accReg accReg (BitVec.ofNat 6 8) ;;
      OR' accReg accReg byteReg

/-- Pack one EVM-stack output limb (`limb j`) and store it at the
    canonical EVM-stack offset `sp_evm + 8 * j`.

    For `j = 0` (the low limb) the MSB lives at byte `(off + 24)` of the
    EVM word (so `limbStart = 24`); for `j = 3` (the high limb) the MSB
    lives at byte `(off + 0)`, i.e. `limbStart = 0`. The general
    formula is `limbStart = 8 * (3 - j)`. -/
private def mload_one_limb
    (addrReg byteReg accReg : Reg) (j : Nat) : Program :=
  mload_byte_pack addrReg byteReg accReg (8 * (3 - j)) 7 ;;
  SD .x12 accReg (BitVec.ofNat 12 (8 * j))

/-- 256-bit EVM `MLOAD` program.

    Pops a 32-byte `offset` from the EVM stack at `x12`, reads 32 bytes
    from EVM memory at byte address `memBaseReg + offset_lo` (the high
    three limbs of `offset` must be zero — spec precondition; no
    runtime check), and writes the resulting big-endian 256-bit word
    back to the same EVM-stack slot at `x12`. The EVM-stack pointer is
    unchanged (one pop + one push of equal width).

    Memory expansion bookkeeping (`evmMemSizeIs` update) is **not**
    performed by this program; it will either be lifted to the spec
    precondition or added in a later sub-slice (see
    `docs/99-mload-design.md` §4). -/
def evm_mload (offReg byteReg accReg addrReg memBaseReg : Reg) : Program :=
  LD offReg .x12 0 ;;
  ADD addrReg memBaseReg offReg ;;
  mload_one_limb addrReg byteReg accReg 0 ;;
  mload_one_limb addrReg byteReg accReg 1 ;;
  mload_one_limb addrReg byteReg accReg 2 ;;
  mload_one_limb addrReg byteReg accReg 3

/-- `CodeReq` for `evm_mload` placed at `base`. -/
abbrev evm_mload_code
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_mload offReg byteReg accReg addrReg memBaseReg)

/-- Concrete instruction length of `mload_byte_pack`.

    `k = 0` is the seed `LBU`; each successor adds one `LBU; SLLI; OR`
    step, so the length is `1 + 3*k`. -/
theorem mload_byte_pack_length
    (addrReg byteReg accReg : Reg) (limbStart k : Nat) :
    (mload_byte_pack addrReg byteReg accReg limbStart k).length = 1 + 3 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [mload_byte_pack, LBU, SLLI, OR', single, seq,
        Program.length_append, ih, Nat.mul_succ]
      omega

/-- Concrete instruction length of one MLOAD limb block. -/
theorem mload_one_limb_length (addrReg byteReg accReg : Reg) (j : Nat) :
    (mload_one_limb addrReg byteReg accReg j).length = 23 := by
  simp [mload_one_limb, SD, single, seq, Program.length_append,
    mload_byte_pack_length]

/-- Concrete instruction length of `evm_mload`. -/
theorem evm_mload_length (offReg byteReg accReg addrReg memBaseReg : Reg) :
    (evm_mload offReg byteReg accReg addrReg memBaseReg).length = 94 := by
  simp [evm_mload, LD, ADD, single, seq, Program.length_append,
    mload_one_limb_length]

/-- Concrete byte length of `evm_mload` when placed in RV64 code memory. -/
theorem evm_mload_byte_length (offReg byteReg accReg addrReg memBaseReg : Reg) :
    4 * (evm_mload offReg byteReg accReg addrReg memBaseReg).length = 376 := by
  rw [evm_mload_length]

/-- Byte offset of the MLOAD offset-load instruction. -/
theorem evm_mload_offset_load_byte_off : 4 * 0 = 0 := by
  rfl

/-- Byte offset of the MLOAD address-add instruction. -/
theorem evm_mload_addr_add_byte_off : 4 * 1 = 4 := by
  rfl

/-- Byte offset of MLOAD limb block `j` within `evm_mload`. -/
theorem evm_mload_limb_block_byte_off (j : Nat) :
    4 * (2 + 23 * j) = 8 + 92 * j := by
  omega

/-- Byte offset of the final stack-store instruction in MLOAD limb block `j`. -/
theorem evm_mload_limb_store_byte_off (j : Nat) :
    4 * (2 + 23 * j + 22) = 96 + 92 * j := by
  omega

/-- Byte offset immediately after the full MLOAD program. -/
theorem evm_mload_end_byte_off : 4 * 94 = 376 := by
  rfl

end EvmAsm.Evm64
