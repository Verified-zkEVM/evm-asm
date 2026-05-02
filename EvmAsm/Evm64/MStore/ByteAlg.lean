/-
  EvmAsm.Evm64.MStore.ByteAlg

  Pure Word-level identities used by the upcoming MSTORE per-limb spec
  (`docs/99-mstore-design.md` §6 sub-slice 4b, beads `evm-asm-pq0e`).

  The MSTORE per-limb byte-unpack (§3.2 of the design) processes bytes
  big-endian: for each `k ∈ {0..7}`, the runtime computes
  `byteSrc := accVal >>> ((7-k)*8)` via `SRLI` and then `SB` writes the
  low 8 bits of `byteSrc` to memory. The relevant identity bridging the
  runtime SRLI form to the abstract `extractByte` form is
  `extractByte (accVal >>> n) 0 = extractByte accVal (n / 8)` (when
  `n` is a multiple of 8 between 0 and 56).

  This file exposes that identity as `extractByte_shr_zero` (and a
  convenience `extractByte_def` re-stating the definitional unfolding
  used by the design note). Standalone — no dependence on machine state,
  separation logic, or the `Program`. Consumed by sub-slice 4c
  (`mstore_byte_unpack_step_spec`) when bridging the runtime
  shift-then-SB form to the static `extractByte` reads in the
  postcondition.

  The MLOAD dual `bytePack8_eq` lives in `Evm64/MLoad/ByteAlg.lean`. If
  later opcodes (e.g. CALLDATALOAD, RETURNDATACOPY) need both, see
  `docs/99-mstore-design.md` §8 follow-up about a shared
  `Evm64/ByteAlg.lean`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/
import EvmAsm.Rv64.Basic
import Std.Tactic.BVDecide
import Mathlib.Tactic.IntervalCases

namespace EvmAsm.Evm64.MStore

open EvmAsm.Rv64

/--
  Definitional re-statement of `extractByte`: the byte at position `i`
  is the low 8 bits of `w >>> (i*8)`.

  This is `rfl` against the definition in `Rv64/Basic.lean`, but
  exposing it as a named lemma lets per-limb spec proofs rewrite from
  the runtime SRLI shape to the abstract `extractByte` form without
  having to `unfold extractByte` (which can interfere with
  `seqFrame` / `xperm` plumbing).
-/
theorem extractByte_def (w : Word) (i : Nat) :
    extractByte w i = (w >>> (i * 8)).truncate 8 := rfl

/--
  **`extractByte (w >>> (i*8)) 0 = extractByte w i`** for `i ∈ {0..7}`.

  Bridges the runtime form produced by `SRLI byteReg accReg (i*8)`
  followed by `SB addrReg byteReg _` (which writes the low 8 bits of
  `byteReg`, i.e. `extractByte byteReg 0`) to the abstract big-endian
  byte view `extractByte accReg i`.

  Proved by `bv_decide` after a finite case-split on `i`.
-/
theorem extractByte_shr_zero (w : Word) (i : Nat) (h : i < 8) :
    extractByte (w >>> (i * 8)) 0 = extractByte w i := by
  -- Eight cases on `i` fully decide via `bv_decide`.
  interval_cases i <;> (simp only [extractByte_def, Nat.zero_mul]; bv_decide)

/--
  Convenience corollary specialised to the `(7 - k)` shape used in the
  MSTORE per-limb program (which loads the most-significant byte first):
  `extractByte (w >>> ((7-k)*8)) 0 = extractByte w (7-k)` for `k ∈ {0..7}`.

  Stated separately so callers don't have to re-derive the bound on
  `7 - k` at every call site.
-/
theorem extractByte_shr_zero_descending (w : Word) (k : Nat) (h : k < 8) :
    extractByte (w >>> ((7 - k) * 8)) 0 = extractByte w (7 - k) := by
  have : 7 - k < 8 := by omega
  exact extractByte_shr_zero w (7 - k) this

/--
  Truncation form of `extractByte_shr_zero_descending`, matching the value
  consumed by the runtime `SB` after `SRLI`.
-/
theorem extractByte_shr_zero_descending_truncate (w : Word) (k : Nat) (h : k < 8) :
    (w >>> ((7 - k) * 8)).truncate 8 = extractByte w (7 - k) := by
  rw [← extractByte_shr_zero_descending w k h]
  rfl

/-- Select the destination dword address for byte `i` in an unaligned
    8-byte MSTORE limb window. -/
def mstoreDwordPairAddr (loAddr hiAddr : Word) (start i : Nat) : Word :=
  if start + i < 8 then loAddr else hiAddr

theorem mstoreDwordPairAddr_low
    (loAddr hiAddr : Word) {start i : Nat} (h_pos : start + i < 8) :
    mstoreDwordPairAddr loAddr hiAddr start i = loAddr := by
  simp [mstoreDwordPairAddr, h_pos]

theorem mstoreDwordPairAddr_high
    (loAddr hiAddr : Word) {start i : Nat} (h_pos : 8 ≤ start + i) :
    mstoreDwordPairAddr loAddr hiAddr start i = hiAddr := by
  simp [mstoreDwordPairAddr, show ¬ start + i < 8 from by omega]

/--
  Replace byte `i` of an unaligned 8-byte MSTORE limb window spanning two
  adjacent destination dwords. `start` is the byte offset of the first limb
  byte within `lo`.
-/
def mstoreDwordPairReplaceByte
    (lo hi : Word) (start i : Nat) (b : BitVec 8) : Word × Word :=
  let pos := start + i
  if pos < 8 then
    (replaceByte lo (pos % 8) b, hi)
  else
    (lo, replaceByte hi (pos % 8) b)

theorem mstoreDwordPairReplaceByte_low
    (lo hi : Word) {start i : Nat} (b : BitVec 8) (h_pos : start + i < 8) :
    mstoreDwordPairReplaceByte lo hi start i b =
      (replaceByte lo ((start + i) % 8) b, hi) := by
  simp [mstoreDwordPairReplaceByte, h_pos]

theorem mstoreDwordPairReplaceByte_high
    (lo hi : Word) {start i : Nat} (b : BitVec 8) (h_pos : 8 ≤ start + i) :
    mstoreDwordPairReplaceByte lo hi start i b =
      (lo, replaceByte hi ((start + i) % 8) b) := by
  simp [mstoreDwordPairReplaceByte, show ¬ start + i < 8 from by omega]

end EvmAsm.Evm64.MStore
