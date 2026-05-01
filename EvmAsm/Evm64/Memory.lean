/-
  EvmAsm.Evm64.Memory

  Separation logic model for EVM memory (byte-addressable, zero-initialized,
  dynamically expandable) stored in RV64IM doubleword-aligned memory cells.

  Slice 1 (issue #99): defines the core `evmMemIs` assertion at dword-cell
  granularity plus the zero-initialized form `evmMemZero`.

  Slice 2 (issue #99): tracks the EVM memory high-water mark in a single
  scratch dword cell via `evmMemSizeIs`, and provides the pure expansion
  helper `evmMemExpand` that computes the new byte-size after an access of
  `(offset, length)`, rounded up to a 32-byte-word boundary as the EVM-spec
  requires. Subsequent slices wire this into MLOAD/MSTORE/MSTORE8 (slices
  3-5) and MSIZE (slice 6).

  Design choices (kept minimal for this slice):

  * EVM memory is modelled as a sequence of 64-bit cells, each owning eight
    consecutive bytes. Byte-level access (MSTORE8 / MLOAD at unaligned
    offsets) will be lifted on top of `evmMemIs` in later slices via the
    `ByteOps.lean` LBU/SB byte-level specs, which already operate on the
    underlying `↦ₘ` dword cells.
  * `numCells` is the dword (8-byte) count. The corresponding EVM byte size
    is `8 * numCells`. EVM memory expansion in the spec is in 32-byte words,
    which is a constraint enforced by the consumers (MSTORE/MLOAD specs),
    not by `evmMemIs` itself.
  * `contents : Nat → Word` is a pure function rather than a `ByteArray`
    so the assertion is total in `Nat` index — out-of-range indices simply
    have no cell asserted (they sit outside the sepConj chain). This
    matches how `evmStackIs` uses a `List EvmWord`.
-/

import EvmAsm.Evm64.Basic
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- `evmMemIs base numCells contents` asserts that `numCells` consecutive
    8-byte memory cells starting at `base` hold the values `contents 0 ..
    contents (numCells-1)`. The cells are stored at byte offsets
    `base + 0, base + 8, ..., base + 8*(numCells-1)`.

    This is the dword-cell view of EVM memory. Byte-level reads/writes are
    lifted on top via the `ByteOps.lean` LBU/SB specs in later slices. -/
def evmMemIs (base : Word) (numCells : Nat) (contents : Nat → Word) : Assertion :=
  match numCells with
  | 0     => empAssertion
  | n + 1 =>
      evmMemIs base n contents ** ((base + (BitVec.ofNat 64 (8 * n))) ↦ₘ contents n)

/-- The zero-initialized EVM memory region: `numCells` dword cells, all 0.
    Models the EVM-spec invariant that unwritten memory reads as zero. -/
def evmMemZero (base : Word) (numCells : Nat) : Assertion :=
  evmMemIs base numCells (fun _ => 0)

@[simp] theorem evmMemIs_zero {base : Word} {contents : Nat → Word} :
    evmMemIs base 0 contents = empAssertion := rfl

theorem evmMemIs_succ {base : Word} {n : Nat} {contents : Nat → Word} :
    evmMemIs base (n + 1) contents =
      (evmMemIs base n contents ** ((base + (BitVec.ofNat 64 (8 * n))) ↦ₘ contents n)) := rfl

@[simp] theorem evmMemZero_zero {base : Word} :
    evmMemZero base 0 = empAssertion := rfl

theorem evmMemZero_succ {base : Word} {n : Nat} :
    evmMemZero base (n + 1) =
      (evmMemZero base n ** ((base + (BitVec.ofNat 64 (8 * n))) ↦ₘ 0)) := rfl

/-! ## pcFree -/

theorem pcFree_evmMemIs {base : Word} {n : Nat} {contents : Nat → Word} :
    (evmMemIs base n contents).pcFree := by
  induction n with
  | zero => exact pcFree_emp
  | succ k ih =>
      rw [evmMemIs_succ]
      exact pcFree_sepConj ih pcFree_memIs

theorem pcFree_evmMemZero {base : Word} {n : Nat} :
    (evmMemZero base n).pcFree := by
  unfold evmMemZero; exact pcFree_evmMemIs

instance (base : Word) (n : Nat) (contents : Nat → Word) :
    Assertion.PCFree (evmMemIs base n contents) := ⟨pcFree_evmMemIs⟩

instance (base : Word) (n : Nat) : Assertion.PCFree (evmMemZero base n) :=
  ⟨pcFree_evmMemZero⟩

/-! ## High-water mark / EVM memory expansion (slice 2)

  The EVM tracks a single dynamic byte-size for memory (MSIZE), which only
  grows: any access to byte range `[offset, offset + length)` expands the
  active memory to the smallest multiple of 32 that covers the access, and
  the new size is the max of the old size and that bound.

  We model the size as a single 64-bit cell held at a caller-chosen scratch
  location `sizeLoc`, owning the assertion that the cell holds the current
  byte-size. The pure helper `evmMemExpand` computes the new byte-size; the
  separation-logic specs in later slices (MLOAD/MSTORE/MSTORE8/MSIZE) will
  read this cell, replace it, and reason about the contents update via
  `evmMemSizeIs`. -/

/-- The EVM memory size cell: an 8-byte cell at `sizeLoc` holding the current
    byte-size of EVM memory. The size is the high-water mark — bytes
    `[0, sizeBytes)` may be accessed; reads of unwritten bytes within that
    range still return zero (modelled by `evmMemZero`). -/
def evmMemSizeIs (sizeLoc : Word) (sizeBytes : Nat) : Assertion :=
  sizeLoc ↦ₘ BitVec.ofNat 64 sizeBytes

theorem evmMemSizeIs_unfold {sizeLoc : Word} {sizeBytes : Nat} :
    evmMemSizeIs sizeLoc sizeBytes = (sizeLoc ↦ₘ BitVec.ofNat 64 sizeBytes) := rfl

theorem pcFree_evmMemSizeIs {sizeLoc : Word} {sizeBytes : Nat} :
    (evmMemSizeIs sizeLoc sizeBytes).pcFree := by
  unfold evmMemSizeIs; exact pcFree_memIs

instance (sizeLoc : Word) (sizeBytes : Nat) :
    Assertion.PCFree (evmMemSizeIs sizeLoc sizeBytes) := ⟨pcFree_evmMemSizeIs⟩

/-- Round a byte count up to the next multiple of 32 (the EVM word size).
    `roundUpTo32 n = ((n + 31) / 32) * 32`. -/
def roundUpTo32 (n : Nat) : Nat := ((n + 31) / 32) * 32

theorem roundUpTo32_zero : roundUpTo32 0 = 0 := by decide

theorem roundUpTo32_le (n : Nat) : n ≤ roundUpTo32 n := by
  unfold roundUpTo32
  have h : n ≤ (n + 31) / 32 * 32 := by
    have := Nat.div_mul_le_self (n + 31) 32
    omega
  exact h

theorem roundUpTo32_dvd (n : Nat) : 32 ∣ roundUpTo32 n := by
  unfold roundUpTo32; exact ⟨(n + 31) / 32, (Nat.mul_comm _ _)⟩

theorem roundUpTo32_idempotent (n : Nat) : roundUpTo32 (roundUpTo32 n) = roundUpTo32 n := by
  unfold roundUpTo32
  -- (n+31)/32 * 32 is already a multiple of 32, so adding 31 and dividing
  -- by 32 yields the same quotient. omega handles Nat div/mod.
  omega

/-- The pure EVM memory-expansion update: given the current high-water
    `sizeBytes` and an access `(offset, length)`, compute the new
    high-water mark.

    Per the EVM yellow paper, an access of zero length never expands memory.
    Otherwise the active memory grows to cover `[offset, offset + length)`,
    rounded up to a 32-byte boundary, and the new size is the max of the old
    size and that bound. -/
def evmMemExpand (sizeBytes offset length : Nat) : Nat :=
  if length = 0 then sizeBytes else max sizeBytes (roundUpTo32 (offset + length))

/-- Zero-length accesses do not expand EVM memory. -/
@[simp] theorem evmMemExpand_zero_length (sizeBytes offset : Nat) :
    evmMemExpand sizeBytes offset 0 = sizeBytes := by
  unfold evmMemExpand; simp

theorem evmMemExpand_ge_old (sizeBytes offset length : Nat) :
    sizeBytes ≤ evmMemExpand sizeBytes offset length := by
  unfold evmMemExpand
  by_cases h : length = 0
  · simp [h]
  · simp [h]; exact Nat.le_max_left _ _

theorem evmMemExpand_ge_access (sizeBytes offset length : Nat) (hlen : length ≠ 0) :
    offset + length ≤ evmMemExpand sizeBytes offset length := by
  unfold evmMemExpand
  simp [hlen]
  exact Nat.le_trans (roundUpTo32_le _) (Nat.le_max_right _ _)

/-- The new high-water mark is always a multiple of 32 (when nonzero) — i.e.
    if the old size was 32-aligned, the new one is too. -/
theorem evmMemExpand_dvd_of_old_dvd (sizeBytes offset length : Nat)
    (h_old : 32 ∣ sizeBytes) :
    32 ∣ evmMemExpand sizeBytes offset length := by
  unfold evmMemExpand
  by_cases hlen : length = 0
  · simp [hlen]; exact h_old
  · simp [hlen]
    -- max of two multiples-of-32 is a multiple of 32
    rcases Nat.le_total sizeBytes (roundUpTo32 (offset + length)) with hle | hle
    · rw [Nat.max_eq_right hle]; exact roundUpTo32_dvd _
    · rw [Nat.max_eq_left hle]; exact h_old

/-- Idempotence: re-expanding for the same access does not grow further. -/
theorem evmMemExpand_idempotent (sizeBytes offset length : Nat) :
    evmMemExpand (evmMemExpand sizeBytes offset length) offset length =
    evmMemExpand sizeBytes offset length := by
  unfold evmMemExpand
  by_cases hlen : length = 0
  · simp [hlen]
  · simp only [hlen, if_false, Nat.max_assoc, Nat.max_self]

end EvmAsm.Evm64
