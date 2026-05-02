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

import EvmAsm.Rv64.ByteOps
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

/-! ## Byte-addressing adapters -/

/-- The RV64 dword cell address that owns the EVM memory byte
    `memBase + byteAddr`. -/
def evmMemDwordAddr (memBase byteAddr : Word) : Word :=
  alignToDword (memBase + byteAddr)

/-- The byte position, inside its owning RV64 dword, of EVM memory byte
    `memBase + byteAddr`. -/
def evmMemByteOffset (memBase byteAddr : Word) : Nat :=
  byteOffset (memBase + byteAddr)

/-- Read the EVM memory byte at `byteAddr` from its owning RV64 dword value. -/
def evmMemByteRead (memBase byteAddr dwordVal : Word) : BitVec 8 :=
  extractByte dwordVal (evmMemByteOffset memBase byteAddr)

/-- Own the RV64 dword cell that contains EVM memory byte `byteAddr`. -/
def evmMemDwordIs (memBase byteAddr dwordVal : Word) : Assertion :=
  evmMemDwordAddr memBase byteAddr ↦ₘ dwordVal

/-- Own the post-state dword after writing byte `b` to EVM memory byte
    `byteAddr`, starting from old owning dword `oldDword`. -/
def evmMemByteWriteIs
    (memBase byteAddr oldDword : Word) (b : BitVec 8) : Assertion :=
  evmMemDwordIs memBase byteAddr
    (replaceByte oldDword (evmMemByteOffset memBase byteAddr) b)

theorem evmMemDwordAddr_unfold {memBase byteAddr : Word} :
    evmMemDwordAddr memBase byteAddr = alignToDword (memBase + byteAddr) := rfl

theorem evmMemByteOffset_unfold {memBase byteAddr : Word} :
    evmMemByteOffset memBase byteAddr = byteOffset (memBase + byteAddr) := rfl

theorem evmMemByteOffset_lt_8 (memBase byteAddr : Word) :
    evmMemByteOffset memBase byteAddr < 8 := by
  unfold evmMemByteOffset
  exact byteOffset_lt_8

theorem evmMemByteAccess_valid_iff_memAddr_valid (memBase byteAddr : Word) :
    isValidByteAccess (memBase + byteAddr) = true ↔
      isValidMemAddr (memBase + byteAddr) = true := by
  rfl

theorem evmMemByteAccess_valid_of_memAddr_valid {memBase byteAddr : Word}
    (h_valid : isValidMemAddr (memBase + byteAddr) = true) :
    isValidByteAccess (memBase + byteAddr) = true := by
  exact (evmMemByteAccess_valid_iff_memAddr_valid memBase byteAddr).mpr h_valid

/-- The byte position inside the owning RV64 dword, packaged as a `Fin 8`
    for direct use with byte-algebra lemmas. -/
def evmMemByteOffsetFin (memBase byteAddr : Word) : Fin 8 :=
  ⟨evmMemByteOffset memBase byteAddr, evmMemByteOffset_lt_8 memBase byteAddr⟩

@[simp] theorem evmMemByteOffsetFin_val (memBase byteAddr : Word) :
    (evmMemByteOffsetFin memBase byteAddr).val =
      evmMemByteOffset memBase byteAddr := rfl

theorem evmMemByteRead_unfold {memBase byteAddr dwordVal : Word} :
    evmMemByteRead memBase byteAddr dwordVal =
      extractByte dwordVal (evmMemByteOffset memBase byteAddr) := rfl

theorem evmMemByteRead_replace_same
    (memBase byteAddr oldDword : Word) (b : BitVec 8) :
    evmMemByteRead memBase byteAddr
      (replaceByte oldDword (evmMemByteOffset memBase byteAddr) b) = b := by
  unfold evmMemByteRead evmMemByteOffset
  exact extractByte_replaceByte_same oldDword
    (evmMemByteOffsetFin memBase byteAddr) b

/-- LBU-shaped bridge: zero-extending the byte read immediately after an EVM
    memory byte write yields the written byte, zero-extended to a word. -/
theorem evmMemByteRead_replace_same_zeroExtend
    (memBase byteAddr oldDword : Word) (b : BitVec 8) :
    (evmMemByteRead memBase byteAddr
      (replaceByte oldDword (evmMemByteOffset memBase byteAddr) b)).zeroExtend 64 =
      b.zeroExtend 64 := by
  rw [evmMemByteRead_replace_same]

/-- LB-shaped bridge: sign-extending the byte read immediately after an EVM
    memory byte write yields the written byte, sign-extended to a word. -/
theorem evmMemByteRead_replace_same_signExtend
    (memBase byteAddr oldDword : Word) (b : BitVec 8) :
    (evmMemByteRead memBase byteAddr
      (replaceByte oldDword (evmMemByteOffset memBase byteAddr) b)).signExtend 64 =
      b.signExtend 64 := by
  rw [evmMemByteRead_replace_same]

theorem evmMemDwordIs_unfold {memBase byteAddr dwordVal : Word} :
    evmMemDwordIs memBase byteAddr dwordVal =
      (evmMemDwordAddr memBase byteAddr ↦ₘ dwordVal) := rfl

theorem evmMemByteWriteIs_unfold
    {memBase byteAddr oldDword : Word} {b : BitVec 8} :
    evmMemByteWriteIs memBase byteAddr oldDword b =
      evmMemDwordIs memBase byteAddr
        (replaceByte oldDword (evmMemByteOffset memBase byteAddr) b) := rfl

theorem pcFree_evmMemDwordIs {memBase byteAddr dwordVal : Word} :
    (evmMemDwordIs memBase byteAddr dwordVal).pcFree := by
  unfold evmMemDwordIs; exact pcFree_memIs

theorem pcFree_evmMemByteWriteIs
    {memBase byteAddr oldDword : Word} {b : BitVec 8} :
    (evmMemByteWriteIs memBase byteAddr oldDword b).pcFree := by
  unfold evmMemByteWriteIs; exact pcFree_evmMemDwordIs

instance (memBase byteAddr dwordVal : Word) :
    Assertion.PCFree (evmMemDwordIs memBase byteAddr dwordVal) :=
  ⟨pcFree_evmMemDwordIs⟩

instance (memBase byteAddr oldDword : Word) (b : BitVec 8) :
    Assertion.PCFree (evmMemByteWriteIs memBase byteAddr oldDword b) :=
  ⟨pcFree_evmMemByteWriteIs⟩

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

theorem roundUpTo32_le_add_31 (n : Nat) :
    roundUpTo32 n ≤ n + 31 := by
  unfold roundUpTo32
  exact Nat.div_mul_le_self (n + 31) 32

theorem roundUpTo32_dvd (n : Nat) : 32 ∣ roundUpTo32 n := by
  unfold roundUpTo32; exact ⟨(n + 31) / 32, (Nat.mul_comm _ _)⟩

theorem roundUpTo32_eq_self_of_dvd (n : Nat) (h : 32 ∣ n) :
    roundUpTo32 n = n := by
  rcases h with ⟨k, rfl⟩
  unfold roundUpTo32
  omega

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
  · rw [if_neg h]; exact Nat.le_max_left _ _

theorem evmMemExpand_ge_access (sizeBytes offset length : Nat) (hlen : length ≠ 0) :
    offset + length ≤ evmMemExpand sizeBytes offset length := by
  unfold evmMemExpand
  rw [if_neg hlen]
  exact Nat.le_trans (roundUpTo32_le _) (Nat.le_max_right _ _)

/-- MLOAD is a 32-byte byte-addressed access: expansion covers the byte just
    past the requested range for any starting byte offset. -/
theorem evmMemExpand_mload_ge_end (sizeBytes offset : Nat) :
    offset + 32 ≤ evmMemExpand sizeBytes offset 32 := by
  exact evmMemExpand_ge_access sizeBytes offset 32 (by decide)

/-- MLOAD expansion covers the starting byte for any byte offset; no
    doubleword-alignment precondition is needed. -/
theorem evmMemExpand_mload_ge_start (sizeBytes offset : Nat) :
    offset ≤ evmMemExpand sizeBytes offset 32 := by
  have h_end := evmMemExpand_mload_ge_end sizeBytes offset
  omega

/-- Every byte selected by MLOAD lies below the expanded high-water mark,
    independent of the offset's alignment. -/
theorem evmMemExpand_mload_byte_lt
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 32) :
    offset + byteIndex < evmMemExpand sizeBytes offset 32 := by
  have h_end := evmMemExpand_mload_ge_end sizeBytes offset
  omega

/-- MSTORE8 is a one-byte byte-addressed access: expansion covers the byte just
    past the requested range for any starting byte offset. -/
theorem evmMemExpand_mstore8_ge_end (sizeBytes offset : Nat) :
    offset + 1 ≤ evmMemExpand sizeBytes offset 1 := by
  exact evmMemExpand_ge_access sizeBytes offset 1 (by decide)

/-- MSTORE8 expansion covers the starting byte for any byte offset; no
    doubleword-alignment precondition is needed. -/
theorem evmMemExpand_mstore8_ge_start (sizeBytes offset : Nat) :
    offset ≤ evmMemExpand sizeBytes offset 1 := by
  have h_end := evmMemExpand_mstore8_ge_end sizeBytes offset
  omega

/-- Every byte selected by MSTORE8 lies below the expanded high-water mark,
    independent of the offset's alignment. -/
theorem evmMemExpand_mstore8_byte_lt
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 1) :
    offset + byteIndex < evmMemExpand sizeBytes offset 1 := by
  have h_end := evmMemExpand_mstore8_ge_end sizeBytes offset
  omega

theorem evmMemExpand_mstore8_byte_dword_end_le
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 1) :
    ((offset + byteIndex) / 8 + 1) * 8 ≤
      evmMemExpand sizeBytes offset 1 := by
  unfold evmMemExpand
  rw [if_neg (by decide : (1 : Nat) ≠ 0)]
  have h_round : ((offset + byteIndex) / 8 + 1) * 8 ≤
      roundUpTo32 (offset + 1) := by
    unfold roundUpTo32
    omega
  exact Nat.le_trans h_round (Nat.le_max_right _ _)

theorem evmMemExpand_mstore8_byte_dword_start_lt
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 1) :
    ((offset + byteIndex) / 8) * 8 <
      evmMemExpand sizeBytes offset 1 := by
  have h_byte_lt := evmMemExpand_mstore8_byte_lt sizeBytes offset byteIndex h_byte
  have h_start_le : ((offset + byteIndex) / 8) * 8 ≤ offset + byteIndex := by
    exact Nat.div_mul_le_self (offset + byteIndex) 8
  exact Nat.lt_of_le_of_lt h_start_le h_byte_lt

theorem evmMemExpand_mstore8_byte_dword_interval
    (sizeBytes offset byteIndex : Nat) (h_byte : byteIndex < 1) :
    ((offset + byteIndex) / 8) * 8 <
        evmMemExpand sizeBytes offset 1 ∧
      ((offset + byteIndex) / 8 + 1) * 8 ≤
        evmMemExpand sizeBytes offset 1 := by
  exact ⟨
    evmMemExpand_mstore8_byte_dword_start_lt sizeBytes offset byteIndex h_byte,
    evmMemExpand_mstore8_byte_dword_end_le sizeBytes offset byteIndex h_byte⟩

theorem evmMemExpand_mstore8_byte_dword_byte_lt
    (sizeBytes offset byteIndex dwordByte : Nat)
    (h_byte : byteIndex < 1) (h_dwordByte : dwordByte < 8) :
    ((offset + byteIndex) / 8) * 8 + dwordByte <
      evmMemExpand sizeBytes offset 1 := by
  have h_interval :=
    evmMemExpand_mstore8_byte_dword_interval sizeBytes offset byteIndex h_byte
  have h_lt_end :
      ((offset + byteIndex) / 8) * 8 + dwordByte <
        ((offset + byteIndex) / 8 + 1) * 8 := by
    omega
  exact Nat.lt_of_lt_of_le h_lt_end h_interval.2

theorem evmMemExpand_mstore8_dword_byte_lt
    (sizeBytes offset dwordByte : Nat) (h_dwordByte : dwordByte < 8) :
    (offset / 8) * 8 + dwordByte <
      evmMemExpand sizeBytes offset 1 := by
  exact evmMemExpand_mstore8_byte_dword_byte_lt
    sizeBytes offset 0 dwordByte (by decide) h_dwordByte

theorem evmMemExpand_le_max_old_access_plus_31
    (sizeBytes offset length : Nat) :
    evmMemExpand sizeBytes offset length ≤ max sizeBytes (offset + length + 31) := by
  unfold evmMemExpand
  by_cases hlen : length = 0
  · simp [hlen]
  · rw [if_neg hlen]
    exact max_le (Nat.le_max_left _ _)
      (Nat.le_trans (roundUpTo32_le_add_31 (offset + length)) (Nat.le_max_right _ _))

theorem evmMemExpand_le_of_old_le_and_access_le
    (sizeBytes offset length bound : Nat)
    (h_old : sizeBytes ≤ bound)
    (h_access : roundUpTo32 (offset + length) ≤ bound) :
    evmMemExpand sizeBytes offset length ≤ bound := by
  unfold evmMemExpand
  by_cases hlen : length = 0
  · simp [hlen, h_old]
  · rw [if_neg hlen]
    exact max_le h_old h_access

/-- If the current high-water mark already covers the rounded access bound,
    the EVM memory size is unchanged. -/
theorem evmMemExpand_eq_old_of_access_le
    (sizeBytes offset length : Nat)
    (h : roundUpTo32 (offset + length) ≤ sizeBytes) :
    evmMemExpand sizeBytes offset length = sizeBytes := by
  unfold evmMemExpand
  by_cases hlen : length = 0
  · simp [hlen]
  · rw [if_neg hlen]
    exact max_eq_left h

/-- If a nonzero access grows past the current high-water mark, the new EVM
    memory size is the rounded access bound. -/
theorem evmMemExpand_eq_access_of_old_le
    (sizeBytes offset length : Nat) (hlen : length ≠ 0)
    (h : sizeBytes ≤ roundUpTo32 (offset + length)) :
    evmMemExpand sizeBytes offset length = roundUpTo32 (offset + length) := by
  unfold evmMemExpand
  rw [if_neg hlen]
  exact max_eq_right h

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
