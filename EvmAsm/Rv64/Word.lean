/-
  EvmAsm.Rv64.Word

  Pure bitvector / address utilities for the RV64 word type, with NO
  dependency on the machine model (Reg / Instr / MachineState). This
  module is a root (no imports), so consumers that only need the `Word`
  notation, alignment predicates, byte-extraction ops, or address
  constants do not transitively pull in the full machine model.

  `Rv64.Basic` imports this file and layers the machine model on top.
-/

namespace EvmAsm.Rv64

/-- We use 64-bit words as our machine word size.
    Defined as `notation` (not `abbrev`) so the elaborator always produces `BitVec 64`
    in Expr output, giving identical Expr.hash regardless of whether `Word` or `BitVec 64`
    was written in source. This is required for the xperm AC reflection fast path. -/
notation "Word" => BitVec 64

-- Note: Addr was previously a separate abbrev but has been unified with Word
-- to avoid Expr.hash mismatches in the xperm tactic (Addr vs Word vs BitVec 64).

-- ============================================================================
-- Memory constraints
-- ============================================================================

/-! ### Valid-memory zones

  The verified machine model recognises three disjoint regions as
  "valid memory" (see GitHub issue #5164 for the rationale). Each is
  a contiguous `[lo, hi]` byte range; `isValidMemAddr` is the
  disjunction over all three.

  The legacy zone (`MEM_START..MEM_END`) is unchanged; the other two
  match ziskemu's host-IO map (`EvmAsm/Codegen/Driver.lean:68-82`,
  `EvmAsm/Codegen/Programs.lean`):

  | Zone | Range | Purpose |
  |---|---|---|
  | Legacy | `0x20..0x78000000` | scratch/heap touched by verified opcodes |
  | Input  | `0x40000000..0x40002000` | ziskemu `INPUT_ADDR` (8 KiB) |
  | RAM    | `0xa0000000..0xc0000000` | ziskemu `.data` + `OUTPUT_ADDR` |
-/

/-- Legacy valid memory region start (low-scratch zone, unchanged
    from before #5164). -/
def MEM_START : Nat := 0x20

/-- Legacy valid memory region end (low-scratch zone). -/
def MEM_END : Nat := 0x78000000

/-- Input-buffer zone start. Matches ziskemu's `INPUT_ADDR`
    (`EvmAsm/Codegen/Programs.lean`). -/
def INPUT_MEM_START : Nat := 0x40000000

/-- Input-buffer zone end. 8 KiB above `INPUT_MEM_START`. -/
def INPUT_MEM_END : Nat := 0x40002000

/-- RAM zone start. Covers ziskemu's writable `.data` section base
    (`-Tdata=0xa0000000`) and `OUTPUT_ADDR = 0xa0010000`. -/
def RAM_MEM_START : Nat := 0xa0000000

/-- RAM zone end. Matches ziskemu's writable region tail. -/
def RAM_MEM_END : Nat := 0xc0000000

/-- Address is 8-byte aligned (doubleword). -/
def isAligned8 (addr : Word) : Bool := addr.toNat % 8 == 0

/-- Address is 4-byte aligned. -/
def isAligned4 (addr : Word) : Bool := addr.toNat % 4 == 0

/-- Address is in valid memory range -- one of three disjoint zones
    (see issue #5164). The first disjunct preserves the pre-#5164
    behaviour for unchanged proofs; the additional disjuncts admit
    addresses in ziskemu's `INPUT_ADDR` and writable-RAM regions. -/
def isValidMemAddr (addr : Word) : Bool :=
  (decide (MEM_START ≤ addr.toNat) && decide (addr.toNat ≤ MEM_END)) ||
  (decide (INPUT_MEM_START ≤ addr.toNat) && decide (addr.toNat ≤ INPUT_MEM_END)) ||
  (decide (RAM_MEM_START ≤ addr.toNat) && decide (addr.toNat ≤ RAM_MEM_END))

/-- Valid doubleword memory access: in range AND 8-byte aligned. -/
def isValidDwordAccess (addr : Word) : Bool :=
  isValidMemAddr addr && isAligned8 addr

/-- Valid word-size memory access: in range AND 4-byte aligned. -/
def isValidMemAccess (addr : Word) : Bool :=
  isValidMemAddr addr && isAligned4 addr

@[simp] theorem isValidDwordAccess_eq {addr : Word} :
    isValidDwordAccess addr = (isValidMemAddr addr && isAligned8 addr) := rfl

@[simp] theorem isValidMemAccess_eq {addr : Word} :
    isValidMemAccess addr = (isValidMemAddr addr && isAligned4 addr) := rfl

@[simp] theorem isValidMemAddr_eq {addr : Word} :
    isValidMemAddr addr =
      ((decide (MEM_START ≤ addr.toNat) && decide (addr.toNat ≤ MEM_END)) ||
       (decide (INPUT_MEM_START ≤ addr.toNat) && decide (addr.toNat ≤ INPUT_MEM_END)) ||
       (decide (RAM_MEM_START ≤ addr.toNat) && decide (addr.toNat ≤ RAM_MEM_END))) := rfl

@[simp] theorem isAligned8_eq (addr : Word) :
    isAligned8 addr = (addr.toNat % 8 == 0) := rfl

@[simp] theorem isAligned4_eq (addr : Word) :
    isAligned4 addr = (addr.toNat % 4 == 0) := rfl

/-- Address is 2-byte aligned. -/
def isAligned2 (addr : Word) : Bool := addr.toNat % 2 == 0

/-- Valid halfword memory access: in range AND 2-byte aligned. -/
def isValidHalfwordAccess (addr : Word) : Bool :=
  isValidMemAddr addr && isAligned2 addr

/-- Valid byte memory access: in range (bytes need no alignment). -/
def isValidByteAccess (addr : Word) : Bool :=
  isValidMemAddr addr

@[simp] theorem isAligned2_eq (addr : Word) :
    isAligned2 addr = (addr.toNat % 2 == 0) := rfl

@[simp] theorem isValidHalfwordAccess_eq {addr : Word} :
    isValidHalfwordAccess addr = (isValidMemAddr addr && isAligned2 addr) := rfl

@[simp] theorem isValidByteAccess_eq {addr : Word} :
    isValidByteAccess addr = isValidMemAddr addr := rfl

/-- ValidMemRange addr n holds when n consecutive doubleword-aligned memory accesses
    starting at addr are all valid. -/
def ValidMemRange (addr : Word) (n : Nat) : Prop :=
  ∀ (i : Nat), i < n → isValidDwordAccess (addr + BitVec.ofNat 64 (8 * i)) = true

/-- Extract a single validity fact from ValidMemRange. -/
theorem ValidMemRange.get {addr : Word} {n : Nat}
    (h : ValidMemRange addr n) {i : Nat} (hi : i < n) :
    isValidDwordAccess (addr + BitVec.ofNat 64 (8 * i)) = true := h i hi

/-- Extract a single validity fact from ValidMemRange with address normalization. -/
theorem ValidMemRange.fetch {addr : Word} {n : Nat}
    (h : ValidMemRange addr n) (i : Nat) (target : Word)
    (hi : i < n)
    (haddr : addr + BitVec.ofNat 64 (8 * i) = target) :
    isValidDwordAccess target = true := by
  rw [← haddr]; exact h i hi

/-- Extract a byte from a 64-bit word at position 0-7. -/
def extractByte (w : Word) (pos : Nat) : BitVec 8 :=
  (w >>> (pos * 8)).truncate 8

/-- Extract a halfword from a 64-bit word at position 0-3 (in halfword units). -/
def extractHalfword (w : Word) (pos : Nat) : BitVec 16 :=
  (w >>> (pos * 16)).truncate 16

/-- Extract a 32-bit word from a 64-bit word at position 0-1 (in word units). -/
def extractWord32 (w : Word) (pos : Nat) : BitVec 32 :=
  (w >>> (pos * 32)).truncate 32

/-- Replace a byte in a 64-bit word at position 0-7. -/
def replaceByte (w : Word) (pos : Nat) (b : BitVec 8) : Word :=
  let mask : Word := ~~~(0xFF#64 <<< (pos * 8))
  (w &&& mask) ||| ((b.zeroExtend 64) <<< (pos * 8))

/-- Replace a halfword in a 64-bit word at position 0-3 (in halfword units). -/
def replaceHalfword (w : Word) (pos : Nat) (h : BitVec 16) : Word :=
  let mask : Word := ~~~(0xFFFF#64 <<< (pos * 16))
  (w &&& mask) ||| ((h.zeroExtend 64) <<< (pos * 16))

/-- Replace a 32-bit word in a 64-bit word at position 0-1 (in word units). -/
def replaceWord32 (w : Word) (pos : Nat) (v : BitVec 32) : Word :=
  let mask : Word := ~~~(0xFFFFFFFF#64 <<< (pos * 32))
  (w &&& mask) ||| ((v.zeroExtend 64) <<< (pos * 32))

/-- Align an address down to the nearest 8-byte boundary. -/
def alignToDword (addr : Word) : Word := addr &&& ~~~7#64

/-- Get the byte offset within a doubleword (0-7). -/
def byteOffset (addr : Word) : Nat := (addr &&& 7#64).toNat

/-- Convert up to 8 bytes (little-endian) into a 64-bit word, zero-padding if fewer than 8. -/
def bytesToWordLE (bs : List (BitVec 8)) : Word :=
  let b0 : Word := (bs[0]?.getD 0).zeroExtend 64
  let b1 : Word := (bs[1]?.getD 0).zeroExtend 64
  let b2 : Word := (bs[2]?.getD 0).zeroExtend 64
  let b3 : Word := (bs[3]?.getD 0).zeroExtend 64
  let b4 : Word := (bs[4]?.getD 0).zeroExtend 64
  let b5 : Word := (bs[5]?.getD 0).zeroExtend 64
  let b6 : Word := (bs[6]?.getD 0).zeroExtend 64
  let b7 : Word := (bs[7]?.getD 0).zeroExtend 64
  b0 ||| (b1 <<< (8 : Word)) ||| (b2 <<< (16 : Word)) ||| (b3 <<< (24 : Word)) |||
  (b4 <<< (32 : Word)) ||| (b5 <<< (40 : Word)) ||| (b6 <<< (48 : Word)) ||| (b7 <<< (56 : Word))

end EvmAsm.Rv64
