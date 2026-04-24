/-
  EvmAsm.Evm64.CodeRegion

  Separation logic model for EVM bytecode stored as a byte array
  in RISC-V memory. Bytes are grouped into 8-byte doubleword chunks,
  each asserted via `↦ₘ` with value reconstructed by `packBytes`.

  Consumers (PUSH1-32, opcode dispatch) use `evmCodeIs_split_at`
  to extract the relevant doubleword, then `generic_lbu_spec` +
  `extractByte_packBytes` to read individual bytes.
-/

import EvmAsm.Evm64.Basic
-- `ByteOps` transitively imports `Rv64.SepLogic`.
import EvmAsm.Rv64.ByteOps

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- packDword / packBytes: reconstruct 64-bit words from byte lists
-- ============================================================================

/-- Pack 8 bytes (little-endian) into a 64-bit word.
    Byte 0 at bits [0,8), byte 1 at bits [8,16), ..., byte 7 at bits [56,64). -/
def packDword (f : Fin 8 → BitVec 8) : Word :=
  (f 0).zeroExtend 64 |||
  ((f 1).zeroExtend 64 <<< 8) |||
  ((f 2).zeroExtend 64 <<< 16) |||
  ((f 3).zeroExtend 64 <<< 24) |||
  ((f 4).zeroExtend 64 <<< 32) |||
  ((f 5).zeroExtend 64 <<< 40) |||
  ((f 6).zeroExtend 64 <<< 48) |||
  ((f 7).zeroExtend 64 <<< 56)

/-- Index into a byte list with zero-padding for out-of-range. -/
def getByteAt (bytes : List (BitVec 8)) (k : Nat) : BitVec 8 :=
  if h : k < bytes.length then bytes[k] else 0

/-- Pack a list of bytes into a 64-bit word (little-endian).
    Uses the first 8 bytes; pads with zeros if fewer than 8 are provided. -/
def packBytes (bytes : List (BitVec 8)) : Word :=
  packDword (fun i => getByteAt bytes i.val)

-- ============================================================================
-- extractByte_packDword: the critical bridge lemma
-- ============================================================================

private theorem epd_core (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (k : Fin 8) :
    let w := b0.zeroExtend 64 |||
       (b1.zeroExtend 64 <<< 8) |||
       (b2.zeroExtend 64 <<< 16) |||
       (b3.zeroExtend 64 <<< 24) |||
       (b4.zeroExtend 64 <<< 32) |||
       (b5.zeroExtend 64 <<< 40) |||
       (b6.zeroExtend 64 <<< 48) |||
       (b7.zeroExtend 64 <<< 56)
    (w >>> (k.val * 8)).truncate 8 =
    (match k with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
                  | 4 => b4 | 5 => b5 | 6 => b6 | 7 => b7) := by
  fin_cases k <;> simp only [] <;> bv_decide

theorem extractByte_packDword {f : Fin 8 → BitVec 8} {i : Fin 8} :
    extractByte (packDword f) i.val = f i := by
  show (packDword f >>> (i.val * 8)).truncate 8 = f i
  unfold packDword
  have := epd_core (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) i
  simp only [] at this
  convert this using 1
  fin_cases i <;> rfl

-- ============================================================================
-- extractByte_packBytes: list-level extraction
-- ============================================================================

theorem extractByte_packBytes (bytes : List (BitVec 8)) (k : Nat)
    (hk : k < 8) (hlen : k < bytes.length) :
    extractByte (packBytes bytes) k = bytes[k] := by
  conv_lhs => rw [show k = (⟨k, hk⟩ : Fin 8).val from rfl]
  rw [packBytes, extractByte_packDword]
  simp [getByteAt, hlen]

-- ============================================================================
-- evmCodeIs: EVM bytecode as a byte array in memory
-- ============================================================================

/-- Auxiliary: assert `nChunks` consecutive doubleword chunks of bytecode. -/
def evmCodeIsAux (base : Word) : Nat → List (BitVec 8) → Assertion
  | 0, _ => empAssertion
  | n + 1, bytes =>
    (base ↦ₘ packBytes (bytes.take 8)) ** evmCodeIsAux (base + 8) n (bytes.drop 8)

/-- Number of doubleword chunks needed for a byte list. -/
private def numChunks (n : Nat) : Nat := (n + 7) / 8

/-- Assert that EVM bytecode occupies consecutive memory starting at `base`.
    Bytes are grouped into 8-byte doubleword chunks. The base address must
    be 8-byte aligned (caller's obligation).

    Each doubleword is packed little-endian: byte at `base+k` is stored
    at bit position `(k%8)*8` within the doubleword at `alignToDword(base+k)`. -/
def evmCodeIs (base : Word) (bytes : List (BitVec 8)) : Assertion :=
  evmCodeIsAux base (numChunks bytes.length) bytes

-- ============================================================================
-- Basic properties
-- ============================================================================

@[simp] theorem evmCodeIs_nil {base : Word} :
    evmCodeIs base [] = empAssertion := rfl

/-- evmCodeIs of a non-empty list decomposes into a chunk and the rest. -/
theorem evmCodeIs_nonempty (base : Word) (bytes : List (BitVec 8)) (h : bytes ≠ []) :
    evmCodeIs base bytes =
    ((base ↦ₘ packBytes (bytes.take 8)) **
     evmCodeIs (base + 8) (bytes.drop 8)) := by
  have hlen : 0 < bytes.length := by cases bytes <;> simp_all
  show evmCodeIsAux base (numChunks bytes.length) bytes =
    ((base ↦ₘ packBytes (bytes.take 8)) **
     evmCodeIsAux (base + 8) (numChunks (bytes.drop 8).length) (bytes.drop 8))
  have hstep : numChunks bytes.length =
    numChunks (bytes.drop 8).length + 1 := by
    simp [numChunks]; omega
  rw [hstep]; rfl

theorem pcFree_evmCodeIsAux {base : Word} {n : Nat} {bytes : List (BitVec 8)} :
    (evmCodeIsAux base n bytes).pcFree := by
  induction n generalizing base bytes with
  | zero => exact pcFree_emp
  | succ _ ih => exact pcFree_sepConj pcFree_memIs ih

theorem pcFree_evmCodeIs {base : Word} {bytes : List (BitVec 8)} :
    (evmCodeIs base bytes).pcFree :=
  pcFree_evmCodeIsAux

instance (base : Word) (bytes : List (BitVec 8)) :
    Assertion.PCFree (evmCodeIs base bytes) :=
  ⟨pcFree_evmCodeIs⟩

-- ============================================================================
-- evmCodeIs_split_at: extract the doubleword containing byte k
-- ============================================================================

theorem evmCodeIs_split_at (base : Word) (bytes : List (BitVec 8)) (dw : Nat)
    (hdw : dw * 8 + 8 ≤ bytes.length) :
    evmCodeIs base bytes =
    (evmCodeIs base (bytes.take (dw * 8)) **
     ((base + BitVec.ofNat 64 (dw * 8)) ↦ₘ
       packBytes ((bytes.drop (dw * 8)).take 8)) **
     evmCodeIs (base + BitVec.ofNat 64 ((dw + 1) * 8))
       (bytes.drop ((dw + 1) * 8))) := by
  induction dw generalizing base bytes with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, List.take_zero, evmCodeIs_nil,
               sepConj_emp_left', BitVec.add_zero, Nat.one_mul]
    exact evmCodeIs_nonempty base bytes (by intro h; simp [h] at hdw)
  | succ n ih =>
    rw [evmCodeIs_nonempty base bytes (by intro h; simp [h] at hdw)]
    have hdw' : n * 8 + 8 ≤ (bytes.drop 8).length := by
      have heq : (bytes.drop 8).length = bytes.length - 8 := by simp
      rw [heq]
      have h8 : 8 ≤ bytes.length := by omega
      have : bytes.length - 8 + 8 = bytes.length := Nat.sub_add_cancel h8
      omega
    rw [ih (base + 8) (bytes.drop 8) hdw']; clear hdw'
    -- Normalize addresses
    have ha1 : (base + 8 : Word) + BitVec.ofNat 64 (n * 8) =
               base + BitVec.ofNat 64 ((n + 1) * 8) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have ha2 : (base + 8 : Word) + BitVec.ofNat 64 ((n + 1) * 8) =
               base + BitVec.ofNat 64 ((n + 2) * 8) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [ha1, ha2]
    -- Normalize list operations
    have harith1 : 8 + n * 8 = (n + 1) * 8 := by ring
    have harith2 : 8 + (n + 1) * 8 = (n + 2) * 8 := by ring
    have ht2 : ((bytes.drop 8).drop (n * 8)).take 8 =
               (bytes.drop ((n + 1) * 8)).take 8 := by
      rw [List.drop_drop, harith1]
    have ht3 : (bytes.drop 8).drop ((n + 1) * 8) =
               bytes.drop ((n + 2) * 8) := by
      rw [List.drop_drop, harith2]
    rw [ht2, ht3]
    -- Reassociate: A ** (B ** (C ** D)) = (A ** B) ** (C ** D)
    rw [← sepConj_assoc']
    congr 1
    -- Show: (base ↦ₘ ...) ** evmCodeIs (base+8) (...) = evmCodeIs base (bytes.take ((n+1)*8))
    symm
    have hne : bytes.take ((n + 1) * 8) ≠ [] := by
      intro h
      have : (bytes.take ((n + 1) * 8)).length = 0 := by simp [h]
      simp only [List.length_take] at this; omega
    rw [evmCodeIs_nonempty base (bytes.take ((n + 1) * 8)) hne]
    congr 1
    · congr 1
      rw [List.take_take, show min 8 ((n + 1) * 8) = 8 from by omega]
    · have harith3 : (n + 1) * 8 - 8 = n * 8 := by omega
      rw [List.drop_take, harith3]

-- ============================================================================
-- Alignment bridge lemma
-- ============================================================================

/-- Aligned base: low 3 bits are zero. -/
abbrev IsAligned8 (addr : Word) : Prop := addr &&& 7#64 = 0#64

/-- An aligned address is unchanged by alignToDword. -/
theorem alignToDword_of_aligned (base : Word) (h : IsAligned8 base) :
    alignToDword base = base := by
  unfold alignToDword
  have : base &&& ~~~7#64 = base ^^^ (base &&& 7#64) := by bv_decide
  rw [this, h]; simp [BitVec.xor_zero]

-- ============================================================================
-- Byte extraction bridge
-- ============================================================================

/-- Reading byte `k` from the code region: the byte at global index `k` can be
    extracted from the containing doubleword's `packBytes` using byte offset `k % 8`. -/
theorem extractByte_codeRegion_at (bytes : List (BitVec 8)) (k : Nat)
    (hk : k < bytes.length) :
    extractByte (packBytes ((bytes.drop (k / 8 * 8)).take 8)) (k % 8) = bytes[k] := by
  have hmod : k % 8 < 8 := Nat.mod_lt k (by omega)
  have hchunkLen : k % 8 < ((bytes.drop (k / 8 * 8)).take 8).length := by
    simp; omega
  rw [extractByte_packBytes _ (k % 8) hmod (by simp; omega)]
  show ((bytes.drop (k / 8 * 8)).take 8)[k % 8]'hchunkLen = bytes[k]
  rw [List.getElem_take, List.getElem_drop]
  congr 1; omega

end EvmAsm.Evm64
