/-
  EvmAsm.Evm64.Calldata.Basic

  Pure calldata helpers for CALLDATALOAD/CALLDATACOPY work (GH #104 slice 1).
  CALLDATALOAD reads 32 bytes starting at a byte offset, interprets them as a
  big-endian 256-bit word, and pads reads past the calldata length with zero.
-/

import EvmAsm.Evm64.EvmWord

namespace EvmAsm.Evm64
namespace Calldata

/-- Read one calldata byte, returning zero past the end of the buffer. -/
def callDataByte (data : List (BitVec 8)) (idx : Nat) : BitVec 8 :=
  if h : idx < data.length then data[idx] else 0

/-- Fold one big-endian byte into an accumulator. -/
def appendByte (acc : Nat) (b : BitVec 8) : Nat :=
  acc * 256 + b.toNat

/-- Natural-number assembly of the 32-byte CALLDATALOAD window. This is the
    executable mathematical target; `callDataLoadWord` reduces it modulo
    `2^256` through `BitVec.ofNat 256`. -/
def callDataLoadNat (data : List (BitVec 8)) (offset : Nat) : Nat :=
  (List.range 32).foldl
    (fun acc i => appendByte acc (callDataByte data (offset + i)))
    0

/-- CALLDATALOAD result word: 32 bytes from calldata, big-endian, zero-padded. -/
def callDataLoadWord (data : List (BitVec 8)) (offset : Nat) : EvmWord :=
  BitVec.ofNat 256 (callDataLoadNat data offset)

theorem callDataByte_of_lt {data : List (BitVec 8)} {idx : Nat}
    (h : idx < data.length) :
    callDataByte data idx = data[idx] := by
  simp [callDataByte, h]

theorem callDataByte_of_ge {data : List (BitVec 8)} {idx : Nat}
    (h : data.length ≤ idx) :
    callDataByte data idx = 0 := by
  simp [callDataByte, show ¬idx < data.length from by omega]

@[simp] theorem callDataByte_nil (idx : Nat) :
    callDataByte [] idx = 0 := by
  exact callDataByte_of_ge (data := []) (idx := idx) (by simp)

@[simp] theorem appendByte_zero :
    appendByte 0 0 = 0 := rfl

theorem callDataLoadNat_nil (offset : Nat) :
    callDataLoadNat [] offset = 0 := by
  have hmul : ∀ xs : List Nat, List.foldl (fun acc (_ : Nat) => acc * 256) 0 xs = 0 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons _ xs ih => simpa [List.foldl_cons] using ih
  simpa [callDataLoadNat, appendByte] using hmul (List.range 32)

theorem callDataLoadWord_nil (offset : Nat) :
    callDataLoadWord [] offset = 0 := by
  rw [callDataLoadWord, callDataLoadNat_nil]
  rfl

/-! ### Upper bound on `callDataLoadNat`

The big-endian 32-byte CALLDATALOAD assembly fits in 256 bits.  This is
the structural ingredient that lets the upcoming RISC-V proof
(`evm-asm-ugei`, GH #104 slice 4) treat the `BitVec.ofNat 256` wrapper
in `callDataLoadWord` as essentially a no-op for limb-projection
reasoning. -/

/-- One folding step preserves the `< 256^k` bucket and grows the bucket
    by one byte. -/
theorem appendByte_lt_pow {acc : Nat} {b : BitVec 8} {k : Nat}
    (h : acc < 256 ^ k) : appendByte acc b < 256 ^ (k + 1) := by
  have hb : b.toNat < 256 := b.isLt
  have hsucc : acc + 1 ≤ 256 ^ k := h
  have hmul : (acc + 1) * 256 ≤ 256 ^ k * 256 :=
    Nat.mul_le_mul_right 256 hsucc
  have hpow : 256 ^ (k + 1) = 256 ^ k * 256 := by
    rw [Nat.pow_succ]
  have hexp : (acc + 1) * 256 = acc * 256 + 256 := by
    rw [Nat.succ_mul]
  rw [hpow]
  unfold appendByte
  omega

/-- Generic byte-fold bound: starting from `acc < 256^k` and folding `n`
    bytes (any `BitVec 8` source) yields a value `< 256^(k+n)`. -/
theorem foldl_appendByte_lt_pow
    {α : Type _} (g : α → BitVec 8) :
    ∀ (xs : List α) (acc k : Nat),
      acc < 256 ^ k →
      (xs.foldl (fun a x => appendByte a (g x)) acc) < 256 ^ (k + xs.length)
  | [], acc, k, h => by simpa using h
  | x :: xs, acc, k, h => by
      have hstep : appendByte acc (g x) < 256 ^ (k + 1) :=
        appendByte_lt_pow h
      have hrec :=
        foldl_appendByte_lt_pow g xs (appendByte acc (g x)) (k + 1) hstep
      have hlen : k + 1 + xs.length = k + (x :: xs).length := by
        simp [List.length_cons]; omega
      simpa [List.foldl_cons, hlen] using hrec

/-- The mathematical CALLDATALOAD assembly always fits in 256 bits. -/
theorem callDataLoadNat_lt (data : List (BitVec 8)) (offset : Nat) :
    callDataLoadNat data offset < 2 ^ 256 := by
  have h0 : (0 : Nat) < 256 ^ 0 := by decide
  have hlen : (List.range 32).length = 32 := List.length_range
  have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  have hbound :=
    foldl_appendByte_lt_pow
      (g := fun i => callDataByte data (offset + i))
      (List.range 32) 0 0 h0
  -- hbound : (...).foldl ... 0 < 256 ^ (0 + (List.range 32).length)
  rw [hlen] at hbound
  -- hbound : (...).foldl ... 0 < 256 ^ (0 + 32)
  simp only [Nat.zero_add] at hbound
  -- hbound : ... < 256 ^ 32
  unfold callDataLoadNat
  exact hpow ▸ hbound

/-- Round-trip: as a natural number, the CALLDATALOAD word equals
    `callDataLoadNat`. Composes `callDataLoadNat_lt` with the BitVec
    `toNat ∘ ofNat` reduction; downstream limb-projection lemmas use
    this to skip past the `BitVec.ofNat 256` wrapper. -/
theorem callDataLoadWord_toNat (data : List (BitVec 8)) (offset : Nat) :
    (callDataLoadWord data offset).toNat = callDataLoadNat data offset := by
  unfold callDataLoadWord
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (callDataLoadNat_lt data offset)]

/-! ### Out-of-bounds CALLDATALOAD collapses to zero

When the EVM offset is at or past the end of calldata, every byte the
32-byte window would touch lies past `data.length` and reads as zero
(`callDataByte_of_ge`).  The big-endian fold therefore collapses to `0`,
and the resulting EvmWord is zero too.  The CALLDATALOAD RISC-V proof
(`evm-asm-ugei`, GH #104 slice 4) uses these on the bounds-check branch
where the spec collapses to a constant-zero limbset. -/

/-- Folding `appendByte 0` over any list (every byte is zero) yields `0`.
    This is the structural ingredient shared between `callDataLoadNat_nil`
    and `callDataLoadNat_of_ge_length`. -/
theorem foldl_appendByte_zero
    {α : Type _} (xs : List α) :
    xs.foldl (fun acc (_ : α) => appendByte acc 0) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simpa [List.foldl_cons, appendByte] using ih

/-- `callDataLoadNat` reads zero past the end of the calldata buffer:
    if the offset is at or beyond `data.length`, every byte in the
    32-byte big-endian window reads as zero, so the assembly is `0`. -/
theorem callDataLoadNat_of_ge_length
    {data : List (BitVec 8)} {offset : Nat}
    (h : data.length ≤ offset) :
    callDataLoadNat data offset = 0 := by
  -- Replace the byte source with the constant-zero generator and reuse
  -- the generic `foldl_appendByte_zero` lemma.
  have hfun :
      (fun (acc : Nat) (i : Nat) =>
        appendByte acc (callDataByte data (offset + i)))
        =
      (fun (acc : Nat) (_ : Nat) => appendByte acc 0) := by
    funext acc i
    have : data.length ≤ offset + i := Nat.le_trans h (Nat.le_add_right _ _)
    rw [callDataByte_of_ge this]
  unfold callDataLoadNat
  rw [hfun]
  exact foldl_appendByte_zero (List.range 32)

/-- `callDataLoadWord` is zero when the offset is past the end of the
    calldata buffer.  Useful on the BGEU bounds-check branch of the
    CALLDATALOAD RISC-V program, where the spec collapses to a
    constant-zero limbset. -/
theorem callDataLoadWord_of_ge_length
    {data : List (BitVec 8)} {offset : Nat}
    (h : data.length ≤ offset) :
    callDataLoadWord data offset = 0 := by
  rw [callDataLoadWord, callDataLoadNat_of_ge_length h]
  rfl

/-! ### CALLDATACOPY pure helper

`callDataCopyBytes data dataOffset size` is the byte sequence that
CALLDATACOPY writes into EVM memory: `size` bytes drawn from `data`
starting at `dataOffset`, zero-padding past the end of the calldata
buffer. This is the executable mathematical target consumed by the
CALLDATACOPY RISC-V program (evm-asm-r3sk / GH #104 slice 5);
defining it here keeps the pure helper colocated with `callDataByte`,
`callDataLoadWord`, and the rest of the pure calldata surface and
unblocks the CALLDATACOPY program slice from the pure-helper side.
-/

/-- The byte sequence written by CALLDATACOPY:
    `size` bytes from `data` starting at `dataOffset`, with
    out-of-bounds reads producing zero. Length is `size` by
    construction (see `callDataCopyBytes_length`). -/
def callDataCopyBytes
    (data : List (BitVec 8)) (dataOffset size : Nat) : List (BitVec 8) :=
  (List.range size).map (fun i => callDataByte data (dataOffset + i))

@[simp] theorem callDataCopyBytes_length
    (data : List (BitVec 8)) (dataOffset size : Nat) :
    (callDataCopyBytes data dataOffset size).length = size := by
  simp [callDataCopyBytes]

@[simp] theorem callDataCopyBytes_zero
    (data : List (BitVec 8)) (dataOffset : Nat) :
    callDataCopyBytes data dataOffset 0 = [] := by
  simp [callDataCopyBytes]

/-- Indexing into the copied byte buffer recovers a `callDataByte` read
    at the corresponding source offset. Useful for stepping through the
    CALLDATACOPY loop spec one byte at a time. -/
theorem callDataCopyBytes_get
    {data : List (BitVec 8)} {dataOffset size : Nat} {i : Nat}
    (h : i < size) :
    (callDataCopyBytes data dataOffset size)[i]'(by
      simpa [callDataCopyBytes_length] using h)
      = callDataByte data (dataOffset + i) := by
  simp [callDataCopyBytes, List.getElem_map, List.getElem_range]

/-- Specialization of `callDataCopyBytes_get` to indices known to lie
    inside the source buffer: the result is the literal calldata byte. -/
theorem callDataCopyBytes_get_of_in_bounds
    {data : List (BitVec 8)} {dataOffset size : Nat} {i : Nat}
    (h : i < size) (hsrc : dataOffset + i < data.length) :
    (callDataCopyBytes data dataOffset size)[i]'(by
      simpa [callDataCopyBytes_length] using h)
      = data[dataOffset + i] := by
  rw [callDataCopyBytes_get h, callDataByte_of_lt hsrc]

/-- Specialization of `callDataCopyBytes_get` to indices past the source
    buffer: the result is the zero-padding byte. -/
theorem callDataCopyBytes_get_of_out_of_bounds
    {data : List (BitVec 8)} {dataOffset size : Nat} {i : Nat}
    (h : i < size) (hsrc : data.length ≤ dataOffset + i) :
    (callDataCopyBytes data dataOffset size)[i]'(by
      simpa [callDataCopyBytes_length] using h)
      = 0 := by
  rw [callDataCopyBytes_get h, callDataByte_of_ge hsrc]

@[simp] theorem callDataCopyBytes_nil (dataOffset size : Nat) :
    callDataCopyBytes [] dataOffset size = List.replicate size 0 := by
  apply List.ext_getElem
  · simp [callDataCopyBytes_length]
  · intro i h₁ h₂
    have hi : i < size := by simpa [callDataCopyBytes_length] using h₁
    rw [callDataCopyBytes_get hi, callDataByte_nil, List.getElem_replicate]

end Calldata
end EvmAsm.Evm64
