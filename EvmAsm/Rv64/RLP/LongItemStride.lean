/-
  EvmAsm.Rv64.RLP.LongItemStride

  EL.3 — the pure stride foundation for LONG RLP items (`longBytes` 0xB8–0xBF /
  `longList` 0xF8–0xFF), the long-class analog of `FlatListLoop.lean` §1
  (`isFlatItem` / `classifyPrefix_encode_head_flat` / `encode_head_eq_itemTotalLen`).

  A long item's encoding is `[prefix] ++ Nat.toBytesBE payloadCount ++ payload`
  with `prefix = 0xB7/0xF7 + lenOfLen` and `lenOfLen = (Nat.toBytesBE payloadCount).length`.
  Its per-item stride `1 + lenOfLen + payloadCount` (= `(encode item).length`) is
  **runtime-dependent** — the `payloadCount` is read from memory — so unlike the
  flat case it is NOT expressible as a prefix-only `itemTotalLen`. The unified
  list loop will instead re-index its pointer as `payloadPtr + payloadCount =
  v13 + (encode item).length`. This file proves the pieces that identity needs,
  purely (no machine state), from the existing spec lemmas: classification of the
  head byte, `lenOfLen ∈ [1,8]`, the length round-trip, the total-length
  decomposition, and the abstract pointer arithmetic.
-/

import EvmAsm.EL.RLP.Properties
import EvmAsm.Rv64.Instructions

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- `(BitVec.ofNat 8 k).toNat = k` for a byte-sized `k`. -/
private theorem toNat_ofNat8 {k : Nat} (h : k < 256) : (BitVec.ofNat 8 k).toNat = k := by
  rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from rfl]; omega

/-- `Nat.toBytesBE` of a positive number is non-empty. -/
private theorem toBytesBE_length_pos {n : Nat} (h : 0 < n) : 0 < (Nat.toBytesBE n).length := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.toBytesBE_succ, List.length_append, List.length_cons, List.length_nil]; omega

-- ============================================================================
-- Long items, payload count, length-of-length
-- ============================================================================

/-- An RLP item encoded in LONG form: a byte string with `> 55` bytes, or a list
    whose encoded payload exceeds `55` bytes. -/
def isLongItem : RLPItem → Prop
  | .bytes data => 55 < data.length
  | .list items => 55 < (encode.encodeItems items).length

/-- The payload byte-count encoded by a long item's length prefix. -/
def itemPayloadCount : RLPItem → Nat
  | .bytes data => data.length
  | .list items => (encode.encodeItems items).length

/-- Length-of-length: the number of big-endian length bytes in the encoding. -/
def itemLenOfLen (item : RLPItem) : Nat := (Nat.toBytesBE (itemPayloadCount item)).length

theorem itemLenOfLen_pos (item : RLPItem) (hlong : isLongItem item) : 0 < itemLenOfLen item := by
  cases item with
  | bytes data =>
    simp only [isLongItem] at hlong; simp only [itemLenOfLen, itemPayloadCount]
    exact toBytesBE_length_pos (by omega)
  | list items =>
    simp only [isLongItem] at hlong; simp only [itemLenOfLen, itemPayloadCount]
    exact toBytesBE_length_pos (by omega)

theorem itemLenOfLen_le_eight (item : RLPItem) (hsize : itemPayloadCount item < 256 ^ 8) :
    itemLenOfLen item ≤ 8 :=
  Nat.toBytesBE_length_le (itemPayloadCount item) 8 hsize

-- ============================================================================
-- Head byte of a long encoding
-- ============================================================================

/-- The head byte of a long byte-string encoding. -/
private theorem encode_long_head_bytes {data : List Byte} (hlong : 55 < data.length) :
    (encode (.bytes data))[0]'(encode_nonempty _)
      = BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length) := by
  have henc : encode (.bytes data)
      = [BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)]
          ++ Nat.toBytesBE data.length ++ data :=
    encodeBytes_long_of_length data hlong
  simp [henc]

/-- The head byte of a long list encoding. -/
private theorem encode_long_head_list {items : List RLPItem}
    (hlong : 55 < (encode.encodeItems items).length) :
    (encode (.list items))[0]'(encode_nonempty _)
      = BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length) := by
  have henc := encode_list_long items hlong
  simp [henc]

-- ============================================================================
-- Classification, length-of-length, total length
-- ============================================================================

/-- A long item's encoding's first byte classifies as `longBytes` or `longList`. -/
theorem classifyPrefix_encode_head_long (item : RLPItem) (hlong : isLongItem item)
    (hsize : itemPayloadCount item < 256 ^ 8) :
    classifyPrefix ((encode item)[0]'(encode_nonempty item)) = .longBytes
      ∨ classifyPrefix ((encode item)[0]'(encode_nonempty item)) = .longList := by
  cases item with
  | bytes data =>
    simp only [isLongItem] at hlong
    have hle : (Nat.toBytesBE data.length).length ≤ 8 :=
      Nat.toBytesBE_length_le data.length 8 (by simpa [itemPayloadCount] using hsize)
    have hpos : 0 < (Nat.toBytesBE data.length).length := toBytesBE_length_pos (by omega)
    left
    rw [encode_long_head_bytes hlong, classifyPrefix_longBytes_iff, toNat_ofNat8 (by omega)]
    omega
  | list items =>
    simp only [isLongItem] at hlong
    have hle : (Nat.toBytesBE (encode.encodeItems items).length).length ≤ 8 :=
      Nat.toBytesBE_length_le _ 8 (by simpa [itemPayloadCount] using hsize)
    have hpos : 0 < (Nat.toBytesBE (encode.encodeItems items).length).length :=
      toBytesBE_length_pos (by omega)
    right
    rw [encode_long_head_list hlong, classifyPrefix_longList_iff, toNat_ofNat8 (by omega)]
    omega

/-- The decoder's length-of-length (read off the prefix byte) equals the
    encoding's actual length-byte count — long byte-string case. -/
theorem encode_long_lenOfLen_eq_bytes {data : List Byte} (hlong : 55 < data.length)
    (hsize : data.length < 256 ^ 8) :
    rlpPrefixLongBytesLenOfLen ((encode (.bytes data))[0]'(encode_nonempty _))
      = itemLenOfLen (.bytes data) := by
  have hle : (Nat.toBytesBE data.length).length ≤ 8 := Nat.toBytesBE_length_le data.length 8 hsize
  rw [encode_long_head_bytes hlong, rlpPrefixLongBytesLenOfLen, toNat_ofNat8 (by omega)]
  simp only [itemLenOfLen, itemPayloadCount]; omega

/-- Length-of-length matches the encoding — long list case. -/
theorem encode_long_lenOfLen_eq_list {items : List RLPItem}
    (hlong : 55 < (encode.encodeItems items).length)
    (hsize : (encode.encodeItems items).length < 256 ^ 8) :
    rlpPrefixLongListLenOfLen ((encode (.list items))[0]'(encode_nonempty _))
      = itemLenOfLen (.list items) := by
  have hle : (Nat.toBytesBE (encode.encodeItems items).length).length ≤ 8 :=
    Nat.toBytesBE_length_le _ 8 hsize
  rw [encode_long_head_list hlong, rlpPrefixLongListLenOfLen, toNat_ofNat8 (by omega)]
  simp only [itemLenOfLen, itemPayloadCount]; omega

/-- **Total-length decomposition.** A long item's encoding is `1` (prefix) `+
    lenOfLen + payloadCount` bytes. -/
theorem encode_long_length_eq (item : RLPItem) (hlong : isLongItem item) :
    (encode item).length = 1 + itemLenOfLen item + itemPayloadCount item := by
  cases item with
  | bytes data =>
    simp only [isLongItem] at hlong
    have henc : encode (.bytes data)
        = [BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)]
            ++ Nat.toBytesBE data.length ++ data :=
      encodeBytes_long_of_length data hlong
    rw [henc]
    simp only [itemLenOfLen, itemPayloadCount, List.length_append, List.length_cons,
      List.length_nil]
  | list items =>
    simp only [isLongItem] at hlong
    rw [encode_list_long items hlong]
    simp only [itemLenOfLen, itemPayloadCount, List.length_cons, List.length_append]
    omega

/-- The big-endian length bytes round-trip back to the payload count (the read
    length the decoder recovers equals what the encoding committed to). -/
theorem encode_long_lenBytes_read (item : RLPItem) :
    Nat.fromBytesBE (Nat.toBytesBE (itemPayloadCount item)) = itemPayloadCount item :=
  Nat.fromBytesBE_toBytesBE _

-- ============================================================================
-- Abstract pointer-stride identity (decoder-agnostic)
-- ============================================================================

/-- The pointer advance for a long item: from `v13`, skip the prefix byte
    (`signExtend12 1`) and `lenOfLen` length bytes to the payload pointer, then
    add the `payloadCount` payload bytes — landing at `v13 + (total length)`. -/
theorem long_payloadPtr_add_len (v13 : Word) (lenOfLen payloadCount : Nat) :
    (v13 + signExtend12 (1 : BitVec 12) + BitVec.ofNat 64 lenOfLen)
        + BitVec.ofNat 64 payloadCount
      = v13 + BitVec.ofNat 64 (1 + lenOfLen + payloadCount) := by
  have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  rw [hse]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod,
    show (1 : Word).toNat = 1 from rfl]
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
  omega

/-- **Long-item stride.** Combining `long_payloadPtr_add_len` with the
    total-length decomposition: advancing `v13` past the header (`1 + lenOfLen`)
    to the payload pointer and then by the payload count lands exactly at
    `v13 + (encode item).length`. -/
theorem encode_long_stride (item : RLPItem) (hlong : isLongItem item) (v13 : Word) :
    (v13 + signExtend12 (1 : BitVec 12) + BitVec.ofNat 64 (itemLenOfLen item))
        + BitVec.ofNat 64 (itemPayloadCount item)
      = v13 + BitVec.ofNat 64 (encode item).length := by
  rw [long_payloadPtr_add_len, encode_long_length_eq item hlong]

-- ============================================================================
-- Sanity
-- ============================================================================

-- A 56-byte string is long: prefix `0xB8`, one length byte `56`, total `1+1+56`.
example : isLongItem (.bytes (List.replicate 56 (0 : Byte))) := by
  simp [isLongItem]

example :
    classifyPrefix ((encode (.bytes (List.replicate 56 (0 : Byte))))[0]'(encode_nonempty _))
      = .longBytes ∨
    classifyPrefix ((encode (.bytes (List.replicate 56 (0 : Byte))))[0]'(encode_nonempty _))
      = .longList :=
  classifyPrefix_encode_head_long _ (by simp [isLongItem]) (by simp [itemPayloadCount])

example (v13 : Word) :
    (v13 + signExtend12 (1 : BitVec 12) + BitVec.ofNat 64 2) + BitVec.ofNat 64 1000
      = v13 + BitVec.ofNat 64 (1 + 2 + 1000) :=
  long_payloadPtr_add_len v13 2 1000

end EvmAsm.Rv64.RLP
