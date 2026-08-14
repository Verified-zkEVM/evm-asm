/-
  EvmAsm.Codegen.Programs.TxSigningHashSpecPrefix

  Composed `rlp_encode_list_prefix` callWithin for K145 (#12038), covering the
  contiguous union of all nine per-form pinned rows (exhaustive on `Word`):

    short  [0, 56)
    long1  [56, 256)
    long2  [256, 2^16)
    long3  [2^16, 2^24)
    long4  [2^24, 2^32)
    long5  [2^32, 2^40)
    long6  [2^40, 2^48)
    long7  [2^48, 2^56)
    long8  [2^56, 2^64)   -- lo-only; `Word.isLt` supplies the hi bound

  No residual length gate: `tsh_prefix_any_callWithin` is total on `len : Word`.
  ABI framing (`out%8=0`, `9 ≤ |outBytes|` i.e. `8 < |out|`, byte-validity) is
  discharged at the pinned TSH call site (`tshPrefixOut_aligned`, zero-init
  16-byte slice of the existing 128 KiB `tsh_buf` — proof ownership only; no
  GuestAddrs / ELF move).

  Pure header model: `MptSpliceSlotSpec.rlpListPrefix`, applied via `tshPrefixApply`.
-/

import EvmAsm.Codegen.Programs.TxSigningHashSpecCore
import EvmAsm.Codegen.Programs.MptSpliceSlotSpec
import EvmAsm.Codegen.Programs.RlpEncodeBytesSAsm
import EvmAsm.Codegen.Programs.RlpBytesEncodedSizeBridge
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong2Spec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong3Spec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong4Spec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong5Spec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong6Spec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong7Spec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong8Spec

namespace EvmAsm.Codegen.TxSigningHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.MptSpliceSlotSpec
open EvmAsm.Codegen.RlpEncodeBytesSAsm
  (beShift beShift_length beShift_eq_toBytesBE beShift_cons
   truncate_shift_eq)
open EvmAsm.Codegen.RlpBytesEncodedSizeSAsm (toBytesBE_length_eq_of_bounds)
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- Fuel covering every arm through long8. -/
def tshPrefixFuel : Nat := 90

/-! ## Pure prefix write into an existing out buffer -/

/-- Header length written by `rlp_encode_list_prefix` for payload `len`. -/
def tshPrefixNH (len : Nat) : Nat := (rlpListPrefix len).length

/-- Set prefix bytes at indices `0 .. |pfx|-1` into `outBytes`.

    Defined as `pfx ++ outBytes.drop |pfx|` (requires `|pfx| ≤ |outBytes|` at
    use sites). Equivalent to successive `List.set` when the prefix fits, and
    makes `(tshPrefixApply …).take NH = rlpListPrefix` definitional. -/
def tshPrefixSet (outBytes : List (BitVec 8)) (pfx : List (BitVec 8)) : List (BitVec 8) :=
  pfx ++ outBytes.drop pfx.length

/-- Apply the RLP list-prefix encoding of `len` into `outBytes`. -/
def tshPrefixApply (outBytes : List (BitVec 8)) (len : Nat) : List (BitVec 8) :=
  tshPrefixSet outBytes (rlpListPrefix len)

/-- `pfx ++ drop` matches the successive-`set` form used by pinned posts. -/
private theorem tshPrefix_append_eq_set1 (outBytes : List (BitVec 8)) (a : BitVec 8)
    (h : 0 < outBytes.length) :
    [a] ++ outBytes.drop 1 = outBytes.set 0 a := by
  cases outBytes with
  | nil => cases h
  | cons _ xs => simp [List.set]

private theorem tshPrefix_append_eq_set2 (outBytes : List (BitVec 8)) (a b : BitVec 8)
    (h : 1 < outBytes.length) :
    [a, b] ++ outBytes.drop 2 = (outBytes.set 0 a).set 1 b := by
  match outBytes with
  | [] | [_] => simp at h
  | _ :: _ :: rest => simp [List.set]

private theorem tshPrefix_append_eq_set3 (outBytes : List (BitVec 8)) (a b c : BitVec 8)
    (h : 2 < outBytes.length) :
    [a, b, c] ++ outBytes.drop 3 = ((outBytes.set 0 a).set 1 b).set 2 c := by
  match outBytes with
  | [] | [_] | [_, _] => simp at h
  | _ :: _ :: _ :: rest => simp [List.set]

private theorem tshPrefix_append_eq_set4 (outBytes : List (BitVec 8))
    (a b c d : BitVec 8) (h : 3 < outBytes.length) :
    [a, b, c, d] ++ outBytes.drop 4 =
      (((outBytes.set 0 a).set 1 b).set 2 c).set 3 d := by
  match outBytes with
  | [] | [_] | [_, _] | [_, _, _] => simp at h
  | _ :: _ :: _ :: _ :: rest => simp [List.set]

private theorem tshPrefix_append_eq_set5 (outBytes : List (BitVec 8))
    (a b c d e : BitVec 8) (h : 4 < outBytes.length) :
    [a, b, c, d, e] ++ outBytes.drop 5 =
      ((((outBytes.set 0 a).set 1 b).set 2 c).set 3 d).set 4 e := by
  match outBytes with
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] => simp at h
  | _ :: _ :: _ :: _ :: _ :: rest => simp [List.set]

private theorem tshPrefix_append_eq_set6 (outBytes : List (BitVec 8))
    (a b c d e f : BitVec 8) (h : 5 < outBytes.length) :
    [a, b, c, d, e, f] ++ outBytes.drop 6 =
      (((((outBytes.set 0 a).set 1 b).set 2 c).set 3 d).set 4 e).set 5 f := by
  match outBytes with
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] => simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: rest => simp [List.set]

private theorem tshPrefix_append_eq_set7 (outBytes : List (BitVec 8))
    (a b c d e f g : BitVec 8) (h : 6 < outBytes.length) :
    [a, b, c, d, e, f, g] ++ outBytes.drop 7 =
      ((((((outBytes.set 0 a).set 1 b).set 2 c).set 3 d).set 4 e).set 5 f).set 6 g := by
  match outBytes with
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _]
  | [_, _, _, _, _, _] => simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest => simp [List.set]

private theorem tshPrefix_append_eq_set8 (outBytes : List (BitVec 8))
    (a b c d e f g i : BitVec 8) (h : 7 < outBytes.length) :
    [a, b, c, d, e, f, g, i] ++ outBytes.drop 8 =
      (((((((outBytes.set 0 a).set 1 b).set 2 c).set 3 d).set 4 e).set 5 f).set 6 g).set 7 i := by
  match outBytes with
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _]
  | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] => simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest => simp [List.set]

private theorem tshPrefix_append_eq_set9 (outBytes : List (BitVec 8))
    (a b c d e f g i j : BitVec 8) (h : 8 < outBytes.length) :
    [a, b, c, d, e, f, g, i, j] ++ outBytes.drop 9 =
      ((((((((outBytes.set 0 a).set 1 b).set 2 c).set 3 d).set 4 e).set 5 f).set 6 g).set 7 i).set 8 j := by
  match outBytes with
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _]
  | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] => simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest => simp [List.set]


/-- `writeShift`'s division byte equals the Word `>>>` form used by pinned posts. -/
theorem tshPrefix_byte_div_eq_shift (v : Word) (i : Nat) :
    BitVec.ofNat 8 (v.toNat / 256 ^ i % 256) =
      BitVec.ofNat 8 (v >>> (8 * i)).toNat := by
  have htrunc : (v >>> (8 * i)).truncate 8 =
      BitVec.ofNat 8 (v >>> (8 * i)).toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact (truncate_shift_eq v i).symm.trans htrunc

theorem tshPrefix_shift_zero (v : Word) : v >>> (0 : Nat) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  simp

/-- Long-form `rlpListPrefix` as tag + `beShift` length bytes. -/
theorem rlpListPrefix_eq_beShift (len k : Nat) (hle : 56 ≤ len)
    (hk : (Nat.toBytesBE len).length = k) :
    rlpListPrefix len = BitVec.ofNat 8 (0xF7 + k) :: beShift len k := by
  have hneg : ¬ len ≤ 55 := by omega
  simp only [rlpListPrefix, if_neg hneg, hk]
  rw [← beShift_eq_toBytesBE len, hk]

/-- Pin fact: prefix out slot (`tsh_buf+16`) is dword-aligned. -/
theorem tshPrefixOut_aligned : ((TshBuf + 16 : Word).toNat % 8 = 0) := by
  unfold TshBuf
  decide

/-- Physical BSS slot from prefix out to nth scratch is 48 bytes — covers every
    form through long8 (≤9 header bytes). -/
theorem tshPrefixSlot_bytes : (64 : Nat) - 16 = 48 := rfl

theorem tshPrefixNH_of_lt_56 (len : Nat) (h : len < 56) :
    tshPrefixNH len = 1 := by
  have hle : len ≤ 55 := Nat.lt_succ_iff.mp h
  simp only [tshPrefixNH, rlpListPrefix, if_pos hle, List.length_cons, List.length_nil]

/-- Every RLP list-prefix is nonempty (short tag or long tag + BE length). -/
theorem tshPrefixNH_pos (len : Nat) : 0 < tshPrefixNH len := by
  simp only [tshPrefixNH, rlpListPrefix]
  split <;> simp [List.length_cons]

theorem tshPrefixApply_of_lt_56 (outBytes : List (BitVec 8)) (len : Nat)
    (h : len < 56) (hlen : 0 < outBytes.length) :
    tshPrefixApply outBytes len =
      outBytes.set 0 (BitVec.ofNat 8 (0xC0 + len)) := by
  have hle : len ≤ 55 := Nat.lt_succ_iff.mp h
  simp only [tshPrefixApply, tshPrefixSet, rlpListPrefix, if_pos hle,
    List.length_cons, List.length_nil]
  exact tshPrefix_append_eq_set1 outBytes _ hlen

theorem tshPrefixApply_long1 (outBytes : List (BitVec 8)) (len : Nat)
    (hlo : 56 ≤ len) (hhi : len < 256) (hlen : 1 < outBytes.length) :
    tshPrefixApply outBytes len =
      (outBytes.set 0 (0xF8 : BitVec 8)).set 1 (BitVec.ofNat 8 len) := by
  rw [tshPrefixApply, rlpListPrefix_long1 len hlo hhi, tshPrefixSet]
  exact tshPrefix_append_eq_set2 outBytes _ _ hlen

theorem tshPrefixNH_long1 (len : Nat) (hlo : 56 ≤ len) (hhi : len < 256) :
    tshPrefixNH len = 2 := by
  rw [tshPrefixNH, rlpListPrefix_long1 len hlo hhi]
  simp only [List.length_cons, List.length_nil]

theorem tshPrefixNH_long2 (len : Nat) (hlo : 256 ≤ len) (hhi : len < 65536) :
    tshPrefixNH len = 3 := by
  have hk : (Nat.toBytesBE len).length = 2 :=
    toBytesBE_length_eq_of_bounds len 2 (by omega) (Or.inr (by omega))
  simp only [tshPrefixNH, rlpListPrefix, if_neg (by omega : ¬ len ≤ 55), hk,
    List.length_cons]

theorem tshPrefixNH_long3 (len : Nat) (hlo : 65536 ≤ len) (hhi : len < 16777216) :
    tshPrefixNH len = 4 := by
  have hk : (Nat.toBytesBE len).length = 3 :=
    toBytesBE_length_eq_of_bounds len 3 (by omega) (Or.inr (by omega))
  simp only [tshPrefixNH, rlpListPrefix, if_neg (by omega : ¬ len ≤ 55), hk,
    List.length_cons]

theorem tshPrefixNH_long4 (len : Nat) (hlo : 16777216 ≤ len) (hhi : len < 4294967296) :
    tshPrefixNH len = 5 := by
  have hk : (Nat.toBytesBE len).length = 4 :=
    toBytesBE_length_eq_of_bounds len 4 (by omega) (Or.inr (by omega))
  simp only [tshPrefixNH, rlpListPrefix, if_neg (by omega : ¬ len ≤ 55), hk,
    List.length_cons]

theorem tshPrefixNH_long5 (len : Nat) (hlo : 4294967296 ≤ len) (hhi : len < 1099511627776) :
    tshPrefixNH len = 6 := by
  have hk : (Nat.toBytesBE len).length = 5 :=
    toBytesBE_length_eq_of_bounds len 5 (by omega) (Or.inr (by omega))
  simp only [tshPrefixNH, rlpListPrefix, if_neg (by omega : ¬ len ≤ 55), hk,
    List.length_cons]

theorem tshPrefixNH_long6 (len : Nat) (hlo : 1099511627776 ≤ len)
    (hhi : len < 281474976710656) :
    tshPrefixNH len = 7 := by
  have hk : (Nat.toBytesBE len).length = 6 :=
    toBytesBE_length_eq_of_bounds len 6 (by omega) (Or.inr (by omega))
  simp only [tshPrefixNH, rlpListPrefix, if_neg (by omega : ¬ len ≤ 55), hk,
    List.length_cons]

theorem tshPrefixNH_long7 (len : Nat) (hlo : 281474976710656 ≤ len)
    (hhi : len < 72057594037927936) :
    tshPrefixNH len = 8 := by
  have hk : (Nat.toBytesBE len).length = 7 :=
    toBytesBE_length_eq_of_bounds len 7 (by omega) (Or.inr (by omega))
  simp only [tshPrefixNH, rlpListPrefix, if_neg (by omega : ¬ len ≤ 55), hk,
    List.length_cons]

theorem tshPrefixNH_long8 (len : Nat) (hlo : 72057594037927936 ≤ len)
    (hhi : len < 2 ^ 64) :
    tshPrefixNH len = 9 := by
  have hk : (Nat.toBytesBE len).length = 8 :=
    toBytesBE_length_eq_of_bounds len 8 (by omega) (Or.inr (by omega))
  simp only [tshPrefixNH, rlpListPrefix, if_neg (by omega : ¬ len ≤ 55), hk,
    List.length_cons]

theorem tshPrefixNH_le_9 (len : Nat) (h : len < 2 ^ 64) :
    tshPrefixNH len ≤ 9 := by
  by_cases c0 : len < 56
  · rw [tshPrefixNH_of_lt_56 len c0]; omega
  by_cases c1 : len < 256
  · rw [tshPrefixNH_long1 len (by omega) c1]; omega
  by_cases c2 : len < 65536
  · rw [tshPrefixNH_long2 len (by omega) c2]; omega
  by_cases c3 : len < 16777216
  · rw [tshPrefixNH_long3 len (by omega) c3]; omega
  by_cases c4 : len < 4294967296
  · rw [tshPrefixNH_long4 len (by omega) c4]; omega
  by_cases c5 : len < 1099511627776
  · rw [tshPrefixNH_long5 len (by omega) c5]; omega
  by_cases c6 : len < 281474976710656
  · rw [tshPrefixNH_long6 len (by omega) c6]; omega
  by_cases c7 : len < 72057594037927936
  · rw [tshPrefixNH_long7 len (by omega) c7]; omega
  rw [tshPrefixNH_long8 len (by omega) h]

theorem tshPrefixNH_le_8 (len : Nat) (h : len < 72057594037927936) :
    tshPrefixNH len ≤ 8 := by
  have h9 := tshPrefixNH_le_9 len (by omega)
  by_cases c0 : len < 56
  · rw [tshPrefixNH_of_lt_56 len c0]; omega
  by_cases c1 : len < 256
  · rw [tshPrefixNH_long1 len (by omega) c1]; omega
  by_cases c2 : len < 65536
  · rw [tshPrefixNH_long2 len (by omega) c2]; omega
  by_cases c3 : len < 16777216
  · rw [tshPrefixNH_long3 len (by omega) c3]; omega
  by_cases c4 : len < 4294967296
  · rw [tshPrefixNH_long4 len (by omega) c4]; omega
  by_cases c5 : len < 1099511627776
  · rw [tshPrefixNH_long5 len (by omega) c5]; omega
  by_cases c6 : len < 281474976710656
  · rw [tshPrefixNH_long6 len (by omega) c6]; omega
  rw [tshPrefixNH_long7 len (by omega) h]

theorem tshPrefixSet_length (outBytes pfx : List (BitVec 8))
    (h : pfx.length ≤ outBytes.length) :
    (tshPrefixSet outBytes pfx).length = outBytes.length := by
  simp only [tshPrefixSet, List.length_append, List.length_drop]
  omega

theorem tshPrefixApply_length (outBytes : List (BitVec 8)) (len : Nat)
    (h : tshPrefixNH len ≤ outBytes.length) :
    (tshPrefixApply outBytes len).length = outBytes.length :=
  tshPrefixSet_length outBytes (rlpListPrefix len) h

theorem tshPrefixApply_take_eq_hdr (outBytes : List (BitVec 8)) (len : Nat)
    (_hlen : tshPrefixNH len ≤ outBytes.length) :
    (tshPrefixApply outBytes len).take (tshPrefixNH len) = rlpListPrefix len := by
  simp only [tshPrefixApply, tshPrefixSet, tshPrefixNH]
  rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]

/-- `getByteAt` ignores a trailing zero replicate (matches `getByteAt` padding). -/
private theorem getByteAt_append_replicate_zero (hdr : List (BitVec 8)) (n j : Nat) :
    getByteAt (hdr ++ List.replicate n (0 : BitVec 8)) j = getByteAt hdr j := by
  unfold getByteAt
  by_cases hL : j < (hdr ++ List.replicate n (0 : BitVec 8)).length
  · simp only [hL, ↓reduceDIte]
    by_cases hH : j < hdr.length
    · simp only [hH, ↓reduceDIte, List.getElem_append_left hH]
    · have hge : hdr.length ≤ j := Nat.not_lt.mp hH
      simp only [hH, ↓reduceDIte]
      rw [List.getElem_append_right (as := hdr) (bs := List.replicate n (0 : BitVec 8)) hge]
      simp [List.getElem_replicate]
  · have : ¬ j < hdr.length := by
      intro h; exact hL (by simp [List.length_append, List.length_replicate]; omega)
    simp only [hL, this, ↓reduceDIte]

/-- Zero-filled 8-byte slot: applied prefix and bare header agree under `packBytes`.
    Retained for the short-domain Success path (`|out|=1` / 8-byte legacy). -/
theorem tshPrefixApply_replicate8_packBytes (len : Nat)
    (hhi : len < 72057594037927936) :
    packBytes (tshPrefixApply (List.replicate 8 (0 : BitVec 8)) len) =
      packBytes (rlpListPrefix len) := by
  have hnh := tshPrefixNH_le_8 len hhi
  have happly :
      tshPrefixApply (List.replicate 8 (0 : BitVec 8)) len =
        rlpListPrefix len ++ List.replicate (8 - tshPrefixNH len) 0 := by
    simp only [tshPrefixApply, tshPrefixSet, tshPrefixNH, List.drop_replicate]
  apply eq_of_forall_extractByte
  intro j hj
  rw [extractByte_packBytes_total _ j hj, extractByte_packBytes_total _ j hj]
  rw [happly, getByteAt_append_replicate_zero]

/-- Same physical dword assertion for Apply-into-zeros vs bare header (8-byte slot). -/
theorem tshPrefix_bytesRegion_apply_eq_hdr (outPtr : Word) (len : Nat)
    (hhi : len < 72057594037927936) (hpos : 0 < tshPrefixNH len) :
    bytesRegion outPtr (tshPrefixApply (List.replicate 8 (0 : BitVec 8)) len) =
      bytesRegion outPtr (rlpListPrefix len) := by
  have hnh := tshPrefixNH_le_8 len hhi
  have hlenA : (tshPrefixApply (List.replicate 8 (0 : BitVec 8)) len).length = 8 := by
    rw [tshPrefixApply_length _ _ (by
      change tshPrefixNH len ≤ 8; exact hnh)]
    decide
  have hlenH : 0 < (rlpListPrefix len).length := by simpa [tshPrefixNH] using hpos
  have hleH : (rlpListPrefix len).length ≤ 8 := by simpa [tshPrefixNH] using hnh
  have hchunkA : ((tshPrefixApply (List.replicate 8 (0 : BitVec 8)) len).length + 7) / 8 = 1 := by
    omega
  have hchunkH : ((rlpListPrefix len).length + 7) / 8 = 1 := by omega
  simp only [bytesRegion, hchunkA, hchunkH, bytesRegionAux]
  have hp := tshPrefixApply_replicate8_packBytes len hhi
  have htA : (tshPrefixApply (List.replicate 8 (0 : BitVec 8)) len).take 8 =
      tshPrefixApply (List.replicate 8 (0 : BitVec 8)) len := by
    apply List.take_of_length_le; omega
  have htH : (rlpListPrefix len).take 8 = rlpListPrefix len := by
    apply List.take_of_length_le; exact hleH
  simp only [htA, htH, hp, sepConj_emp_right']

/-- Apply into a 16-byte zero slot (covers long8's 9-byte header). -/
theorem tshPrefixApply_replicate16_eq (len : Nat) (_hnh : tshPrefixNH len ≤ 16) :
    tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len =
      rlpListPrefix len ++ List.replicate (16 - tshPrefixNH len) 0 := by
  simp only [tshPrefixApply, tshPrefixSet, tshPrefixNH, List.drop_replicate]

/-- Zero-filled 16-byte slot: applied prefix and bare header agree under `packBytes`. -/
theorem tshPrefixApply_replicate16_packBytes (len : Nat) (hhi : len < 2 ^ 64) :
    packBytes (tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len) =
      packBytes (rlpListPrefix len) := by
  have hnh := tshPrefixNH_le_9 len hhi
  have happly := tshPrefixApply_replicate16_eq len (by omega)
  apply eq_of_forall_extractByte
  intro j hj
  rw [extractByte_packBytes_total _ j hj, extractByte_packBytes_total _ j hj]
  rw [happly, getByteAt_append_replicate_zero]

/-- First 8 bytes of Apply16 when `NH ≤ 8`: header padded to one dword. -/
private theorem tshPrefixApply16_take8_of_le_8 (len : Nat)
    (hnh : tshPrefixNH len ≤ 8) :
    (tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len).take 8 =
      rlpListPrefix len ++ List.replicate (8 - tshPrefixNH len) 0 := by
  have happly := tshPrefixApply_replicate16_eq len (by omega)
  have hle : (rlpListPrefix len).length ≤ 8 := by simpa [tshPrefixNH] using hnh
  have hsub : 8 - tshPrefixNH len ≤ 16 - tshPrefixNH len := by omega
  have hlen : (rlpListPrefix len).length = tshPrefixNH len := rfl
  rw [happly, List.take_append, List.take_of_length_le hle, hlen,
    List.take_replicate, Nat.min_eq_left hsub]

/-- Trailing dword of Apply16 when `NH ≤ 8` is eight zeros. -/
private theorem tshPrefixApply16_drop8_of_le_8 (len : Nat)
    (hnh : tshPrefixNH len ≤ 8) :
    (tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len).drop 8 =
      List.replicate 8 (0 : BitVec 8) := by
  have happly := tshPrefixApply_replicate16_eq len (by omega)
  have hle : (rlpListPrefix len).length ≤ 8 := by simpa [tshPrefixNH] using hnh
  rw [happly, List.drop_append, List.drop_of_length_le hle, List.nil_append,
    List.drop_replicate]
  -- (16 - NH) - (8 - NH) = 8
  change List.replicate (16 - tshPrefixNH len - (8 - tshPrefixNH len)) 0 =
    List.replicate 8 0
  congr 1
  omega

/-- `len < 2^56`: Apply16 = hdr-region (1 dword) ** trailing zero dword. -/
theorem tshPrefix_bytesRegion_apply16_eq_hdr_lt_2_56 (outPtr : Word) (len : Nat)
    (hhi : len < 72057594037927936) (hpos : 0 < tshPrefixNH len) :
    bytesRegion outPtr (tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len) =
      (bytesRegion outPtr (rlpListPrefix len) **
        bytesRegion (outPtr + 8) (List.replicate 8 (0 : BitVec 8))) := by
  have hnh := tshPrefixNH_le_8 len hhi
  have hlenA : (tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len).length = 16 := by
    have hle : tshPrefixNH len ≤ 16 := by omega
    simpa [List.length_replicate] using
      tshPrefixApply_length (List.replicate 16 (0 : BitVec 8)) len hle
  have htake := tshPrefixApply16_take8_of_le_8 len hnh
  have hdrop := tshPrefixApply16_drop8_of_le_8 len hnh
  have hpack : packBytes
      (rlpListPrefix len ++ List.replicate (8 - tshPrefixNH len) 0) =
      packBytes (rlpListPrefix len) := by
    apply eq_of_forall_extractByte
    intro j hj
    rw [extractByte_packBytes_total _ j hj, extractByte_packBytes_total _ j hj,
      getByteAt_append_replicate_zero]
  have hchunkA : ((tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len).length + 7) / 8 = 2 := by
    omega
  have hchunkH : ((rlpListPrefix len).length + 7) / 8 = 1 := by
    have hle : (rlpListPrefix len).length ≤ 8 := by simpa [tshPrefixNH] using hnh
    have hpos' : 0 < (rlpListPrefix len).length := by simpa [tshPrefixNH] using hpos
    omega
  have hchunkZ : ((List.replicate 8 (0 : BitVec 8)).length + 7) / 8 = 1 := by decide
  have htH : (rlpListPrefix len).take 8 = rlpListPrefix len := by
    apply List.take_of_length_le; simpa [tshPrefixNH] using hnh
  have hz : (List.replicate 8 (0 : BitVec 8)).take 8 = List.replicate 8 (0 : BitVec 8) := rfl
  have hdt :
      ((tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len).drop 8).take 8 =
        List.replicate 8 (0 : BitVec 8) := by
    rw [hdrop]; rfl
  -- Expand both sides to dword atoms, then reassociate the emp pads.
  simp only [bytesRegion, hchunkA, hchunkH, hchunkZ, bytesRegionAux, htake, hdt, htH, hz,
    hpack]
  -- LHS: A ** B ** emp ; RHS: (A ** emp) ** (B ** emp)
  simp only [sepConj_emp_right']

/-- `2^56 ≤ len < 2^64`: Apply16 and bare 9-byte hdr agree as 2-dword regions. -/
theorem tshPrefix_bytesRegion_apply16_eq_hdr_ge_2_56 (outPtr : Word) (len : Nat)
    (hlo : 72057594037927936 ≤ len) (hhi : len < 2 ^ 64) :
    bytesRegion outPtr (tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len) =
      bytesRegion outPtr (rlpListPrefix len) := by
  have hnh : tshPrefixNH len = 9 := tshPrefixNH_long8 len hlo hhi
  have happly := tshPrefixApply_replicate16_eq len (by rw [hnh]; decide)
  have hlenA : (tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len).length = 16 := by
    have hle : tshPrefixNH len ≤ 16 := by rw [hnh]; decide
    simpa [List.length_replicate] using
      tshPrefixApply_length (List.replicate 16 (0 : BitVec 8)) len hle
  have hlenH : (rlpListPrefix len).length = 9 := by simpa [tshPrefixNH] using hnh
  have hchunkA : ((tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len).length + 7) / 8 = 2 := by
    omega
  have hchunkH : ((rlpListPrefix len).length + 7) / 8 = 2 := by omega
  have htA : (tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len).take 8 =
      (rlpListPrefix len).take 8 := by
    rw [happly, List.take_append_of_le_length (by omega : 8 ≤ (rlpListPrefix len).length)]
  have hdA :
      (tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len).drop 8 =
        (rlpListPrefix len).drop 8 ++ List.replicate 7 (0 : BitVec 8) := by
    rw [happly, List.drop_append_of_le_length (by omega : 8 ≤ (rlpListPrefix len).length)]
    simp only [hnh]
  have hp0 : packBytes
      ((tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len).take 8) =
      packBytes ((rlpListPrefix len).take 8) := by
    rw [htA]
  have htDropA :
      ((tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len).drop 8).take 8 =
        (rlpListPrefix len).drop 8 ++ List.replicate 7 (0 : BitVec 8) := by
    rw [hdA]
    have hlen8 :
        ((rlpListPrefix len).drop 8 ++ List.replicate 7 (0 : BitVec 8)).length = 8 := by
      simp [List.length_append, List.length_drop, hlenH]
    exact List.take_of_length_le (le_of_eq hlen8)
  have htDropH : ((rlpListPrefix len).drop 8).take 8 = (rlpListPrefix len).drop 8 := by
    apply List.take_of_length_le
    simp [List.length_drop, hlenH]
  have hp1 : packBytes
      (((tshPrefixApply (List.replicate 16 (0 : BitVec 8)) len).drop 8).take 8) =
      packBytes (((rlpListPrefix len).drop 8).take 8) := by
    rw [htDropA, htDropH]
    apply eq_of_forall_extractByte
    intro j hj
    rw [extractByte_packBytes_total _ j hj, extractByte_packBytes_total _ j hj,
      getByteAt_append_replicate_zero]
  -- Rewrite packBytes atoms only; do not expand the takes into mismatched shapes.
  simp only [bytesRegion, hchunkA, hchunkH, bytesRegionAux, hp0, hp1]

/-! ## Short form, rewritten to `tshPrefixApply` post -/

theorem tsh_prefix_short_apply_in_fullCode
    (len outPtr cellPtr raVal v5 v6 v7 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len : len.toNat < 56)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 0 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 8 PrefixB (raVal &&& ~~~1) fullCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
       (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))) := by
  have h := tsh_prefix_short_in_fullCode len outPtr cellPtr raVal v5 v6 v7
    outBytes cellOld h_len h_out_align h_out_len h_out_valid
  have happly := tshPrefixApply_of_lt_56 outBytes len.toNat h_len h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (1 : Word) := by
    rw [tshPrefixNH_of_lt_56 len.toNat h_len]; rfl
  simpa [happly, hnh] using h

theorem tsh_prefix_long1_in_fullCode
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 56 ≤ len.toNat)
    (h_len_hi : len.toNat < 256)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 1 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 22 PrefixB (raVal &&& ~~~1) fullCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
       (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))) := by
  have h := cpsTripleWithin_extend_code prefix_mono
    (EvmAsm.Codegen.RlpSpliceHelperSpec.rlp_encode_list_prefix_long1_pinned_spec_within
      PrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
      outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid)
  have happly := tshPrefixApply_long1 outBytes len.toNat h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (2 : Word) := by
    rw [tshPrefixNH_long1 len.toNat h_len_lo h_len_hi]; rfl
  simpa [happly, hnh] using h

theorem tshPrefixApply_long2 (outBytes : List (BitVec 8)) (len : Word)
    (hlo : 256 ≤ len.toNat) (hhi : len.toNat < 65536) (hlen : 2 < outBytes.length) :
    tshPrefixApply outBytes len.toNat =
      ((outBytes.set 0 (0xf9 : BitVec 8)).set 1 (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 2 (BitVec.ofNat 8 len.toNat) := by
  have hk : (Nat.toBytesBE len.toNat).length = 2 :=
    toBytesBE_length_eq_of_bounds len.toNat 2 (by omega) (Or.inr (by omega))
  have hpfx := rlpListPrefix_eq_beShift len.toNat 2 (by omega) hk
  have hbe : beShift len.toNat 2 =
      [BitVec.ofNat 8 (len.toNat / 256 ^1 % 256), BitVec.ofNat 8 (len.toNat % 256)] := by
    rw [beShift_cons 1 len.toNat,
      beShift_cons 0 len.toNat]
    simp only [beShift, Nat.pow_one, Nat.pow_zero, Nat.div_one]
  have h1 := tshPrefix_byte_div_eq_shift len 1
  rw [show 8 * 1 = 8 from by norm_num] at h1
  have hlow : BitVec.ofNat 8 (len.toNat % 256) = BitVec.ofNat 8 len.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [tshPrefixApply, hpfx, hbe, tshPrefixSet,
    show BitVec.ofNat 8 (0xF7 + 2) = (0xf9 : BitVec 8) from by decide, h1, hlow]
  exact tshPrefix_append_eq_set3 outBytes _ _ _ hlen

theorem tsh_prefix_long2_in_fullCode
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 256 ≤ len.toNat)
    (h_len_hi : len.toNat < 65536)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 2 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 32 PrefixB (raVal &&& ~~~1) fullCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
       (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))) := by
  have h := cpsTripleWithin_extend_code prefix_mono
    (RlpEncodeListPrefixLong2Spec.rlp_encode_list_prefix_long2_pinned_spec_within
      PrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
      outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid)
  have happly := tshPrefixApply_long2 outBytes len h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (3 : Word) := by
    rw [tshPrefixNH_long2 len.toNat h_len_lo h_len_hi]; rfl
  simpa [happly, hnh] using h

theorem tshPrefixApply_long3 (outBytes : List (BitVec 8)) (len : Word)
    (hlo : 65536 ≤ len.toNat) (hhi : len.toNat < 16777216) (hlen : 3 < outBytes.length) :
    tshPrefixApply outBytes len.toNat =
      (((outBytes.set 0 (0xfa : BitVec 8)).set 1 (BitVec.ofNat 8 (len >>> (16 : Nat)).toNat)).set 2 (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 3 (BitVec.ofNat 8 len.toNat) := by
  have hk : (Nat.toBytesBE len.toNat).length = 3 :=
    toBytesBE_length_eq_of_bounds len.toNat 3 (by omega) (Or.inr (by omega))
  have hpfx := rlpListPrefix_eq_beShift len.toNat 3 (by omega) hk
  have hbe : beShift len.toNat 3 =
      [BitVec.ofNat 8 (len.toNat / 256 ^2 % 256), BitVec.ofNat 8 (len.toNat / 256 ^1 % 256), BitVec.ofNat 8 (len.toNat % 256)] := by
    rw [beShift_cons 2 len.toNat,
      beShift_cons 1 len.toNat,
      beShift_cons 0 len.toNat]
    simp only [beShift, Nat.pow_one, Nat.pow_zero, Nat.div_one]
  have h2 := tshPrefix_byte_div_eq_shift len 2
  rw [show 8 * 2 = 16 from by norm_num] at h2
  have h1 := tshPrefix_byte_div_eq_shift len 1
  rw [show 8 * 1 = 8 from by norm_num] at h1
  have hlow : BitVec.ofNat 8 (len.toNat % 256) = BitVec.ofNat 8 len.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [tshPrefixApply, hpfx, hbe, tshPrefixSet,
    show BitVec.ofNat 8 (0xF7 + 3) = (0xfa : BitVec 8) from by decide, h2, h1, hlow]
  exact tshPrefix_append_eq_set4 outBytes _ _ _ _ hlen

theorem tsh_prefix_long3_in_fullCode
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 65536 ≤ len.toNat)
    (h_len_hi : len.toNat < 16777216)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 3 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 42 PrefixB (raVal &&& ~~~1) fullCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
       (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))) := by
  have h := cpsTripleWithin_extend_code prefix_mono
    (RlpEncodeListPrefixLong3Spec.rlp_encode_list_prefix_long3_pinned_spec_within
      PrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
      outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid)
  have happly := tshPrefixApply_long3 outBytes len h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (4 : Word) := by
    rw [tshPrefixNH_long3 len.toNat h_len_lo h_len_hi]; rfl
  simpa [happly, hnh] using h

theorem tshPrefixApply_long4 (outBytes : List (BitVec 8)) (len : Word)
    (hlo : 16777216 ≤ len.toNat) (hhi : len.toNat < 4294967296) (hlen : 4 < outBytes.length) :
    tshPrefixApply outBytes len.toNat =
      ((((outBytes.set 0 (0xfb : BitVec 8)).set 1 (BitVec.ofNat 8 (len >>> (24 : Nat)).toNat)).set 2 (BitVec.ofNat 8 (len >>> (16 : Nat)).toNat)).set 3 (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 4 (BitVec.ofNat 8 len.toNat) := by
  have hk : (Nat.toBytesBE len.toNat).length = 4 :=
    toBytesBE_length_eq_of_bounds len.toNat 4 (by omega) (Or.inr (by omega))
  have hpfx := rlpListPrefix_eq_beShift len.toNat 4 (by omega) hk
  have hbe : beShift len.toNat 4 =
      [BitVec.ofNat 8 (len.toNat / 256 ^3 % 256), BitVec.ofNat 8 (len.toNat / 256 ^2 % 256), BitVec.ofNat 8 (len.toNat / 256 ^1 % 256), BitVec.ofNat 8 (len.toNat % 256)] := by
    rw [beShift_cons 3 len.toNat,
      beShift_cons 2 len.toNat,
      beShift_cons 1 len.toNat,
      beShift_cons 0 len.toNat]
    simp only [beShift, Nat.pow_one, Nat.pow_zero, Nat.div_one]
  have h3 := tshPrefix_byte_div_eq_shift len 3
  rw [show 8 * 3 = 24 from by norm_num] at h3
  have h2 := tshPrefix_byte_div_eq_shift len 2
  rw [show 8 * 2 = 16 from by norm_num] at h2
  have h1 := tshPrefix_byte_div_eq_shift len 1
  rw [show 8 * 1 = 8 from by norm_num] at h1
  have hlow : BitVec.ofNat 8 (len.toNat % 256) = BitVec.ofNat 8 len.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [tshPrefixApply, hpfx, hbe, tshPrefixSet,
    show BitVec.ofNat 8 (0xF7 + 4) = (0xfb : BitVec 8) from by decide, h3, h2, h1, hlow]
  exact tshPrefix_append_eq_set5 outBytes _ _ _ _ _ hlen

theorem tsh_prefix_long4_in_fullCode
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 16777216 ≤ len.toNat)
    (h_len_hi : len.toNat < 4294967296)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 4 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 52 PrefixB (raVal &&& ~~~1) fullCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
       (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))) := by
  have h := cpsTripleWithin_extend_code prefix_mono
    (RlpEncodeListPrefixLong4Spec.rlp_encode_list_prefix_long4_pinned_spec_within
      PrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
      outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid)
  have happly := tshPrefixApply_long4 outBytes len h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (5 : Word) := by
    rw [tshPrefixNH_long4 len.toNat h_len_lo h_len_hi]; rfl
  simpa [happly, hnh] using h

theorem tshPrefixApply_long5 (outBytes : List (BitVec 8)) (len : Word)
    (hlo : 4294967296 ≤ len.toNat) (hhi : len.toNat < 1099511627776) (hlen : 5 < outBytes.length) :
    tshPrefixApply outBytes len.toNat =
      (((((outBytes.set 0 (0xfc : BitVec 8)).set 1 (BitVec.ofNat 8 (len >>> (32 : Nat)).toNat)).set 2 (BitVec.ofNat 8 (len >>> (24 : Nat)).toNat)).set 3 (BitVec.ofNat 8 (len >>> (16 : Nat)).toNat)).set 4 (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 5 (BitVec.ofNat 8 len.toNat) := by
  have hk : (Nat.toBytesBE len.toNat).length = 5 :=
    toBytesBE_length_eq_of_bounds len.toNat 5 (by omega) (Or.inr (by omega))
  have hpfx := rlpListPrefix_eq_beShift len.toNat 5 (by omega) hk
  have hbe : beShift len.toNat 5 =
      [BitVec.ofNat 8 (len.toNat / 256 ^4 % 256), BitVec.ofNat 8 (len.toNat / 256 ^3 % 256), BitVec.ofNat 8 (len.toNat / 256 ^2 % 256), BitVec.ofNat 8 (len.toNat / 256 ^1 % 256), BitVec.ofNat 8 (len.toNat % 256)] := by
    rw [beShift_cons 4 len.toNat,
      beShift_cons 3 len.toNat,
      beShift_cons 2 len.toNat,
      beShift_cons 1 len.toNat,
      beShift_cons 0 len.toNat]
    simp only [beShift, Nat.pow_one, Nat.pow_zero, Nat.div_one]
  have h4 := tshPrefix_byte_div_eq_shift len 4
  rw [show 8 * 4 = 32 from by norm_num] at h4
  have h3 := tshPrefix_byte_div_eq_shift len 3
  rw [show 8 * 3 = 24 from by norm_num] at h3
  have h2 := tshPrefix_byte_div_eq_shift len 2
  rw [show 8 * 2 = 16 from by norm_num] at h2
  have h1 := tshPrefix_byte_div_eq_shift len 1
  rw [show 8 * 1 = 8 from by norm_num] at h1
  have hlow : BitVec.ofNat 8 (len.toNat % 256) = BitVec.ofNat 8 len.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [tshPrefixApply, hpfx, hbe, tshPrefixSet,
    show BitVec.ofNat 8 (0xF7 + 5) = (0xfc : BitVec 8) from by decide, h4, h3, h2, h1, hlow]
  exact tshPrefix_append_eq_set6 outBytes _ _ _ _ _ _ hlen

theorem tsh_prefix_long5_in_fullCode
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 4294967296 ≤ len.toNat)
    (h_len_hi : len.toNat < 1099511627776)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 5 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 62 PrefixB (raVal &&& ~~~1) fullCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
       (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))) := by
  have h := cpsTripleWithin_extend_code prefix_mono
    (RlpEncodeListPrefixLong5Spec.rlp_encode_list_prefix_long5_pinned_spec_within
      PrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
      outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid)
  have happly := tshPrefixApply_long5 outBytes len h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (6 : Word) := by
    rw [tshPrefixNH_long5 len.toNat h_len_lo h_len_hi]; rfl
  simpa [happly, hnh] using h

theorem tshPrefixApply_long6 (outBytes : List (BitVec 8)) (len : Word)
    (hlo : 1099511627776 ≤ len.toNat) (hhi : len.toNat < 281474976710656) (hlen : 6 < outBytes.length) :
    tshPrefixApply outBytes len.toNat =
      ((((((outBytes.set 0 (0xfd : BitVec 8)).set 1 (BitVec.ofNat 8 (len >>> (40 : Nat)).toNat)).set 2 (BitVec.ofNat 8 (len >>> (32 : Nat)).toNat)).set 3 (BitVec.ofNat 8 (len >>> (24 : Nat)).toNat)).set 4 (BitVec.ofNat 8 (len >>> (16 : Nat)).toNat)).set 5 (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 6 (BitVec.ofNat 8 len.toNat) := by
  have hk : (Nat.toBytesBE len.toNat).length = 6 :=
    toBytesBE_length_eq_of_bounds len.toNat 6 (by omega) (Or.inr (by omega))
  have hpfx := rlpListPrefix_eq_beShift len.toNat 6 (by omega) hk
  have hbe : beShift len.toNat 6 =
      [BitVec.ofNat 8 (len.toNat / 256 ^5 % 256), BitVec.ofNat 8 (len.toNat / 256 ^4 % 256), BitVec.ofNat 8 (len.toNat / 256 ^3 % 256), BitVec.ofNat 8 (len.toNat / 256 ^2 % 256), BitVec.ofNat 8 (len.toNat / 256 ^1 % 256), BitVec.ofNat 8 (len.toNat % 256)] := by
    rw [beShift_cons 5 len.toNat,
      beShift_cons 4 len.toNat,
      beShift_cons 3 len.toNat,
      beShift_cons 2 len.toNat,
      beShift_cons 1 len.toNat,
      beShift_cons 0 len.toNat]
    simp only [beShift, Nat.pow_one, Nat.pow_zero, Nat.div_one]
  have h5 := tshPrefix_byte_div_eq_shift len 5
  rw [show 8 * 5 = 40 from by norm_num] at h5
  have h4 := tshPrefix_byte_div_eq_shift len 4
  rw [show 8 * 4 = 32 from by norm_num] at h4
  have h3 := tshPrefix_byte_div_eq_shift len 3
  rw [show 8 * 3 = 24 from by norm_num] at h3
  have h2 := tshPrefix_byte_div_eq_shift len 2
  rw [show 8 * 2 = 16 from by norm_num] at h2
  have h1 := tshPrefix_byte_div_eq_shift len 1
  rw [show 8 * 1 = 8 from by norm_num] at h1
  have hlow : BitVec.ofNat 8 (len.toNat % 256) = BitVec.ofNat 8 len.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [tshPrefixApply, hpfx, hbe, tshPrefixSet,
    show BitVec.ofNat 8 (0xF7 + 6) = (0xfd : BitVec 8) from by decide, h5, h4, h3, h2, h1, hlow]
  exact tshPrefix_append_eq_set7 outBytes _ _ _ _ _ _ _ hlen

theorem tsh_prefix_long6_in_fullCode
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 1099511627776 ≤ len.toNat)
    (h_len_hi : len.toNat < 281474976710656)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 6 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 72 PrefixB (raVal &&& ~~~1) fullCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
       (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))) := by
  have h := cpsTripleWithin_extend_code prefix_mono
    (RlpEncodeListPrefixLong6Spec.rlp_encode_list_prefix_long6_pinned_spec_within
      PrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
      outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid)
  have happly := tshPrefixApply_long6 outBytes len h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (7 : Word) := by
    rw [tshPrefixNH_long6 len.toNat h_len_lo h_len_hi]; rfl
  simpa [happly, hnh] using h

theorem tshPrefixApply_long7 (outBytes : List (BitVec 8)) (len : Word)
    (hlo : 281474976710656 ≤ len.toNat) (hhi : len.toNat < 72057594037927936) (hlen : 7 < outBytes.length) :
    tshPrefixApply outBytes len.toNat =
      (((((((outBytes.set 0 (0xfe : BitVec 8)).set 1 (BitVec.ofNat 8 (len >>> (48 : Nat)).toNat)).set 2 (BitVec.ofNat 8 (len >>> (40 : Nat)).toNat)).set 3 (BitVec.ofNat 8 (len >>> (32 : Nat)).toNat)).set 4 (BitVec.ofNat 8 (len >>> (24 : Nat)).toNat)).set 5 (BitVec.ofNat 8 (len >>> (16 : Nat)).toNat)).set 6 (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 7 (BitVec.ofNat 8 len.toNat) := by
  have hk : (Nat.toBytesBE len.toNat).length = 7 :=
    toBytesBE_length_eq_of_bounds len.toNat 7 (by omega) (Or.inr (by omega))
  have hpfx := rlpListPrefix_eq_beShift len.toNat 7 (by omega) hk
  have hbe : beShift len.toNat 7 =
      [BitVec.ofNat 8 (len.toNat / 256 ^6 % 256), BitVec.ofNat 8 (len.toNat / 256 ^5 % 256), BitVec.ofNat 8 (len.toNat / 256 ^4 % 256), BitVec.ofNat 8 (len.toNat / 256 ^3 % 256), BitVec.ofNat 8 (len.toNat / 256 ^2 % 256), BitVec.ofNat 8 (len.toNat / 256 ^1 % 256), BitVec.ofNat 8 (len.toNat % 256)] := by
    rw [beShift_cons 6 len.toNat,
      beShift_cons 5 len.toNat,
      beShift_cons 4 len.toNat,
      beShift_cons 3 len.toNat,
      beShift_cons 2 len.toNat,
      beShift_cons 1 len.toNat,
      beShift_cons 0 len.toNat]
    simp only [beShift, Nat.pow_one, Nat.pow_zero, Nat.div_one]
  have h6 := tshPrefix_byte_div_eq_shift len 6
  rw [show 8 * 6 = 48 from by norm_num] at h6
  have h5 := tshPrefix_byte_div_eq_shift len 5
  rw [show 8 * 5 = 40 from by norm_num] at h5
  have h4 := tshPrefix_byte_div_eq_shift len 4
  rw [show 8 * 4 = 32 from by norm_num] at h4
  have h3 := tshPrefix_byte_div_eq_shift len 3
  rw [show 8 * 3 = 24 from by norm_num] at h3
  have h2 := tshPrefix_byte_div_eq_shift len 2
  rw [show 8 * 2 = 16 from by norm_num] at h2
  have h1 := tshPrefix_byte_div_eq_shift len 1
  rw [show 8 * 1 = 8 from by norm_num] at h1
  have hlow : BitVec.ofNat 8 (len.toNat % 256) = BitVec.ofNat 8 len.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [tshPrefixApply, hpfx, hbe, tshPrefixSet,
    show BitVec.ofNat 8 (0xF7 + 7) = (0xfe : BitVec 8) from by decide, h6, h5, h4, h3, h2, h1, hlow]
  exact tshPrefix_append_eq_set8 outBytes _ _ _ _ _ _ _ _ hlen

theorem tsh_prefix_long7_in_fullCode
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 281474976710656 ≤ len.toNat)
    (h_len_hi : len.toNat < 72057594037927936)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 7 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 82 PrefixB (raVal &&& ~~~1) fullCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
       (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))) := by
  have h := cpsTripleWithin_extend_code prefix_mono
    (RlpEncodeListPrefixLong7Spec.rlp_encode_list_prefix_long7_pinned_spec_within
      PrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
      outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid)
  have happly := tshPrefixApply_long7 outBytes len h_len_lo h_len_hi h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (8 : Word) := by
    rw [tshPrefixNH_long7 len.toNat h_len_lo h_len_hi]; rfl
  simpa [happly, hnh] using h

theorem tshPrefixApply_long8 (outBytes : List (BitVec 8)) (len : Word)
    (hlo : 72057594037927936 ≤ len.toNat) (hhi : len.toNat < 2 ^ 64)
    (hlen : 8 < outBytes.length) :
    tshPrefixApply outBytes len.toNat =
      ((((((((outBytes.set 0 (0xff : BitVec 8)).set 1
          (BitVec.ofNat 8 (len >>> (56 : Nat)).toNat)).set 2
          (BitVec.ofNat 8 (len >>> (48 : Nat)).toNat)).set 3
          (BitVec.ofNat 8 (len >>> (40 : Nat)).toNat)).set 4
          (BitVec.ofNat 8 (len >>> (32 : Nat)).toNat)).set 5
          (BitVec.ofNat 8 (len >>> (24 : Nat)).toNat)).set 6
          (BitVec.ofNat 8 (len >>> (16 : Nat)).toNat)).set 7
          (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 8
          (BitVec.ofNat 8 len.toNat) := by
  have hk : (Nat.toBytesBE len.toNat).length = 8 :=
    toBytesBE_length_eq_of_bounds len.toNat 8 (by omega) (Or.inr (by omega))
  have hpfx := rlpListPrefix_eq_beShift len.toNat 8 (by omega) hk
  have hbe : beShift len.toNat 8 =
      [BitVec.ofNat 8 (len.toNat / 256 ^7 % 256), BitVec.ofNat 8 (len.toNat / 256 ^6 % 256),
       BitVec.ofNat 8 (len.toNat / 256 ^5 % 256), BitVec.ofNat 8 (len.toNat / 256 ^4 % 256),
       BitVec.ofNat 8 (len.toNat / 256 ^3 % 256), BitVec.ofNat 8 (len.toNat / 256 ^2 % 256),
       BitVec.ofNat 8 (len.toNat / 256 ^1 % 256), BitVec.ofNat 8 (len.toNat % 256)] := by
    rw [beShift_cons 7 len.toNat,
      beShift_cons 6 len.toNat,
      beShift_cons 5 len.toNat,
      beShift_cons 4 len.toNat,
      beShift_cons 3 len.toNat,
      beShift_cons 2 len.toNat,
      beShift_cons 1 len.toNat,
      beShift_cons 0 len.toNat]
    simp only [beShift, Nat.pow_one, Nat.pow_zero, Nat.div_one]
  have h7 := tshPrefix_byte_div_eq_shift len 7
  rw [show 8 * 7 = 56 from by norm_num] at h7
  have h6 := tshPrefix_byte_div_eq_shift len 6
  rw [show 8 * 6 = 48 from by norm_num] at h6
  have h5 := tshPrefix_byte_div_eq_shift len 5
  rw [show 8 * 5 = 40 from by norm_num] at h5
  have h4 := tshPrefix_byte_div_eq_shift len 4
  rw [show 8 * 4 = 32 from by norm_num] at h4
  have h3 := tshPrefix_byte_div_eq_shift len 3
  rw [show 8 * 3 = 24 from by norm_num] at h3
  have h2 := tshPrefix_byte_div_eq_shift len 2
  rw [show 8 * 2 = 16 from by norm_num] at h2
  have h1 := tshPrefix_byte_div_eq_shift len 1
  rw [show 8 * 1 = 8 from by norm_num] at h1
  have hlow : BitVec.ofNat 8 (len.toNat % 256) = BitVec.ofNat 8 len.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [tshPrefixApply, hpfx, hbe, tshPrefixSet,
    show BitVec.ofNat 8 (0xF7 + 8) = (0xff : BitVec 8) from by decide,
    h7, h6, h5, h4, h3, h2, h1, hlow]
  exact tshPrefix_append_eq_set9 outBytes _ _ _ _ _ _ _ _ _ hlen

theorem tsh_prefix_long8_in_fullCode
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 72057594037927936 ≤ len.toNat)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 8 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 90 PrefixB (raVal &&& ~~~1) fullCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
       (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))) := by
  have h := cpsTripleWithin_extend_code prefix_mono
    (RlpEncodeListPrefixLong8Spec.rlp_encode_list_prefix_long8_pinned_spec_within
      PrefixB len outPtr cellPtr raVal v5 v28 v29 v30 v31
      outBytes cellOld h_len_lo h_out_align h_out_len h_out_valid)
  have happly := tshPrefixApply_long8 outBytes len h_len_lo len.isLt h_out_len
  have hnh : BitVec.ofNat 64 (tshPrefixNH len.toNat) = (9 : Word) := by
    rw [tshPrefixNH_long8 len.toNat h_len_lo len.isLt]; rfl
  simpa [happly, hnh] using h

/-! ## Contiguous long-form cover `[56, 2^64)` at fuel `tshPrefixFuel` -/

/-- Long1…long8 composition: total on `56 ≤ len` (Word domain).
    Buffer obligation uses the strongest arm (`8 < |outBytes|`). -/
theorem tsh_prefix_long_any_in_fullCode
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 56 ≤ len.toNat)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 8 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin tshPrefixFuel PrefixB (raVal &&& ~~~1) fullCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
       (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))) := by
  have hlen1 : 1 < outBytes.length := by omega
  have hlen2 : 2 < outBytes.length := by omega
  have hlen3 : 3 < outBytes.length := by omega
  have hlen4 : 4 < outBytes.length := by omega
  have hlen5 : 5 < outBytes.length := by omega
  have hlen6 : 6 < outBytes.length := by omega
  have hlen7 : 7 < outBytes.length := by omega
  by_cases c1 : len.toNat < 256
  · exact cpsTripleWithin_mono_nSteps (by decide : 22 ≤ tshPrefixFuel)
      (tsh_prefix_long1_in_fullCode len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld h_len_lo c1 h_out_align hlen1 h_out_valid)
  by_cases c2 : len.toNat < 65536
  · exact cpsTripleWithin_mono_nSteps (by decide : 32 ≤ tshPrefixFuel)
      (tsh_prefix_long2_in_fullCode len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld (by omega) c2 h_out_align hlen2 h_out_valid)
  by_cases c3 : len.toNat < 16777216
  · exact cpsTripleWithin_mono_nSteps (by decide : 42 ≤ tshPrefixFuel)
      (tsh_prefix_long3_in_fullCode len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld (by omega) c3 h_out_align hlen3 h_out_valid)
  by_cases c4 : len.toNat < 4294967296
  · exact cpsTripleWithin_mono_nSteps (by decide : 52 ≤ tshPrefixFuel)
      (tsh_prefix_long4_in_fullCode len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld (by omega) c4 h_out_align hlen4 h_out_valid)
  by_cases c5 : len.toNat < 1099511627776
  · exact cpsTripleWithin_mono_nSteps (by decide : 62 ≤ tshPrefixFuel)
      (tsh_prefix_long5_in_fullCode len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld (by omega) c5 h_out_align hlen5 h_out_valid)
  by_cases c6 : len.toNat < 281474976710656
  · exact cpsTripleWithin_mono_nSteps (by decide : 72 ≤ tshPrefixFuel)
      (tsh_prefix_long6_in_fullCode len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld (by omega) c6 h_out_align hlen6 h_out_valid)
  by_cases c7 : len.toNat < 72057594037927936
  · exact cpsTripleWithin_mono_nSteps (by decide : 82 ≤ tshPrefixFuel)
      (tsh_prefix_long7_in_fullCode len outPtr cellPtr raVal v5 v28 v29 v30 v31
        outBytes cellOld (by omega) c7 h_out_align hlen7 h_out_valid)
  exact tsh_prefix_long8_in_fullCode len outPtr cellPtr raVal v5 v28 v29 v30 v31
    outBytes cellOld (by omega) h_out_align h_out_len h_out_valid

/-- Long-form `callWithin` at `tx_signing_hash+216` for `56 ≤ len` (full Word). -/
theorem tsh_prefix_long_any_callWithin
    (vOld len outPtr cellPtr v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_len_lo : 56 ≤ len.toNat)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 8 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    let ret := tshPrefixJalPC + 4
    cpsTripleWithin (1 + tshPrefixFuel) tshPrefixJalPC ret fullCode
      (((.x1 ↦ᵣ vOld) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
         ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** regOwn .x5 ** regOwn .x28 **
         regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
         (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat)) ** F))) := by
  intro ret
  have hret_eq : (ret &&& ~~~(1 : Word)) = ret := tshPrefixJal_ret_even
  have hcore := tsh_prefix_long_any_in_fullCode len outPtr cellPtr ret v5 v28 v29 v30 v31
    outBytes cellOld h_len_lo h_out_align h_out_len h_out_valid
  rw [hret_eq] at hcore
  have hcallee : cpsTripleWithin tshPrefixFuel PrefixB ret fullCode
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
         ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** regOwn .x5 ** regOwn .x28 **
         regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
         (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcore
  have hcalleeF := cpsTripleWithin_frameR F hF hcallee
  have hP : ((((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
      ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact hF
  exact callWithin_spec tshPrefixJalPC PrefixB vOld tshPrefixJalOff tshPrefixFuel
    tshPrefixJal_target tshPrefixJal_mem hP
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcalleeF)

/-- Short-form `callWithin` posting via `tshPrefixApply` / `tshPrefixNH`. -/
theorem tsh_prefix_short_apply_callWithin
    (vOld len outPtr cellPtr v5 v6 v7 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_len : len.toNat < 56)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 0 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    let ret := tshPrefixJalPC + 4
    cpsTripleWithin (1 + 8) tshPrefixJalPC ret fullCode
      (((.x1 ↦ᵣ vOld) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
         (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat)) ** F))) := by
  intro ret
  have hret_eq : (ret &&& ~~~(1 : Word)) = ret := tshPrefixJal_ret_even
  have hcore := tsh_prefix_short_apply_in_fullCode len outPtr cellPtr ret v5 v6 v7
    outBytes cellOld h_len h_out_align h_out_len h_out_valid
  rw [hret_eq] at hcore
  have hcallee : cpsTripleWithin 8 PrefixB ret fullCode
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
         (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat))))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcore
  have hcalleeF := cpsTripleWithin_frameR F hF hcallee
  have hP : ((((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact hF
  exact callWithin_spec tshPrefixJalPC PrefixB vOld tshPrefixJalOff 8
    tshPrefixJal_target tshPrefixJal_mem hP
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcalleeF)

/-- Open four preserved callee-saved-style temps in a post. -/
private theorem tsh_open_regs_28_31 (v28 v29 v30 v31 : Word) (P : Assertion) (h : _)
    (hq : ((.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** P) h) :
    (regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** P) h := by
  have s28 : ((.x28 ↦ᵣ v28) **
      ((.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** P)) h := by xperm_hyp hq
  have o28 := sepConj_mono_left (regIs_to_regOwn .x28 v28) h s28
  have s29 : ((.x29 ↦ᵣ v29) **
      (regOwn .x28 ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** P)) h := by xperm_hyp o28
  have o29 := sepConj_mono_left (regIs_to_regOwn .x29 v29) h s29
  have s30 : ((.x30 ↦ᵣ v30) **
      (regOwn .x29 ** regOwn .x28 ** (.x31 ↦ᵣ v31) ** P)) h := by xperm_hyp o29
  have o30 := sepConj_mono_left (regIs_to_regOwn .x30 v30) h s30
  have s31 : ((.x31 ↦ᵣ v31) **
      (regOwn .x30 ** regOwn .x29 ** regOwn .x28 ** P)) h := by xperm_hyp o30
  have o31 := sepConj_mono_left (regIs_to_regOwn .x31 v31) h s31
  xperm_hyp o31

private theorem tsh_open_regs_6_7 (v6 v7 : Word) (P : Assertion) (h : _)
    (hq : ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** P) h) :
    (regOwn .x6 ** regOwn .x7 ** P) h := by
  have s6 : ((.x6 ↦ᵣ v6) ** ((.x7 ↦ᵣ v7) ** P)) h := by xperm_hyp hq
  have o6 := sepConj_mono_left (regIs_to_regOwn .x6 v6) h s6
  have s7 : ((.x7 ↦ᵣ v7) ** (regOwn .x6 ** P)) h := by xperm_hyp o6
  have o7 := sepConj_mono_left (regIs_to_regOwn .x7 v7) h s7
  xperm_hyp o7

/-- Contiguous cover of every `len : Word` at fuel `1 + tshPrefixFuel`.

    Requires the full BSS slot (`8 < |outBytes|`) so every long form fits,
    including long8's 9-byte header. Clobbers the union of short (`x5–x7`) and
    long (`x5,x28–x31`) temps. -/
theorem tsh_prefix_any_callWithin
    (vOld len outPtr cellPtr v5 v6 v7 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 8 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    let ret := tshPrefixJalPC + 4
    cpsTripleWithin (1 + tshPrefixFuel) tshPrefixJalPC ret fullCode
      (((.x1 ↦ᵣ vOld) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
         ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
         (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat)) ** F))) := by
  intro ret
  by_cases hshort : len.toNat < 56
  · let Fshort : Assertion :=
      ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
        ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) ** F
    have hFshort : Fshort.pcFree := by
      unfold Fshort
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hF
    have hC := tsh_prefix_short_apply_callWithin vOld len outPtr cellPtr v5 v6 v7
      outBytes cellOld Fshort hFshort hshort h_out_align (by omega) h_out_valid
    refine cpsTripleWithin_mono_nSteps (by decide : 1 + 8 ≤ 1 + tshPrefixFuel) ?_
    exact cpsTripleWithin_weaken (fun _ hp => by
        simp only [Fshort] at hp ⊢
        xperm_hyp hp)
      (fun h hq => by
        simp only [Fshort, ret] at hq ⊢
        have hq' :
            ((.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
              ((.x1 ↦ᵣ ret) **
                ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ cellPtr) **
                 regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
                 (.x0 ↦ᵣ (0 : Word)) **
                 bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
                 (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat)) ** F))) h := by
          xperm_hyp hq
        have opened := tsh_open_regs_28_31 v28 v29 v30 v31 _ h hq'
        xperm_hyp opened) hC
  · let Flong : Assertion :=
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) ** F
    have hFlong : Flong.pcFree := by
      unfold Flong
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hF
    have hL := tsh_prefix_long_any_callWithin vOld len outPtr cellPtr v5 v28 v29 v30 v31
      outBytes cellOld Flong hFlong (by omega) h_out_align h_out_len h_out_valid
    exact cpsTripleWithin_weaken (fun _ hp => by
        simp only [Flong] at hp ⊢
        xperm_hyp hp)
      (fun h hq => by
        simp only [Flong, ret] at hq ⊢
        have hq' :
            ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
              ((.x1 ↦ᵣ ret) **
                ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ cellPtr) **
                 regOwn .x5 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
                 regOwn .x31 **
                 (.x0 ↦ᵣ (0 : Word)) **
                 bytesRegion outPtr (tshPrefixApply outBytes len.toNat) **
                 (cellPtr ↦ₘ BitVec.ofNat 64 (tshPrefixNH len.toNat)) ** F))) h := by
          xperm_hyp hq
        have opened := tsh_open_regs_6_7 v6 v7 _ h hq'
        xperm_hyp opened) hL

end EvmAsm.Codegen.TxSigningHashSpec
