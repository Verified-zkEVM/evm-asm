/-
  EvmAsm.Codegen.Programs.TxSigningHashSpecPrefix

  Composed `rlp_encode_list_prefix` callWithin for K145 (#12038), covering the
  contiguous union of the eight per-form pinned rows:

    short  [0, 56)
    long1  [56, 256)
    long2  [256, 2^16)
    long3  [2^16, 2^24)
    long4  [2^24, 2^32)
    long5  [2^32, 2^40)
    long6  [2^40, 2^48)
    long7  [2^48, 2^56)

  Residual **registry gate** after composition: `len.toNat < 2^56` only.
  ABI framing (`out%8=0`, `8 ≤ |outBytes|`, byte-validity) is discharged at the
  pinned TSH call site (`tshPrefixOut_aligned`, fixed BSS slot) — not in the gate.

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

/-- Fuel covering every arm through long7. -/
def tshPrefixFuel : Nat := 82

/-! ## Pure prefix write into an existing out buffer -/

/-- Header length written by `rlp_encode_list_prefix` for payload `len`. -/
def tshPrefixNH (len : Nat) : Nat := (rlpListPrefix len).length

/-- Set prefix bytes at indices `0 .. |pfx|-1` into `outBytes`. -/
def tshPrefixSet (outBytes : List (BitVec 8)) (pfx : List (BitVec 8)) : List (BitVec 8) :=
  (List.range pfx.length).foldl
    (fun acc i => acc.set i (pfx.getD i (0 : BitVec 8))) outBytes

/-- Apply the RLP list-prefix encoding of `len` into `outBytes`. -/
def tshPrefixApply (outBytes : List (BitVec 8)) (len : Nat) : List (BitVec 8) :=
  tshPrefixSet outBytes (rlpListPrefix len)

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

theorem tshPrefixApply_of_lt_56 (outBytes : List (BitVec 8)) (len : Nat)
    (h : len < 56) (_hlen : 0 < outBytes.length) :
    tshPrefixApply outBytes len =
      outBytes.set 0 (BitVec.ofNat 8 (0xC0 + len)) := by
  have hle : len ≤ 55 := Nat.lt_succ_iff.mp h
  simp only [tshPrefixApply, tshPrefixSet, rlpListPrefix, if_pos hle,
    List.length_cons, List.length_nil, show List.range 1 = [0] from by decide,
    List.foldl, List.getD_cons_zero]

theorem tshPrefixApply_long1 (outBytes : List (BitVec 8)) (len : Nat)
    (hlo : 56 ≤ len) (hhi : len < 256) (_hlen : 1 < outBytes.length) :
    tshPrefixApply outBytes len =
      (outBytes.set 0 (0xF8 : BitVec 8)).set 1 (BitVec.ofNat 8 len) := by
  rw [tshPrefixApply, rlpListPrefix_long1 len hlo hhi]
  simp only [tshPrefixSet, List.length_cons, List.length_nil,
    show List.range 2 = [0, 1] from by decide, List.foldl,
    List.getD_cons_zero, List.getD_cons_succ]

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
    (hlo : 256 ≤ len.toNat) (hhi : len.toNat < 65536) (_hlen : 2 < outBytes.length) :
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
  rw [tshPrefixApply, hpfx, hbe]
  simp only [tshPrefixSet, List.length_cons, List.length_nil,
    show List.range 3 = [0, 1, 2] from by decide, List.foldl,
    List.getD_cons_zero, List.getD_cons_succ,
    show BitVec.ofNat 8 (0xF7 + 2) = (0xf9 : BitVec 8) from by decide]
  have h1 := tshPrefix_byte_div_eq_shift len 1
  rw [show 8 * 1 = 8 from by norm_num] at h1
  have hlow : BitVec.ofNat 8 (len.toNat % 256) = BitVec.ofNat 8 len.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  simp only [h1, hlow]

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
    (hlo : 65536 ≤ len.toNat) (hhi : len.toNat < 16777216) (_hlen : 3 < outBytes.length) :
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
  rw [tshPrefixApply, hpfx, hbe]
  simp only [tshPrefixSet, List.length_cons, List.length_nil,
    show List.range 4 = [0, 1, 2, 3] from by decide, List.foldl,
    List.getD_cons_zero, List.getD_cons_succ,
    show BitVec.ofNat 8 (0xF7 + 3) = (0xfa : BitVec 8) from by decide]
  have h2 := tshPrefix_byte_div_eq_shift len 2
  rw [show 8 * 2 = 16 from by norm_num] at h2
  have h1 := tshPrefix_byte_div_eq_shift len 1
  rw [show 8 * 1 = 8 from by norm_num] at h1
  have hlow : BitVec.ofNat 8 (len.toNat % 256) = BitVec.ofNat 8 len.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  simp only [h2, h1, hlow]

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
    (hlo : 16777216 ≤ len.toNat) (hhi : len.toNat < 4294967296) (_hlen : 4 < outBytes.length) :
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
  rw [tshPrefixApply, hpfx, hbe]
  simp only [tshPrefixSet, List.length_cons, List.length_nil,
    show List.range 5 = [0, 1, 2, 3, 4] from by decide, List.foldl,
    List.getD_cons_zero, List.getD_cons_succ,
    show BitVec.ofNat 8 (0xF7 + 4) = (0xfb : BitVec 8) from by decide]
  have h3 := tshPrefix_byte_div_eq_shift len 3
  rw [show 8 * 3 = 24 from by norm_num] at h3
  have h2 := tshPrefix_byte_div_eq_shift len 2
  rw [show 8 * 2 = 16 from by norm_num] at h2
  have h1 := tshPrefix_byte_div_eq_shift len 1
  rw [show 8 * 1 = 8 from by norm_num] at h1
  have hlow : BitVec.ofNat 8 (len.toNat % 256) = BitVec.ofNat 8 len.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  simp only [h3, h2, h1, hlow]

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
    (hlo : 4294967296 ≤ len.toNat) (hhi : len.toNat < 1099511627776) (_hlen : 5 < outBytes.length) :
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
  rw [tshPrefixApply, hpfx, hbe]
  simp only [tshPrefixSet, List.length_cons, List.length_nil,
    show List.range 6 = [0, 1, 2, 3, 4, 5] from by decide, List.foldl,
    List.getD_cons_zero, List.getD_cons_succ,
    show BitVec.ofNat 8 (0xF7 + 5) = (0xfc : BitVec 8) from by decide]
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
  simp only [h4, h3, h2, h1, hlow]

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
    (hlo : 1099511627776 ≤ len.toNat) (hhi : len.toNat < 281474976710656) (_hlen : 6 < outBytes.length) :
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
  rw [tshPrefixApply, hpfx, hbe]
  simp only [tshPrefixSet, List.length_cons, List.length_nil,
    show List.range 7 = [0, 1, 2, 3, 4, 5, 6] from by decide, List.foldl,
    List.getD_cons_zero, List.getD_cons_succ,
    show BitVec.ofNat 8 (0xF7 + 6) = (0xfd : BitVec 8) from by decide]
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
  simp only [h5, h4, h3, h2, h1, hlow]

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
    (hlo : 281474976710656 ≤ len.toNat) (hhi : len.toNat < 72057594037927936) (_hlen : 7 < outBytes.length) :
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
  rw [tshPrefixApply, hpfx, hbe]
  simp only [tshPrefixSet, List.length_cons, List.length_nil,
    show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from by decide, List.foldl,
    List.getD_cons_zero, List.getD_cons_succ,
    show BitVec.ofNat 8 (0xF7 + 7) = (0xfe : BitVec 8) from by decide]
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
  simp only [h6, h5, h4, h3, h2, h1, hlow]

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

/-! ## Contiguous long-form cover `[56, 2^56)` at fuel `tshPrefixFuel` -/

/-- Long1…long7 composition: residual length gate `56 ≤ len < 2^56`.
    Buffer obligation uses the strongest arm (`7 < |outBytes|`). -/
theorem tsh_prefix_long_any_in_fullCode
    (len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 56 ≤ len.toNat)
    (h_len_hi : len.toNat < 72057594037927936)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 7 < outBytes.length)
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
  exact tsh_prefix_long7_in_fullCode len outPtr cellPtr raVal v5 v28 v29 v30 v31
    outBytes cellOld (by omega) h_len_hi h_out_align h_out_len h_out_valid

/-- Long-form `callWithin` at `tx_signing_hash+216` for `56 ≤ len < 2^56`. -/
theorem tsh_prefix_long_any_callWithin
    (vOld len outPtr cellPtr v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_len_lo : 56 ≤ len.toNat)
    (h_len_hi : len.toNat < 72057594037927936)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 7 < outBytes.length)
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
    outBytes cellOld h_len_lo h_len_hi h_out_align h_out_len h_out_valid
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

end EvmAsm.Codegen.TxSigningHashSpec
