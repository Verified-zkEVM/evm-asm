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

  Residual domain gate after composition: `len.toNat < 2^56`.

  ## Extra hypotheses beyond the length band (audit)

  Every per-form pinned triple also carries ABI hyps (not length-domain):
  - `h_out_align : outPtr.toNat % 8 = 0`
  - `h_out_len   : N < outBytes.length` with N = 0,1,…,7 for short…long7
  - `h_out_valid : ∀ k < outBytes.length, isValidByteAccess (outPtr+k)`

  Composed gate therefore includes the strongest buffer obligation:
  `8 ≤ outBytes.length` (covers long7's `7 < length`), plus align + valid.
  Registry long4+ notes already classify these as ABI, not input-domain; they
  still belong in the composed row's full restriction set.

  Pure header model: `MptSpliceSlotSpec.rlpListPrefix`.
-/

import EvmAsm.Codegen.Programs.TxSigningHashSpecCore
import EvmAsm.Codegen.Programs.MptSpliceSlotSpec
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
open EvmAsm.Rv64.Tactics

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

/-- Step budget covering every form through long7 (largest pinned fuel). -/
def tshPrefixFuel : Nat := 82

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

end EvmAsm.Codegen.TxSigningHashSpec
