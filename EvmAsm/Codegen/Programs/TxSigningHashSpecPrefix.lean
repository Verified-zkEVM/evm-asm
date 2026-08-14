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

end EvmAsm.Codegen.TxSigningHashSpec
