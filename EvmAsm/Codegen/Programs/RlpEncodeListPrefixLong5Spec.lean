/-
  EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong5Spec

  **`rlp_encode_list_prefix`, 5-length-byte long form** (GH #10780 item 3, width 5).

  `RlpSpliceHelperSpec.lean` proves the short form (`len < 56`) and the 1-length-byte
  long form; `RlpEncodeListPrefixLong2Spec.lean` proves `256 ≤ len < 65536`;
  `RlpEncodeListPrefixLong3Spec.lean` proves `65536 ≤ len < 16777216`;
  `RlpEncodeListPrefixLong4Spec.lean` proves `16777216 ≤ len < 4294967296`. This module
  adds `4294967296 ≤ len < 1099511627776`: header byte `0xFC` followed by the
  5 big-endian length bytes, header length 6.

  ## What is different from the long4 arm — exactly two things

  1. **The lenlen ladder falls one branch further.** In long4 the
     `BLTU x10, 4294967296` at idx19 (`base+76`) is *taken* and
     jumps straight to the shared header writer at idx30 (`base+120`). Here it is **not**
     taken, so control falls into idx20–idx22
     (`base+80`, `base+84`, `base+88`),
     where `x28 := 5` and `x29 := 4294967296 <<< 8` before
     `BLTU x10, 1099511627776` (idx22, offset `+32`) jumps to
     `base+120`. That is three extra dispatch steps over long4 — 17 ladder
     steps rather than 14 — and it is the only genuinely per-width part of the
     arm: the routine computes `x28` by falling through `k` branches, so the ladder is
     inherently eight cases.
  2. **The loop is cited at `m := 5`.** `RlpEncodeListPrefixLoopSpec.lpLolLoop` covers
     idx35–idx41 whole, at a symbolic trip count `m`, in `7 * m + 1` steps with
     postcondition `writeShift dst di len.toNat m`. Long4 instantiates it at
     `m := 4`; this arm instantiates it at `m := 5`, `di := 1`, so the loop
     contributes **36 steps** instead of 29. Nothing about the loop
     is re-proved, and nothing about it is unrolled.

  Everything else is long4 byte for byte: the header writer idx30–34, the epilogue
  idx42–44, the closing `JALR`, the frame/clobber set, and the shape of the
  postcondition.

  ## Step count 62, derived from the program

  `17` to reach idx30 (idx 0, 1, 8–22)
  `+ 5` for idx30–34 `+ 36` for the loop (`7*5+1`) `+ 3` for idx42–44 `+ 1`
  for the `JALR` `= 62`. Long4's 52 is the same accounting with 14 ladder steps and
  a 29-step loop.

  ## Byte order, read off the loop rather than assumed

  `x29` starts at `lenlen - 1 = 4` and counts **down**, while `x30` starts at
  `outPtr + 1` and counts **up**. So the iterations store `len >>> 32`, …,
  `len` at `out[1]` … `out[5]` — big-endian, most significant first, matching RLP. As in
  long2/long3/long4 the postcondition pins **each index to its own shift**, because a
  statement symmetric in the two cursors would not detect them being swapped.

  ## Canonical form

  The first length byte is nonzero, which is what makes the emitted header canonical RLP
  (#10780 item 1: a length-of-length carrying a leading zero still *parses* and hashes
  differently). It is not re-derived here:
  `RlpEncodeListPrefixCanonical.first_length_byte_ne_zero` proves it at every width from
  `u64ByteLen`'s own bounds, and `long5_first_length_byte_ne_zero` below is its
  `lenlen = 5` instance.

  ## The overflow side condition, checked rather than assumed

  `lpLolLoop` requires `outPtr.toNat + (di + m) ≤ 2 ^ 64`, which at `di := 1, m := 5` is
  `outPtr.toNat + 6 ≤ 2 ^ 64`. The alignment hypothesis `outPtr.toNat % 8 = 0`
  supplies eight bytes of slack, so `omega` closes it from alignment alone — the same
  one-line step long4 uses for `+ 5`, with no extra hypothesis. ⚠️ That headroom does
  **not** extend past this width family: at `lenlen = 8` the requirement is `+ 9`, more
  than alignment supplies, and that arm will need an explicit bound. This arm does not.

  ## Scope

  Proof only; no emitted bytes change. No elaboration budget is widened anywhere in this
  module, and `maxRecDepth` is left at its default.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Evm64.CallingConvention
import EvmAsm.EL.RLP.Properties
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLoopSpec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixCanonical

namespace EvmAsm.Codegen

namespace RlpEncodeListPrefixLong5Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpEncodeBytesSAsm (writeShift truncate_shift_eq)
open EvmAsm.Codegen.RlpEncodeListPrefixLoopSpec (lpLolLoop)
open EvmAsm.Codegen.RlpListEncodedSizeSAsm (u64ByteLen)

/-- Code-membership for a `∀ base` `ofProg` slice: instruction `k` of the program,
    addressed as a concrete `base + OFF` term. Mirrors the file-local macro of the same
    name in the long1/long2/long3/long4/loop modules (each is `local`, so not
    importable). -/
local macro "cmem" k:term:max : tactic =>
  `(tactic| exact CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr _ _ $k _ (by decide) (by decide) (by bv_omega)))

/-! ## Arithmetic helpers

    Re-declared from `RlpSpliceHelperSpec.lean`/`RlpEncodeListPrefixLong4Spec.lean`,
    where they are `private`. -/

private theorem ult_of_toNat_lt {a c : Word} (h : a.toNat < c.toNat) :
    BitVec.ult a c := by
  simpa [BitVec.ult, decide_eq_true_eq] using h

private theorem not_ult_of_toNat_ge {a c : Word} (h : c.toNat ≤ a.toNat) :
    ¬ BitVec.ult a c := by
  simp only [BitVec.ult, decide_eq_true_eq]
  omega

private theorem trunc8_eq_ofNat_toNat (len : Word) :
    len.truncate 8 = BitVec.ofNat 8 len.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-! ## The loop's output, in the long4 postcondition's shape

    `lpLolLoop` hands back `writeShift outBytes 1 len.toNat 5`. The theorem below states
    the region as 5 nested `List.set`s instead, exactly as long4 does with four, so the
    arms' postconditions read the same way and each byte is pinned to its own shift. -/

/-- The `i`-th stored byte, moving from `writeShift`'s division form to the shift form
    the postcondition names. `truncate_shift_eq` already has the hard direction. -/
private theorem byte_div_eq_shift (v : Word) (i : Nat) :
    BitVec.ofNat 8 (v.toNat / 256 ^ i % 256) = BitVec.ofNat 8 (v >>> (8 * i)).toNat :=
  (truncate_shift_eq v i).symm.trans (trunc8_eq_ofNat_toNat (v >>> (8 * i)))

private theorem shift_zero_id (v : Word) : v >>> (0 : Nat) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  simp


/-- ⭐ **5 length bytes at index 1, spelled as `List.set`s.** Each index is
    tied to its own shift: `out[1]` to `len >>> 32`, … `out[5]` to `len`.
    Unfolding `writeShift` at the literal width is definitional; the only content is
    rewriting `len.toNat / 256 ^ i % 256` into `(len >>> 8i).toNat`. -/
private theorem writeShift_five (dst : List Byte) (len : Word) :
    writeShift dst 1 len.toNat 5
      =
        (((((dst.set 1 (BitVec.ofNat 8 (len >>> (32 : Nat)).toNat)).set 2
            (BitVec.ofNat 8 (len >>> (24 : Nat)).toNat)).set 3
            (BitVec.ofNat 8 (len >>> (16 : Nat)).toNat)).set 4
            (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 5
            (BitVec.ofNat 8 len.toNat)) := by
  have hstep : writeShift dst 1 len.toNat 5
      =
        (((((dst.set 1 (BitVec.ofNat 8 (len.toNat / 256 ^ 4 % 256))).set 2
            (BitVec.ofNat 8 (len.toNat / 256 ^ 3 % 256))).set 3
            (BitVec.ofNat 8 (len.toNat / 256 ^ 2 % 256))).set 4
            (BitVec.ofNat 8 (len.toNat / 256 ^ 1 % 256))).set 5
            (BitVec.ofNat 8 (len.toNat / 256 ^ 0 % 256))) := rfl
  have h4 := byte_div_eq_shift len 4
  have h3 := byte_div_eq_shift len 3
  have h2 := byte_div_eq_shift len 2
  have h1 := byte_div_eq_shift len 1
  have h0 := byte_div_eq_shift len 0
  rw [show 8 * 4 = 32 from by norm_num] at h4
  rw [show 8 * 3 = 24 from by norm_num] at h3
  rw [show 8 * 2 = 16 from by norm_num] at h2
  rw [show 8 * 1 = 8 from by norm_num] at h1
  rw [show 8 * 0 = 0 from by norm_num, shift_zero_id len] at h0
  rw [hstep, h4, h3, h2, h1, h0]

/-! ## Canonical form: the length-of-length carries no leading zero -/

/-- **The first length byte is nonzero**, at this arm's width.

    Not re-proved: `RlpEncodeListPrefixCanonical.first_length_byte_ne_zero` establishes
    it for every `lenlen ∈ 1..8` from the two bounds `u64ByteLen`'s own definition
    contains, and this is its `lenlen = 5` instance — the same relationship
    `long4_first_length_byte_ne_zero` has to the long4 arm. Combined with the triple
    below, `out[1] ≠ 0`, which is what makes the emitted header canonical RLP rather
    than a header that merely parses (#10780 item 1). -/
theorem long5_first_length_byte_ne_zero {len : Word}
    (h_lo : 4294967296 ≤ len.toNat) (h_hi : len.toNat < 1099511627776) :
    BitVec.ofNat 8 (len >>> (32 : Nat)).toNat ≠ 0 := by
  have hwidth : u64ByteLen len = 5 := by
    unfold u64ByteLen
    split_ifs <;> omega
  have h := RlpEncodeListPrefixCanonical.first_length_byte_ne_zero (len := len) (by omega)
  rwa [hwidth, show 8 * (5 - 1) = 32 from by norm_num] at h

/-! ## The triple -/

/-- **`rlp_encode_list_prefix`, 5-length-byte long form** (`4294967296 ≤ len <
    1099511627776`): writes the header bytes `[0xFC, len >>> 32, len >>> 24, len >>> 16, len
    >>> 8, len]` and header length 6, returns `a0 = 0`; scratch registers pinned.

    Clobbers `t0`/`t3`–`t6` (`x5`, `x28`–`x31`) as the long1–long4 arms do; `x6`/`x7`
    are untouched on this path and so do not appear.

    The 5 length bytes are pinned to their own shifts because the loop counts `x29`
    down while counting `x30` up, and a symmetric statement would not detect the cursors
    being swapped. Together with `long5_first_length_byte_ne_zero`, `out[1]` is
    additionally known to be nonzero, so the emitted header is canonical RLP.

    ⭐ The loop (idx35–idx41) is discharged by one application of `lpLolLoop` at
    `m := 5`, `di := 1` — 36 of the 62 steps — rather than unrolled per
    iteration. -/
theorem rlp_encode_list_prefix_long5_pinned_spec_within
    (base len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 4294967296 ≤ len.toNat)
    (h_len_hi : len.toNat < 1099511627776)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 5 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 62 base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpEncodeListPrefix_prog)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x28 ** regOwn .x29 **
       regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr
         ((((((outBytes.set 0 (0xFC : BitVec 8)).set 1
             (BitVec.ofNat 8 (len >>> (32 : Nat)).toNat)).set 2
             (BitVec.ofNat 8 (len >>> (24 : Nat)).toNat)).set 3
             (BitVec.ofNat 8 (len >>> (16 : Nat)).toNat)).set 4
             (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 5
             (BitVec.ofNat 8 len.toNat)) **
       (cellPtr ↦ₘ (6 : Word))) := by
  set CR := CodeReq.ofProg base rlpEncodeListPrefix_prog with hCR
  have h_out_len0 : 0 < outBytes.length := by omega
  -- idx0 (base+0): LI x5, 56
  have hli5 := liftCode (cr' := CR)
    (li_spec_gen_within .x5 v5 (56 : Word) base (by decide))
    (by rw [hCR]; cmem 0)
  -- idx1 (base+4): BGEU x10, x5, +28 — TAKEN (len ≥ 56) → base+32
  have hbr1 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 1)
    (h := bgeu_spec_gen_within .x10 .x5 (28 : BitVec 13) len (56 : Word) (base + 4))
  rw [show (base + 4 : Word) + signExtend13 (28 : BitVec 13) = base + 32 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega,
      show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbr1
  have hnult56 : ¬ BitVec.ult len (56 : Word) :=
    not_ult_of_toNat_ge (by rw [show ((56 : Word)).toNat = 56 from by decide]; omega)
  have ht1 := cpsBranchWithin_takenStripPure2 hbr1 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact hnult56 ((sepConj_pure_right _).1 hQ).2)
  -- idx8 (base+32): LI x28, 1
  have hli28_1 := liftCode (cr' := CR)
    (li_spec_gen_within .x28 v28 (1 : Word) (base + 32) (by decide))
    (by rw [hCR]; cmem 8)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at hli28_1
  -- idx9 (base+36): LI x29, 256
  have hli29 := liftCode (cr' := CR)
    (li_spec_gen_within .x29 v29 (256 : Word) (base + 36) (by decide))
    (by rw [hCR]; cmem 9)
  rw [show (base + 36 : Word) + 4 = base + 40 from by bv_omega] at hli29
  -- idx10 (base+40): BLTU x10, x29, +80 — NOT taken (len ≥ 256) → base+44
  have hbr10 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 10)
    (h := bltu_spec_gen_within .x10 .x29 (80 : BitVec 13) len (256 : Word)
      (base + 40))
  rw [show (base + 40 : Word) + signExtend13 (80 : BitVec 13) = base + 120 from by
        rw [show signExtend13 (80 : BitVec 13) = (80 : Word) from by decide]
        bv_omega,
      show (base + 40 : Word) + 4 = base + 44 from by bv_omega] at hbr10
  have hnult10 : ¬ BitVec.ult len (256 : Word) :=
    not_ult_of_toNat_ge
      (by rw [show ((256 : Word)).toNat = 256 from by decide]; omega)
  have hnt10 := cpsBranchWithin_ntakenStripPure2 hbr10 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hnult10 ((sepConj_pure_right _).1 hQ).2)
  -- idx11 (base+44): LI x28, 2
  have hli28_2 := liftCode (cr' := CR)
    (li_spec_gen_within .x28 (1 : Word) (2 : Word) (base + 44) (by decide))
    (by rw [hCR]; cmem 11)
  rw [show (base + 44 : Word) + 4 = base + 48 from by bv_omega] at hli28_2
  -- idx12 (base+48): SLLI x29, x29, 8 — x29 := 65536
  have hsll_2 := liftCode (cr' := CR)
    (slli_spec_gen_same_within .x29 (256 : Word) (8 : BitVec 6) (base + 48)
      (by decide))
    (by rw [hCR]; cmem 12)
  rw [show (base + 48 : Word) + 4 = base + 52 from by bv_omega,
      show ((256 : Word) <<< ((8 : BitVec 6)).toNat) =
        (65536 : Word) from by decide] at hsll_2
  -- idx13 (base+52): BLTU x10, x29, +68 — NOT taken (len ≥ 65536) → base+56
  have hbr13 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 13)
    (h := bltu_spec_gen_within .x10 .x29 (68 : BitVec 13) len (65536 : Word)
      (base + 52))
  rw [show (base + 52 : Word) + signExtend13 (68 : BitVec 13) = base + 120 from by
        rw [show signExtend13 (68 : BitVec 13) = (68 : Word) from by decide]
        bv_omega,
      show (base + 52 : Word) + 4 = base + 56 from by bv_omega] at hbr13
  have hnult13 : ¬ BitVec.ult len (65536 : Word) :=
    not_ult_of_toNat_ge
      (by rw [show ((65536 : Word)).toNat = 65536 from by decide]; omega)
  have hnt13 := cpsBranchWithin_ntakenStripPure2 hbr13 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hnult13 ((sepConj_pure_right _).1 hQ).2)
  -- idx14 (base+56): LI x28, 3
  have hli28_3 := liftCode (cr' := CR)
    (li_spec_gen_within .x28 (2 : Word) (3 : Word) (base + 56) (by decide))
    (by rw [hCR]; cmem 14)
  rw [show (base + 56 : Word) + 4 = base + 60 from by bv_omega] at hli28_3
  -- idx15 (base+60): SLLI x29, x29, 8 — x29 := 16777216
  have hsll_3 := liftCode (cr' := CR)
    (slli_spec_gen_same_within .x29 (65536 : Word) (8 : BitVec 6) (base + 60)
      (by decide))
    (by rw [hCR]; cmem 15)
  rw [show (base + 60 : Word) + 4 = base + 64 from by bv_omega,
      show ((65536 : Word) <<< ((8 : BitVec 6)).toNat) =
        (16777216 : Word) from by decide] at hsll_3
  -- idx16 (base+64): BLTU x10, x29, +56 — NOT taken (len ≥ 16777216) → base+68
  have hbr16 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 16)
    (h := bltu_spec_gen_within .x10 .x29 (56 : BitVec 13) len (16777216 : Word)
      (base + 64))
  rw [show (base + 64 : Word) + signExtend13 (56 : BitVec 13) = base + 120 from by
        rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]
        bv_omega,
      show (base + 64 : Word) + 4 = base + 68 from by bv_omega] at hbr16
  have hnult16 : ¬ BitVec.ult len (16777216 : Word) :=
    not_ult_of_toNat_ge
      (by rw [show ((16777216 : Word)).toNat = 16777216 from by decide]; omega)
  have hnt16 := cpsBranchWithin_ntakenStripPure2 hbr16 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hnult16 ((sepConj_pure_right _).1 hQ).2)
  -- idx17 (base+68): LI x28, 4
  have hli28_4 := liftCode (cr' := CR)
    (li_spec_gen_within .x28 (3 : Word) (4 : Word) (base + 68) (by decide))
    (by rw [hCR]; cmem 17)
  rw [show (base + 68 : Word) + 4 = base + 72 from by bv_omega] at hli28_4
  -- idx18 (base+72): SLLI x29, x29, 8 — x29 := 4294967296
  have hsll_4 := liftCode (cr' := CR)
    (slli_spec_gen_same_within .x29 (16777216 : Word) (8 : BitVec 6) (base + 72)
      (by decide))
    (by rw [hCR]; cmem 18)
  rw [show (base + 72 : Word) + 4 = base + 76 from by bv_omega,
      show ((16777216 : Word) <<< ((8 : BitVec 6)).toNat) =
        (4294967296 : Word) from by decide] at hsll_4
  -- idx19 (base+76): BLTU x10, x29, +44 — NOT taken (len ≥ 4294967296) → base+80
  have hbr19 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 19)
    (h := bltu_spec_gen_within .x10 .x29 (44 : BitVec 13) len (4294967296 : Word)
      (base + 76))
  rw [show (base + 76 : Word) + signExtend13 (44 : BitVec 13) = base + 120 from by
        rw [show signExtend13 (44 : BitVec 13) = (44 : Word) from by decide]
        bv_omega,
      show (base + 76 : Word) + 4 = base + 80 from by bv_omega] at hbr19
  have hnult19 : ¬ BitVec.ult len (4294967296 : Word) :=
    not_ult_of_toNat_ge
      (by rw [show ((4294967296 : Word)).toNat = 4294967296 from by decide]; omega)
  have hnt19 := cpsBranchWithin_ntakenStripPure2 hbr19 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hnult19 ((sepConj_pure_right _).1 hQ).2)
  -- idx20 (base+80): LI x28, 5
  have hli28_5 := liftCode (cr' := CR)
    (li_spec_gen_within .x28 (4 : Word) (5 : Word) (base + 80) (by decide))
    (by rw [hCR]; cmem 20)
  rw [show (base + 80 : Word) + 4 = base + 84 from by bv_omega] at hli28_5
  -- idx21 (base+84): SLLI x29, x29, 8 — x29 := 1099511627776
  have hsll_5 := liftCode (cr' := CR)
    (slli_spec_gen_same_within .x29 (4294967296 : Word) (8 : BitVec 6) (base + 84)
      (by decide))
    (by rw [hCR]; cmem 21)
  rw [show (base + 84 : Word) + 4 = base + 88 from by bv_omega,
      show ((4294967296 : Word) <<< ((8 : BitVec 6)).toNat) =
        (1099511627776 : Word) from by decide] at hsll_5
  -- idx22 (base+88): BLTU x10, x29, +32 — TAKEN (len < 1099511627776) → base+120
  have hbr22 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 22)
    (h := bltu_spec_gen_within .x10 .x29 (32 : BitVec 13) len (1099511627776 : Word)
      (base + 88))
  rw [show (base + 88 : Word) + signExtend13 (32 : BitVec 13) = base + 120 from by
        rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]
        bv_omega,
      show (base + 88 : Word) + 4 = base + 92 from by bv_omega] at hbr22
  have hult22 : BitVec.ult len (1099511627776 : Word) :=
    ult_of_toNat_lt
      (by rw [show ((1099511627776 : Word)).toNat = 1099511627776 from by decide]; omega)
  have ht22 := cpsBranchWithin_takenStripPure2 hbr22 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ((sepConj_pure_right _).1 hQ).2 hult22)
  -- idx30 (base+120): ADDI x29, x28, 247 — x29 := 0xFC
  have ha30 := liftCode (cr' := CR)
    (addi_spec_gen_within .x29 .x28 (1099511627776 : Word) (5 : Word)
      (247 : BitVec 12) (base + 120) (by decide))
    (by rw [hCR]; cmem 30)
  rw [show (base + 120 : Word) + 4 = base + 124 from by bv_omega,
      show (5 : Word) + signExtend12 (247 : BitVec 12) = (252 : Word) from by
        decide] at ha30
  -- idx31 (base+124): SB x11, x29 — out[0] := 0xFC
  have hsb31 := liftCode (cr' := CR)
    (bytesRegion_sb_within .x11 .x29 outPtr (252 : Word) (base + 124) outBytes 0
      h_out_align h_out_len0 (by have := outPtr.isLt; omega) (h_out_valid 0 h_out_len0))
    (by rw [hCR]; cmem 31)
  rw [show outPtr + BitVec.ofNat 64 0 = outPtr from by bv_omega,
      show ((252 : Word)).truncate 8 = (0xFC : BitVec 8) from by decide,
      show (base + 124 : Word) + 4 = base + 128 from by bv_omega] at hsb31
  -- idx32 (base+128): MV x30, x11
  have hmv := liftCode (cr' := CR)
    (mv_spec_gen_within .x30 .x11 outPtr v30 (base + 128) (by decide))
    (by rw [hCR]; cmem 32)
  rw [show (base + 128 : Word) + 4 = base + 132 from by bv_omega] at hmv
  -- idx33 (base+132): ADDI x30, x30, 1 — x30 := outPtr + 1
  have ha33 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x30 outPtr (1 : BitVec 12) (base + 132) (by decide))
    (by rw [hCR]; cmem 33)
  rw [show (base + 132 : Word) + 4 = base + 136 from by bv_omega,
      show outPtr + signExtend12 (1 : BitVec 12) = outPtr + BitVec.ofNat 64 1 from by
        rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]] at ha33
  -- idx34 (base+136): ADDI x29, x28, -1 — x29 := 4 = lenlen - 1
  have ha34 := liftCode (cr' := CR)
    (addi_spec_gen_within .x29 .x28 (252 : Word) (5 : Word)
      (-1 : BitVec 12) (base + 136) (by decide))
    (by rw [hCR]; cmem 34)
  rw [show (base + 136 : Word) + 4 = base + 140 from by bv_omega,
      show (5 : Word) + signExtend12 (-1 : BitVec 12) = (4 : Word) from by
        decide] at ha34
  -- ══ idx35–41 (base+140 → base+168): the length-byte loop, cited whole at m := 5 ══
  have hloop := lpLolLoop base outPtr v31 (56 : Word) len
    (outBytes.set 0 (0xFC : BitVec 8)) 1 5 (by omega) h_out_align
    (by rw [List.length_set]; omega)
    (by have := outPtr.isLt; omega)
    (fun k hk => h_out_valid (1 + k) (by omega))
  rw [show 7 * 5 + 1 = 36 from by norm_num,
      show BitVec.ofNat 64 5 - 1 = (4 : Word) from by decide,
      show (1 : Nat) + 5 = 6 from by norm_num,
      writeShift_five (outBytes.set 0 (0xFC : BitVec 8)) len] at hloop
  -- idx42 (base+168): ADDI x30, x28, 1 — x30 := 6 (header length)
  have ha42 := liftCode (cr' := CR)
    (addi_spec_gen_within .x30 .x28 (outPtr + BitVec.ofNat 64 6) (5 : Word)
      (1 : BitVec 12) (base + 168) (by decide))
    (by rw [hCR]; cmem 42)
  rw [show (base + 168 : Word) + 4 = base + 172 from by bv_omega,
      show (5 : Word) + signExtend12 (1 : BitVec 12) = (6 : Word) from by
        decide] at ha42
  -- idx43 (base+172): SD x12, x30 — *cell := 6
  have hsd := liftCode (cr' := CR)
    (sd_spec_within .x12 .x30 cellPtr (6 : Word) cellOld (0 : BitVec 12)
      (base + 172))
    (by rw [hCR]; cmem 43)
  simp only [signExtend12_0] at hsd
  rw [show cellPtr + (0 : Word) = cellPtr from by bv_omega,
      show (base + 172 : Word) + 4 = base + 176 from by bv_omega] at hsd
  -- idx44 (base+176): LI x10, 0
  have hli10 := liftCode (cr' := CR)
    (li_spec_gen_within .x10 len (0 : Word) (base + 176) (by decide))
    (by rw [hCR]; cmem 44)
  rw [show (base + 176 : Word) + 4 = base + 180 from by bv_omega] at hli10
  -- idx45 (base+180): ret
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (base + 180) raVal)
    (by rw [hCR]; cmem 45)
  -- ══ frames ══
  have hli5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hli5
  have ht1F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) ht1
  have hli28_1F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hli28_1
  have hli29F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hli29
  have hnt10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hnt10
  have hli28_2F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x29 : Reg) ↦ᵣ (256 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hli28_2
  have hsll_2F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsll_2
  have hnt13F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hnt13
  have hli28_3F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x29 : Reg) ↦ᵣ (65536 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hli28_3
  have hsll_3F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (3 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsll_3
  have hnt16F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (3 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hnt16
  have hli28_4F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x29 : Reg) ↦ᵣ (16777216 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hli28_4
  have hsll_4F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (4 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsll_4
  have hnt19F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (4 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hnt19
  have hli28_5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x29 : Reg) ↦ᵣ (4294967296 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hli28_5
  have hsll_5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (5 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsll_5
  have ht22F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (5 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) ht22
  have ha30F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha30
  have hsb31F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (5 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsb31
  have hmvF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (5 : Word)) **
     ((.x29 : Reg) ↦ᵣ (252 : Word)) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (0xFC : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hmv
  have ha33F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (5 : Word)) **
     ((.x29 : Reg) ↦ᵣ (252 : Word)) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (0xFC : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha33
  have ha34F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (0xFC : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha34
  have hloopF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x28 : Reg) ↦ᵣ (5 : Word)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hloop
  have ha42F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     regOwn .x5 ** ((.x29 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x31 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((((((outBytes.set 0 (0xFC : BitVec 8)).set 1
           (BitVec.ofNat 8 (len >>> (32 : Nat)).toNat)).set 2
           (BitVec.ofNat 8 (len >>> (24 : Nat)).toNat)).set 3
           (BitVec.ofNat 8 (len >>> (16 : Nat)).toNat)).set 4
           (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 5
           (BitVec.ofNat 8 len.toNat)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha42
  have hsdF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) **
     regOwn .x5 ** ((.x28 : Reg) ↦ᵣ (5 : Word)) **
     ((.x29 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x31 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((((((outBytes.set 0 (0xFC : BitVec 8)).set 1
           (BitVec.ofNat 8 (len >>> (32 : Nat)).toNat)).set 2
           (BitVec.ofNat 8 (len >>> (24 : Nat)).toNat)).set 3
           (BitVec.ofNat 8 (len >>> (16 : Nat)).toNat)).set 4
           (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 5
           (BitVec.ofNat 8 len.toNat)))
    (by pcf) hsd
  have hli10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     regOwn .x5 ** ((.x28 : Reg) ↦ᵣ (5 : Word)) **
     ((.x29 : Reg) ↦ᵣ (-1 : Word)) ** ((.x30 : Reg) ↦ᵣ (6 : Word)) **
     regOwn .x31 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((((((outBytes.set 0 (0xFC : BitVec 8)).set 1
           (BitVec.ofNat 8 (len >>> (32 : Nat)).toNat)).set 2
           (BitVec.ofNat 8 (len >>> (24 : Nat)).toNat)).set 3
           (BitVec.ofNat 8 (len >>> (16 : Nat)).toNat)).set 4
           (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 5
           (BitVec.ofNat 8 len.toNat)) **
     (cellPtr ↦ₘ (6 : Word)))
    (by pcf) hli10
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
     ((.x12 : Reg) ↦ᵣ cellPtr) **
     regOwn .x5 ** ((.x28 : Reg) ↦ᵣ (5 : Word)) **
     ((.x29 : Reg) ↦ᵣ (-1 : Word)) ** ((.x30 : Reg) ↦ᵣ (6 : Word)) **
     regOwn .x31 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((((((outBytes.set 0 (0xFC : BitVec 8)).set 1
           (BitVec.ofNat 8 (len >>> (32 : Nat)).toNat)).set 2
           (BitVec.ofNat 8 (len >>> (24 : Nat)).toNat)).set 3
           (BitVec.ofNat 8 (len >>> (16 : Nat)).toNat)).set 4
           (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 5
           (BitVec.ofNat 8 len.toNat)) **
     (cellPtr ↦ₘ (6 : Word)))
    (by pcf) hret
  -- ══ compose: 17 ladder + 5 header + 36 loop + 3 epilogue + 1 ret = 62 ══
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hli5F ht1F
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 hli28_1F
  have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc2 hli29F
  have hc4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc3 hnt10F
  have hc5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc4 hli28_2F
  have hc6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc5 hsll_2F
  have hc7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc6 hnt13F
  have hc8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc7 hli28_3F
  have hc9 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc8 hsll_3F
  have hc10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc9 hnt16F
  have hc11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc10 hli28_4F
  have hc12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc11 hsll_4F
  have hc13 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc12 hnt19F
  have hc14 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc13 hli28_5F
  have hc15 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc14 hsll_5F
  have hc16 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc15 ht22F
  have hc17 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc16 ha30F
  have hc18 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc17 hsb31F
  have hc19 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc18 hmvF
  have hc20 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc19 ha33F
  have hc21 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc20 ha34F
  have hc22 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc21 hloopF
  have hc23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc22 ha42F
  have hc24 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc23 hsdF
  have hc25 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc24 hli10F
  have hc26 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc25 hretF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hc26
  have hq1 : (((.x28 : Reg) ↦ᵣ (5 : Word)) **
      (((.x29 : Reg) ↦ᵣ (-1 : Word)) **
       (((.x30 : Reg) ↦ᵣ (6 : Word)) **
        (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
         ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
         regOwn .x5 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr
           ((((((outBytes.set 0 (0xFC : BitVec 8)).set 1
               (BitVec.ofNat 8 (len >>> (32 : Nat)).toNat)).set 2
               (BitVec.ofNat 8 (len >>> (24 : Nat)).toNat)).set 3
               (BitVec.ofNat 8 (len >>> (16 : Nat)).toNat)).set 4
               (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 5
               (BitVec.ofNat 8 len.toNat)) **
         (cellPtr ↦ₘ (6 : Word)))))) h := by
    xperm_hyp hq
  have hq2 := sepConj_mono (regIs_to_regOwn .x28 _)
    (sepConj_mono (regIs_to_regOwn .x29 _)
      (sepConj_mono (regIs_to_regOwn .x30 _) (fun _ hh => hh))) h hq1
  xperm_hyp hq2

end RlpEncodeListPrefixLong5Spec

end EvmAsm.Codegen
