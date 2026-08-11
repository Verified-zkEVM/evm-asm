/-
  EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong2Spec

  **`rlp_encode_list_prefix`, 2-length-byte long form** (GH #10780 item 3).

  `RlpSpliceHelperSpec.lean` proves the short form (`len < 56`) and the 1-length-byte
  long form (`56 ≤ len < 256`). This module adds `256 ≤ len < 65536`: header byte
  `0xF9` followed by the two big-endian length bytes, header length 3.

  ## Why a sibling module

  `RlpSpliceHelperSpec.lean` is at ~1337 of the hard 1500-line cap and this proof is
  ~400 lines, so it cannot go there. Same split as `RlpEncodeUintBeSAsm` →
  `RlpEncodeUintBeComposeSAsm`. The file-local `cmem` macro and the four `private`
  arithmetic helpers are re-declared below rather than exported, so nothing in the
  existing module changes.

  ## What is new here versus the long1 arm

  1. **The lenlen search runs one step further.** `BLTU x10, 256` (idx10) is *not*
     taken, so control falls into idx11–13, where `x28 := 2` and `x29 := 256 <<< 8`
     before `BLTU x10, 65536` (idx13) jumps to the shared header writer.
  2. ⭐ **The length-byte loop iterates twice**, not once. idx35–41 is a real loop with
     a back edge at idx41, and this is the first arm where it runs more than one
     iteration — the step count goes 22 → **32** (3 extra dispatch steps + 7 for the
     second body). The loop is unrolled here rather than given an invariant, which is
     the right call at `lenlen = 2` and stops being so around `lenlen = 4`: see the
     note at the end of this header.
  3. ⭐ **Canonical form is now a real obligation.** With two length bytes the encoding
     is only valid RLP if the *first* one is nonzero — a leading zero in a
     length-of-length still parses and hashes differently, which is exactly #10780's
     item 1. `long2_first_length_byte_ne_zero` discharges it: from `256 ≤ len` the
     high byte is `len / 256 ≥ 1`. At `lenlen = 1` this was vacuous (a single length
     byte cannot lead with a zero), so this arm is where the property starts to bite.

  ## Byte order, read off the loop rather than assumed

  `x29` starts at `lenlen - 1 = 1` and counts **down**, while `x30` starts at
  `outPtr + 1` and counts **up**. So the first iteration stores `len >>> 8` at
  `out[1]` and the second stores `len` at `out[2]` — big-endian, most significant
  first, matching RLP. Getting this backwards would still typecheck against a
  postcondition that named the bytes symmetrically, which is why the postcondition
  below pins each index to its own shift.

  ## Scope

  Proof only; no emitted bytes change. `lenlen ≥ 3` remains open, and the honest note
  for whoever takes it: unrolling stops paying around `lenlen = 4`. The general arm
  wants the loop stated once as `cpsBranchWithin` with the invariant "`out[1..k]` holds
  the top `k` bytes of `len` and `x29 = lenlen - 1 - k`", instantiated per width —
  otherwise the file grows by ~200 lines per byte.
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

namespace EvmAsm.Codegen

namespace RlpEncodeListPrefixLong2Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP

/-- Code-membership for a `∀ base` `ofProg` slice: instruction `k` of the program,
    addressed as a concrete `base + OFF` term. Mirrors `RlpSpliceHelperSpec`'s
    file-local macro of the same name (it is `local`, so not importable). -/
local macro "cmem" k:term:max : tactic =>
  `(tactic| exact CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr _ _ $k _ (by decide) (by decide) (by bv_omega)))

/-! ## Arithmetic helpers

    Re-declared from `RlpSpliceHelperSpec.lean`, where they are `private`. -/

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

private theorem srl_zero (x : Word) : x >>> ((0 : Word).toNat % 64) = x := by
  rw [show ((0 : Word)).toNat % 64 = 0 from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  simp

/-- The second length byte's shift, normalised. -/
private theorem srl_eight (x : Word) : x >>> ((8 : Word).toNat % 64) = x >>> (8 : Nat) := by
  rw [show ((8 : Word)).toNat % 64 = 8 from by decide]

/-! ## ⭐ Canonical form: the length-of-length carries no leading zero -/

/-- **The first length byte is nonzero.** With two length bytes, RLP requires the
    length-of-length to be minimal, i.e. `out[1] ≠ 0`; a header carrying a leading
    zero there still *parses* and hashes differently, so this is a correctness
    property and not cosmetics (#10780 item 1).

    It follows from the arm's own lower bound: `256 ≤ len` forces the high byte
    `len / 256` to be at least 1, and `len < 65536` keeps it below 256 so the
    truncation cannot wrap it back to zero. At `lenlen = 1` the corresponding claim is
    vacuous, which is why it first appears here. -/
theorem long2_first_length_byte_ne_zero {len : Word}
    (h_lo : 256 ≤ len.toNat) (h_hi : len.toNat < 65536) :
    BitVec.ofNat 8 (len >>> (8 : Nat)).toNat ≠ 0 := by
  have hsh : (len >>> (8 : Nat)).toNat = len.toNat / 256 := by
    rw [BitVec.toNat_ushiftRight]
    norm_num [Nat.shiftRight_eq_div_pow]
  intro hzero
  have hz : (0 : BitVec 8).toNat = 0 := by decide
  have h0 := congrArg BitVec.toNat hzero
  rw [BitVec.toNat_ofNat, hsh, hz] at h0
  norm_num at h0
  omega

/-! ## The triple -/

/-- **`rlp_encode_list_prefix`, 2-length-byte long form** (`256 ≤ len < 65536`):
    writes the header bytes `[0xF9, len >>> 8, len]` and header length 3, returns
    `a0 = 0`; scratch registers pinned.

    Clobbers `t0`/`t3`–`t6` (`x5`, `x28`–`x31`) as the long1 arm does; `x6`/`x7` are
    untouched on this path and so do not appear.

    The two length bytes are pinned to their own shifts — `out[1]` to `len >>> 8` and
    `out[2]` to `len` — because the loop counts `x29` down while counting `x30` up, and
    a symmetric statement would not detect the two being swapped. Combined with
    `long2_first_length_byte_ne_zero`, `out[1]` is additionally known to be nonzero,
    which is what makes the emitted header canonical RLP. -/
theorem rlp_encode_list_prefix_long2_pinned_spec_within
    (base len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 256 ≤ len.toNat)
    (h_len_hi : len.toNat < 65536)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 2 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 32 base (raVal &&& ~~~1)
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
         (((outBytes.set 0 (0xF9 : BitVec 8)).set 1
             (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 2
           (BitVec.ofNat 8 len.toNat)) **
       (cellPtr ↦ₘ (3 : Word))) := by
  set CR := CodeReq.ofProg base rlpEncodeListPrefix_prog with hCR
  have h_out_len0 : 0 < outBytes.length := by omega
  have h_out_len1 : 1 < outBytes.length := by omega
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
  have hli28 := liftCode (cr' := CR)
    (li_spec_gen_within .x28 v28 (1 : Word) (base + 32) (by decide))
    (by rw [hCR]; cmem 8)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at hli28
  -- idx9 (base+36): LI x29, 256
  have hli29 := liftCode (cr' := CR)
    (li_spec_gen_within .x29 v29 (256 : Word) (base + 36) (by decide))
    (by rw [hCR]; cmem 9)
  rw [show (base + 36 : Word) + 4 = base + 40 from by bv_omega] at hli29
  -- idx10 (base+40): BLTU x10, x29, +80 — NOT taken (len ≥ 256) → base+44
  have hbr10 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 10)
    (h := bltu_spec_gen_within .x10 .x29 (80 : BitVec 13) len (256 : Word) (base + 40))
  rw [show (base + 40 : Word) + signExtend13 (80 : BitVec 13) = base + 120 from by
        rw [show signExtend13 (80 : BitVec 13) = (80 : Word) from by decide]; bv_omega,
      show (base + 40 : Word) + 4 = base + 44 from by bv_omega] at hbr10
  have hnult256 : ¬ BitVec.ult len (256 : Word) :=
    not_ult_of_toNat_ge (by rw [show ((256 : Word)).toNat = 256 from by decide]; omega)
  have hnt10 := cpsBranchWithin_ntakenStripPure2 hbr10 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hnult256 ((sepConj_pure_right _).1 hQ).2)
  -- idx11 (base+44): LI x28, 2
  have hli28b := liftCode (cr' := CR)
    (li_spec_gen_within .x28 (1 : Word) (2 : Word) (base + 44) (by decide))
    (by rw [hCR]; cmem 11)
  rw [show (base + 44 : Word) + 4 = base + 48 from by bv_omega] at hli28b
  -- idx12 (base+48): SLLI x29, x29, 8 — x29 := 65536
  have hsll12 := liftCode (cr' := CR)
    (slli_spec_gen_same_within .x29 (256 : Word) (8 : BitVec 6) (base + 48) (by decide))
    (by rw [hCR]; cmem 12)
  rw [show (base + 48 : Word) + 4 = base + 52 from by bv_omega,
      show ((256 : Word) <<< ((8 : BitVec 6)).toNat) = (65536 : Word) from by decide] at hsll12
  -- idx13 (base+52): BLTU x10, x29, +68 — TAKEN (len < 65536) → base+120
  have hbr13 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 13)
    (h := bltu_spec_gen_within .x10 .x29 (68 : BitVec 13) len (65536 : Word) (base + 52))
  rw [show (base + 52 : Word) + signExtend13 (68 : BitVec 13) = base + 120 from by
        rw [show signExtend13 (68 : BitVec 13) = (68 : Word) from by decide]; bv_omega,
      show (base + 52 : Word) + 4 = base + 56 from by bv_omega] at hbr13
  have hult65536 : BitVec.ult len (65536 : Word) :=
    ult_of_toNat_lt (by rw [show ((65536 : Word)).toNat = 65536 from by decide]; omega)
  have ht13 := cpsBranchWithin_takenStripPure2 hbr13 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ((sepConj_pure_right _).1 hQ).2 hult65536)
  -- idx30 (base+120): ADDI x29, x28, 247 — x29 := 0xF9
  have ha30 := liftCode (cr' := CR)
    (addi_spec_gen_within .x29 .x28 (65536 : Word) (2 : Word)
      (247 : BitVec 12) (base + 120) (by decide))
    (by rw [hCR]; cmem 30)
  rw [show (base + 120 : Word) + 4 = base + 124 from by bv_omega,
      show (2 : Word) + signExtend12 (247 : BitVec 12) = (249 : Word) from by decide] at ha30
  -- idx31 (base+124): SB x11, x29 — out[0] := 0xF9
  have hsb31 := liftCode (cr' := CR)
    (bytesRegion_sb_within .x11 .x29 outPtr (249 : Word) (base + 124) outBytes 0
      h_out_align h_out_len0 (by have := outPtr.isLt; omega) (h_out_valid 0 h_out_len0))
    (by rw [hCR]; cmem 31)
  rw [show outPtr + BitVec.ofNat 64 0 = outPtr from by bv_omega,
      show ((249 : Word)).truncate 8 = (0xF9 : BitVec 8) from by decide,
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
  -- idx34 (base+136): ADDI x29, x28, -1 — x29 := 1
  have ha34 := liftCode (cr' := CR)
    (addi_spec_gen_within .x29 .x28 (249 : Word) (2 : Word)
      (-1 : BitVec 12) (base + 136) (by decide))
    (by rw [hCR]; cmem 34)
  rw [show (base + 136 : Word) + 4 = base + 140 from by bv_omega,
      show (2 : Word) + signExtend12 (-1 : BitVec 12) = (1 : Word) from by decide] at ha34
  -- ══ iteration 1: x29 = 1, stores the HIGH byte at out[1] ══
  -- idx35 (base+140): BLT x29, x0, +28 — NOT taken (1 <ₛ 0 false) → base+144
  have hbr35a := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 35)
    (h := blt_spec_gen_within .x29 .x0 (28 : BitVec 13) (1 : Word) (0 : Word) (base + 140))
  rw [show (base + 140 : Word) + signExtend13 (28 : BitVec 13) = base + 168 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega,
      show (base + 140 : Word) + 4 = base + 144 from by bv_omega] at hbr35a
  have hnt35a := cpsBranchWithin_ntakenStripPure2 hbr35a (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact (by decide : ¬ BitVec.slt (1 : Word) (0 : Word))
      ((sepConj_pure_right _).1 hQ).2)
  -- idx36 (base+144): SLLI x31, x29, 3 — x31 := 8
  have hslla := liftCode (cr' := CR)
    (slli_spec_gen_within .x31 .x29 v31 (1 : Word) (3 : BitVec 6) (base + 144) (by decide))
    (by rw [hCR]; cmem 36)
  rw [show (base + 144 : Word) + 4 = base + 148 from by bv_omega,
      show ((1 : Word) <<< ((3 : BitVec 6)).toNat) = (8 : Word) from by decide] at hslla
  -- idx37 (base+148): SRL x5, x10, x31 — x5 := len >>> 8
  have hsrla := liftCode (cr' := CR)
    (srl_spec_gen_within .x5 .x10 .x31 (56 : Word) len (8 : Word) (base + 148) (by decide))
    (by rw [hCR]; cmem 37)
  rw [show (base + 148 : Word) + 4 = base + 152 from by bv_omega, srl_eight len] at hsrla
  -- idx38 (base+152): SB x30, x5 — out[1] := high byte
  have hsb38a := liftCode (cr' := CR)
    (bytesRegion_sb_within .x30 .x5 outPtr (len >>> (8 : Nat)) (base + 152)
      (outBytes.set 0 (0xF9 : BitVec 8)) 1
      h_out_align (by rw [List.length_set]; exact h_out_len1)
      (by have := outPtr.isLt; omega) (h_out_valid 1 h_out_len1))
    (by rw [hCR]; cmem 38)
  rw [trunc8_eq_ofNat_toNat (len >>> (8 : Nat)),
      show (base + 152 : Word) + 4 = base + 156 from by bv_omega] at hsb38a
  -- idx39 (base+156): ADDI x30, x30, 1 — x30 := outPtr + 2
  have ha39a := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x30 (outPtr + BitVec.ofNat 64 1)
      (1 : BitVec 12) (base + 156) (by decide))
    (by rw [hCR]; cmem 39)
  rw [show (base + 156 : Word) + 4 = base + 160 from by bv_omega,
      show (outPtr + BitVec.ofNat 64 1) + signExtend12 (1 : BitVec 12)
        = outPtr + BitVec.ofNat 64 2 from by
          rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide];
            bv_omega] at ha39a
  -- idx40 (base+160): ADDI x29, x29, -1 — x29 := 0
  have ha40a := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x29 (1 : Word) (-1 : BitVec 12) (base + 160) (by decide))
    (by rw [hCR]; cmem 40)
  rw [show (base + 160 : Word) + 4 = base + 164 from by bv_omega,
      show (1 : Word) + signExtend12 (-1 : BitVec 12) = (0 : Word) from by decide] at ha40a
  -- idx41 (base+164): JAL x0, -24 — back-jump → base+140
  have hjala := liftCode (cr' := CR)
    (jal_x0_spec_gen_within (-24 : BitVec 21) (base + 164))
    (by rw [hCR]; cmem 41)
  rw [show (base + 164 : Word) + signExtend21 (-24 : BitVec 21) = base + 140 from by
        rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega] at hjala
  -- ══ iteration 2: x29 = 0, stores the LOW byte at out[2] ══
  -- idx35 (base+140): BLT x29, x0, +28 — NOT taken (0 <ₛ 0 false) → base+144
  have hbr35b := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 35)
    (h := blt_spec_gen_within .x29 .x0 (28 : BitVec 13) (0 : Word) (0 : Word) (base + 140))
  rw [show (base + 140 : Word) + signExtend13 (28 : BitVec 13) = base + 168 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega,
      show (base + 140 : Word) + 4 = base + 144 from by bv_omega] at hbr35b
  have hnt35b := cpsBranchWithin_ntakenStripPure2 hbr35b (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact (by decide : ¬ BitVec.slt (0 : Word) (0 : Word))
      ((sepConj_pure_right _).1 hQ).2)
  -- idx36 (base+144): SLLI x31, x29, 3 — x31 := 0
  have hsllb := liftCode (cr' := CR)
    (slli_spec_gen_within .x31 .x29 (8 : Word) (0 : Word) (3 : BitVec 6) (base + 144)
      (by decide))
    (by rw [hCR]; cmem 36)
  rw [show (base + 144 : Word) + 4 = base + 148 from by bv_omega,
      show ((0 : Word) <<< ((3 : BitVec 6)).toNat) = (0 : Word) from by decide] at hsllb
  -- idx37 (base+148): SRL x5, x10, x31 — x5 := len >>> 0 = len
  have hsrlb := liftCode (cr' := CR)
    (srl_spec_gen_within .x5 .x10 .x31 (len >>> (8 : Nat)) len (0 : Word) (base + 148)
      (by decide))
    (by rw [hCR]; cmem 37)
  rw [show (base + 148 : Word) + 4 = base + 152 from by bv_omega, srl_zero len] at hsrlb
  -- idx38 (base+152): SB x30, x5 — out[2] := low byte
  have hsb38b := liftCode (cr' := CR)
    (bytesRegion_sb_within .x30 .x5 outPtr len (base + 152)
      ((outBytes.set 0 (0xF9 : BitVec 8)).set 1
        (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)) 2
      h_out_align (by rw [List.length_set, List.length_set]; exact h_out_len)
      (by have := outPtr.isLt; omega) (h_out_valid 2 h_out_len))
    (by rw [hCR]; cmem 38)
  rw [trunc8_eq_ofNat_toNat len,
      show (base + 152 : Word) + 4 = base + 156 from by bv_omega] at hsb38b
  -- idx39 (base+156): ADDI x30, x30, 1 — x30 := outPtr + 3
  have ha39b := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x30 (outPtr + BitVec.ofNat 64 2)
      (1 : BitVec 12) (base + 156) (by decide))
    (by rw [hCR]; cmem 39)
  rw [show (base + 156 : Word) + 4 = base + 160 from by bv_omega,
      show (outPtr + BitVec.ofNat 64 2) + signExtend12 (1 : BitVec 12)
        = outPtr + BitVec.ofNat 64 3 from by
          rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide];
            bv_omega] at ha39b
  -- idx40 (base+160): ADDI x29, x29, -1 — x29 := -1
  have ha40b := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x29 (0 : Word) (-1 : BitVec 12) (base + 160) (by decide))
    (by rw [hCR]; cmem 40)
  rw [show (base + 160 : Word) + 4 = base + 164 from by bv_omega,
      show (0 : Word) + signExtend12 (-1 : BitVec 12)
        = (0xFFFFFFFFFFFFFFFF : Word) from by decide] at ha40b
  -- idx41 (base+164): JAL x0, -24 — back-jump → base+140
  have hjalb := liftCode (cr' := CR)
    (jal_x0_spec_gen_within (-24 : BitVec 21) (base + 164))
    (by rw [hCR]; cmem 41)
  rw [show (base + 164 : Word) + signExtend21 (-24 : BitVec 21) = base + 140 from by
        rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega] at hjalb
  -- ══ loop exit ══
  -- idx35 (base+140): BLT x29, x0, +28 — TAKEN (-1 <ₛ 0) → base+168
  have hbr35c := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 35)
    (h := blt_spec_gen_within .x29 .x0 (28 : BitVec 13)
      (0xFFFFFFFFFFFFFFFF : Word) (0 : Word) (base + 140))
  rw [show (base + 140 : Word) + signExtend13 (28 : BitVec 13) = base + 168 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega,
      show (base + 140 : Word) + 4 = base + 144 from by bv_omega] at hbr35c
  have ht35 := cpsBranchWithin_takenStripPure2 hbr35c (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ((sepConj_pure_right _).1 hQ).2
      (by decide : BitVec.slt (0xFFFFFFFFFFFFFFFF : Word) (0 : Word)))
  -- idx42 (base+168): ADDI x30, x28, 1 — x30 := 3 (header length)
  have ha42 := liftCode (cr' := CR)
    (addi_spec_gen_within .x30 .x28 (outPtr + BitVec.ofNat 64 3) (2 : Word)
      (1 : BitVec 12) (base + 168) (by decide))
    (by rw [hCR]; cmem 42)
  rw [show (base + 168 : Word) + 4 = base + 172 from by bv_omega,
      show (2 : Word) + signExtend12 (1 : BitVec 12) = (3 : Word) from by decide] at ha42
  -- idx43 (base+172): SD x12, x30 — *cell := 3
  have hsd := liftCode (cr' := CR)
    (sd_spec_within .x12 .x30 cellPtr (3 : Word) cellOld (0 : BitVec 12) (base + 172))
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
  have hli28F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hli28
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
  have hli28bF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x29 : Reg) ↦ᵣ (256 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hli28b
  have hsll12F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsll12
  have ht13F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) ht13
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
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsb31
  have hmvF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x29 : Reg) ↦ᵣ (249 : Word)) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (0xF9 : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hmv
  have ha33F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x29 : Reg) ↦ᵣ (249 : Word)) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (0xF9 : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha33
  have ha34F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (0xF9 : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha34
  have hnt35aF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) ** ((.x31 : Reg) ↦ᵣ v31) **
     bytesRegion outPtr (outBytes.set 0 (0xF9 : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hnt35a
  have hsllaF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (0xF9 : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hslla
  have hsrlaF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x28 : Reg) ↦ᵣ (2 : Word)) ** ((.x29 : Reg) ↦ᵣ (1 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (0xF9 : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsrla
  have hsb38aF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x28 : Reg) ↦ᵣ (2 : Word)) ** ((.x29 : Reg) ↦ᵣ (1 : Word)) **
     ((.x31 : Reg) ↦ᵣ (8 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsb38a
  have ha39aF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (len >>> (8 : Nat))) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x29 : Reg) ↦ᵣ (1 : Word)) ** ((.x31 : Reg) ↦ᵣ (8 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF9 : BitVec 8)).set 1
         (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha39a
  have ha40aF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (len >>> (8 : Nat))) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 2)) ** ((.x31 : Reg) ↦ᵣ (8 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF9 : BitVec 8)).set 1
         (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha40a
  have hjalaF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (len >>> (8 : Nat))) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x29 : Reg) ↦ᵣ (0 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 2)) ** ((.x31 : Reg) ↦ᵣ (8 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF9 : BitVec 8)).set 1
         (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hjala
  rw [sepConj_emp_left'] at hjalaF
  have hnt35bF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (len >>> (8 : Nat))) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 2)) ** ((.x31 : Reg) ↦ᵣ (8 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF9 : BitVec 8)).set 1
         (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hnt35b
  have hsllbF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (len >>> (8 : Nat))) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 2)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF9 : BitVec 8)).set 1
         (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsllb
  have hsrlbF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x28 : Reg) ↦ᵣ (2 : Word)) ** ((.x29 : Reg) ↦ᵣ (0 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 2)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF9 : BitVec 8)).set 1
         (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsrlb
  have hsb38bF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x28 : Reg) ↦ᵣ (2 : Word)) ** ((.x29 : Reg) ↦ᵣ (0 : Word)) **
     ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsb38b
  have ha39bF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       (((outBytes.set 0 (0xF9 : BitVec 8)).set 1
           (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 2
         (BitVec.ofNat 8 len.toNat)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha39b
  have ha40bF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 3)) ** ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       (((outBytes.set 0 (0xF9 : BitVec 8)).set 1
           (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 2
         (BitVec.ofNat 8 len.toNat)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha40b
  have hjalbF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x29 : Reg) ↦ᵣ (0xFFFFFFFFFFFFFFFF : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 3)) ** ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       (((outBytes.set 0 (0xF9 : BitVec 8)).set 1
           (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 2
         (BitVec.ofNat 8 len.toNat)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hjalb
  rw [sepConj_emp_left'] at hjalbF
  have ht35F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 3)) ** ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       (((outBytes.set 0 (0xF9 : BitVec 8)).set 1
           (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 2
         (BitVec.ofNat 8 len.toNat)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) ht35
  have ha42F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) **
     ((.x29 : Reg) ↦ᵣ (0xFFFFFFFFFFFFFFFF : Word)) **
     ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       (((outBytes.set 0 (0xF9 : BitVec 8)).set 1
           (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 2
         (BitVec.ofNat 8 len.toNat)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha42
  have hsdF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x29 : Reg) ↦ᵣ (0xFFFFFFFFFFFFFFFF : Word)) **
     ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       (((outBytes.set 0 (0xF9 : BitVec 8)).set 1
           (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 2
         (BitVec.ofNat 8 len.toNat)))
    (by pcf) hsd
  have hli10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x29 : Reg) ↦ᵣ (0xFFFFFFFFFFFFFFFF : Word)) **
     ((.x30 : Reg) ↦ᵣ (3 : Word)) ** ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       (((outBytes.set 0 (0xF9 : BitVec 8)).set 1
           (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 2
         (BitVec.ofNat 8 len.toNat)) **
     (cellPtr ↦ₘ (3 : Word)))
    (by pcf) hli10
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
     ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (2 : Word)) **
     ((.x29 : Reg) ↦ᵣ (0xFFFFFFFFFFFFFFFF : Word)) **
     ((.x30 : Reg) ↦ᵣ (3 : Word)) ** ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       (((outBytes.set 0 (0xF9 : BitVec 8)).set 1
           (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 2
         (BitVec.ofNat 8 len.toNat)) **
     (cellPtr ↦ₘ (3 : Word)))
    (by pcf) hret
  -- ══ compose ══
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hli5F ht1F
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 hli28F
  have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc2 hli29F
  have hc4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc3 hnt10F
  have hc5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc4 hli28bF
  have hc6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc5 hsll12F
  have hc7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc6 ht13F
  have hc8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc7 ha30F
  have hc9 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc8 hsb31F
  have hc10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc9 hmvF
  have hc11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc10 ha33F
  have hc12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc11 ha34F
  have hc13 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc12 hnt35aF
  have hc14 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc13 hsllaF
  have hc15 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc14 hsrlaF
  have hc16 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc15 hsb38aF
  have hc17 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc16 ha39aF
  have hc18 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc17 ha40aF
  have hc19 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc18 hjalaF
  have hc20 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc19 hnt35bF
  have hc21 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc20 hsllbF
  have hc22 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc21 hsrlbF
  have hc23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc22 hsb38bF
  have hc24 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc23 ha39bF
  have hc25 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc24 ha40bF
  have hc26 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc25 hjalbF
  have hc27 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc26 ht35F
  have hc28 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc27 ha42F
  have hc29 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc28 hsdF
  have hc30 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc29 hli10F
  have hc31 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc30 hretF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hc31
  have hq1 : (((.x5 : Reg) ↦ᵣ len) **
      (((.x28 : Reg) ↦ᵣ (2 : Word)) **
       (((.x29 : Reg) ↦ᵣ (0xFFFFFFFFFFFFFFFF : Word)) **
        (((.x30 : Reg) ↦ᵣ (3 : Word)) **
         (((.x31 : Reg) ↦ᵣ (0 : Word)) **
          (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
           ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion outPtr
             (((outBytes.set 0 (0xF9 : BitVec 8)).set 1
                 (BitVec.ofNat 8 (len >>> (8 : Nat)).toNat)).set 2
               (BitVec.ofNat 8 len.toNat)) **
           (cellPtr ↦ₘ (3 : Word)))))))) h := by
    xperm_hyp hq
  have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
    (sepConj_mono (regIs_to_regOwn .x28 _)
      (sepConj_mono (regIs_to_regOwn .x29 _)
        (sepConj_mono (regIs_to_regOwn .x30 _)
          (sepConj_mono (regIs_to_regOwn .x31 _) (fun _ hh => hh))))) h hq1
  xperm_hyp hq2

end RlpEncodeListPrefixLong2Spec

end EvmAsm.Codegen
