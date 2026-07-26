/-
  EvmAsm.Codegen.Programs.HpDecodeNibblesSAsmPaths

  Path assembly + whole-routine contract for the verified byte-transparent
  `hp_decode_nibbles` port (bead evm-asm-4ch8f.16.3) — the five control
  paths over the segment/loop triples of `HpDecodeNibblesSAsm.lean`, the
  unified single-exit body, and the `abiFrame_spec` wrap
  (`hp_decode_nibbles_spec`).  Split from the base module for the file-size
  gate; see that file's header for the routine and model documentation.
-/

import EvmAsm.Codegen.Programs.HpDecodeNibblesSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace HpDecodeNibblesSAsm

open BytesToNibblesSAsm (highNibble lowNibble nibblePair nibblePrefix
  length_nibblePrefix)

/-! ## Path assembly -/

/-- The full body footprint at one program point (fixed atom order). -/
private def hdnFoot (src dst cnt isl : Word) (srcBytes : List (BitVec 8))
    (x10v x8v x11v x9v x12v x18v x13v x19v x14v x20v : Word)
    (w5 w6 w7 w28 w29 w30 w31 : Word)
    (bufW : List (BitVec 8)) (cntW islW : Word) : Assertion :=
  (.x10 ↦ᵣ x10v) ** (.x8 ↦ᵣ x8v) ** (.x11 ↦ᵣ x11v) ** (.x9 ↦ᵣ x9v)
  ** (.x12 ↦ᵣ x12v) ** (.x18 ↦ᵣ x18v) ** (.x13 ↦ᵣ x13v) ** (.x19 ↦ᵣ x19v)
  ** (.x14 ↦ᵣ x14v) ** (.x20 ↦ᵣ x20v)
  ** (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28)
  ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31) ** (Reg.x0 ↦ᵣ (0 : Word))
  ** bytesRegion src srcBytes ** bytesRegion dst bufW
  ** (cnt ↦ₘ cntW) ** (isl ↦ₘ islW)

private theorem pcFree_hdnFoot (src dst cnt isl : Word) (srcBytes : List (BitVec 8))
    (x10v x8v x11v x9v x12v x18v x13v x19v x14v x20v : Word)
    (w5 w6 w7 w28 w29 w30 w31 : Word)
    (bufW : List (BitVec 8)) (cntW islW : Word) :
    (hdnFoot src dst cnt isl srcBytes x10v x8v x11v x9v x12v x18v x13v x19v
      x14v x20v w5 w6 w7 w28 w29 w30 w31 bufW cntW islW).pcFree := by
  unfold hdnFoot
  repeat' first
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj

/-- Path A: `len = 0` — the first guard branches straight to the fail
    tail; nothing is written. -/
private theorem pathA_spec (base src dst cnt isl : Word)
    (srcBytes bufOrig : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl : Word)
    (s8 s9 s18 s19 s20 : Word)
    (hlen0 : srcBytes.length = 0) :
    cpsTripleWithin 7 (bAt base 0) (bAt base 36) (hdnCr base)
      (hdnFoot src dst cnt isl srcBytes src s8 (BitVec.ofNat 64 srcBytes.length)
        s9 dst s18 cnt s19 isl s20 v5 v6 v7 v28 v29 v30 v31 bufOrig oldCnt oldIsl)
      (hdnFoot src dst cnt isl srcBytes (1 : Word) src
        (BitVec.ofNat 64 srcBytes.length) (BitVec.ofNat 64 srcBytes.length)
        dst dst cnt cnt isl isl v5 v6 v7 v28 v29 v30 v31 bufOrig oldCnt oldIsl) := by
  have h0 := seg0_spec base src (BitVec.ofNat 64 srcBytes.length) dst cnt isl
    s8 s9 s18 s19 s20
  have h1 := br1_taken base (BitVec.ofNat 64 srcBytes.length)
    (by rw [hlen0]; rfl)
  have h2 := fail38_spec base src
  -- Widen each link to the full footprint and chain.
  have F0 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)
      ** (Reg.x0 ↦ᵣ (0 : Word)) ** bytesRegion src srcBytes
      ** bytesRegion dst bufOrig ** (cnt ↦ₘ oldCnt) ** (isl ↦ₘ oldIsl))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h0
  have F1 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ src) ** (.x8 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)
      ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)
      ** bytesRegion src srcBytes ** bytesRegion dst bufOrig
      ** (cnt ↦ₘ oldCnt) ** (isl ↦ₘ oldIsl))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h1
  have F2 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x9 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)
      ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)
      ** (Reg.x0 ↦ᵣ (0 : Word)) ** bytesRegion src srcBytes
      ** bytesRegion dst bufOrig ** (cnt ↦ₘ oldCnt) ** (isl ↦ₘ oldIsl))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h2
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) F0 F1
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 F2
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
    (cpsTripleWithin_mono_nSteps (by omega) s2)
  · unfold hdnFoot at hp
    xperm_hyp hp
  · unfold hdnFoot
    xperm_hyp hq


/-- Shared prefix of paths C/D/E: body 0–14 (`len ≠ 0`, valid flag, is-leaf
    flag stored, `x6` reduced to the parity bit). -/
private theorem prefix2_spec (base src dst cnt isl : Word)
    (srcBytes bufOrig : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl : Word)
    (s8 s9 s18 s19 s20 : Word)
    (hlen : 0 < srcBytes.length)
    (hsalign : src.toNat % 8 = 0) (hsover : src.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ j, j < srcBytes.length →
      isValidByteAccess (src + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 13 (bAt base 0) (bAt base 13) (hdnCr base)
      (hdnFoot src dst cnt isl srcBytes src s8 (BitVec.ofNat 64 srcBytes.length)
        s9 dst s18 cnt s19 isl s20 v5 v6 v7 v28 v29 v30 v31 bufOrig oldCnt oldIsl)
      (hdnFoot src dst cnt isl srcBytes src src
        (BitVec.ofNat 64 srcBytes.length) (BitVec.ofNat 64 srcBytes.length)
        dst dst cnt cnt isl isl
        ((srcBytes.getD 0 0).zeroExtend 64)
        (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 % 2))
        (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16))
        (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))
        v29 v30 v31 bufOrig oldCnt
        (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))) := by
  have hlen64 : srcBytes.length < 2 ^ 64 := by omega
  have h0 := seg0_spec base src (BitVec.ofNat 64 srcBytes.length) dst cnt isl
    s8 s9 s18 s19 s20
  have h1 := br1_ntaken base (BitVec.ofNat 64 srcBytes.length)
    (by
      intro heq
      have h2 := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64] at h2
      rw [show (0 : Word).toNat = 0 from rfl] at h2
      omega)
  have h2 := seg1_spec base src srcBytes v5 v6 v7 v28 hlen hsalign hsover
    (hsvalid 0 hlen)
  have h3 := seg2_spec base isl oldIsl (srcBytes.getD 0 0) v28
  have F0 := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)
      ** (Reg.x0 ↦ᵣ (0 : Word)) ** bytesRegion src srcBytes
      ** bytesRegion dst bufOrig ** (cnt ↦ₘ oldCnt) ** (isl ↦ₘ oldIsl))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h0
  have F1 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ src) ** (.x8 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)
      ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)
      ** bytesRegion src srcBytes ** bytesRegion dst bufOrig
      ** (cnt ↦ₘ oldCnt) ** (isl ↦ₘ oldIsl))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h1
  have F2 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x9 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)
      ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)
      ** (Reg.x0 ↦ᵣ (0 : Word))
      ** bytesRegion dst bufOrig ** (cnt ↦ₘ oldCnt) ** (isl ↦ₘ oldIsl))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h2
  have F3 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ src) ** (.x8 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x9 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl)
      ** (.x5 ↦ᵣ ((srcBytes.getD 0 0).zeroExtend 64))
      ** (.x7 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16))
      ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)
      ** (Reg.x0 ↦ᵣ (0 : Word))
      ** bytesRegion src srcBytes ** bytesRegion dst bufOrig
      ** (cnt ↦ₘ oldCnt))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h3
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) F0 F1
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 F2
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 F3
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
    (cpsTripleWithin_mono_nSteps (by omega) s3)
  · unfold hdnFoot at hp
    xperm_hyp hp
  · unfold hdnFoot
    xperm_hyp hq

/-! ## Success-path window bridges -/

private theorem hdnOdd_true_of (bs : List (BitVec 8))
    (h : (hdnB0 bs).toNat / 16 % 2 = 1) : hdnOdd bs = true := by
  unfold hdnOdd
  exact decide_eq_true h

private theorem hdnOdd_false_of (bs : List (BitVec 8))
    (h : (hdnB0 bs).toNat / 16 % 2 = 0) : hdnOdd bs = false := by
  unfold hdnOdd
  exact decide_eq_false (by omega)

private theorem hdnC0_odd (bs : List (BitVec 8))
    (h : (hdnB0 bs).toNat / 16 % 2 = 1) : hdnC0 bs = 1 := by
  unfold hdnC0
  rw [hdnOdd_true_of bs h]
  rfl

private theorem hdnC0_even (bs : List (BitVec 8))
    (h : (hdnB0 bs).toNat / 16 % 2 = 0) : hdnC0 bs = 0 := by
  unfold hdnC0
  rw [hdnOdd_false_of bs h]
  rfl

private theorem hdnWin_zero_odd (bs orig : List (BitVec 8))
    (h : (hdnB0 bs).toNat / 16 % 2 = 1) :
    hdnWin bs orig 0 = orig.set 0 (lowNibble (hdnB0 bs)) := by
  unfold hdnWin hdnInitNibs
  rw [hdnOdd_true_of bs h]
  show setBytes orig 0 ([lowNibble (hdnB0 bs)] ++ nibblePrefix (bs.drop 1) 0) = _
  rw [show nibblePrefix (bs.drop 1) 0 = [] from rfl, List.append_nil]
  rfl

private theorem hdnWin_zero_even (bs orig : List (BitVec 8))
    (h : (hdnB0 bs).toNat / 16 % 2 = 0) :
    hdnWin bs orig 0 = orig := by
  unfold hdnWin hdnInitNibs
  rw [hdnOdd_false_of bs h]
  show setBytes orig 0 ([] ++ nibblePrefix (bs.drop 1) 0) = _
  rw [show nibblePrefix (bs.drop 1) 0 = [] from rfl]
  rfl

/-- Path E: even parity, zero padding nibble — the full success run
    through the loop. -/
private theorem pathE_spec (base src dst cnt isl : Word)
    (srcBytes bufOrig : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl : Word)
    (s8 s9 s18 s19 s20 : Word)
    (hlen : 0 < srcBytes.length)
    (heven : (srcBytes.getD 0 0).toNat / 16 % 2 = 0)
    (hsalign : src.toNat % 8 = 0) (hsover : src.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ j, j < srcBytes.length →
      isValidByteAccess (src + BitVec.ofNat 64 j) = true)
    (hbuf : hdnC0 srcBytes + 2 * (srcBytes.length - 1) ≤ bufOrig.length)
    (hdalign : dst.toNat % 8 = 0) (hdover : dst.toNat + bufOrig.length < 2 ^ 64)
    (hdvalid : ∀ j, j < bufOrig.length →
      isValidByteAccess (dst + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (13 + 4 + ((srcBytes.length - 1) * 11 + 1) + 3 + 5)
      (bAt base 0) (bAt base 36) (hdnCr base)
      (hdnFoot src dst cnt isl srcBytes src s8 (BitVec.ofNat 64 srcBytes.length)
        s9 dst s18 cnt s19 isl s20 v5 v6 v7 v28 v29 v30 v31 bufOrig oldCnt oldIsl)
      (hdnFoot src dst cnt isl srcBytes (0 : Word) src
        (BitVec.ofNat 64 srcBytes.length) (BitVec.ofNat 64 srcBytes.length)
        dst dst cnt cnt isl isl
        (BitVec.ofNat 64 srcBytes.length)
        (if srcBytes.length ≤ 1 then BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 % 2)
          else src + BitVec.ofNat 64 (srcBytes.length - 1))
        (if srcBytes.length ≤ 1 then BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16)
          else (srcBytes.getD (srcBytes.length - 1) 0).zeroExtend 64)
        (if srcBytes.length ≤ 1 then BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)
          else BitVec.ofNat 64 ((srcBytes.getD (srcBytes.length - 1) 0).toNat / 16))
        (if srcBytes.length ≤ 1 then v29
          else BitVec.ofNat 64 ((srcBytes.getD (srcBytes.length - 1) 0).toNat % 16))
        (BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1)))
        (dst + BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1)))
        (hdnWin srcBytes bufOrig (srcBytes.length - 1))
        (BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1)))
        (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))) := by
  have hc0 : hdnC0 srcBytes = 0 := hdnC0_even srcBytes heven
  have hpre := prefix2_spec base src dst cnt isl srcBytes bufOrig
    v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl s8 s9 s18 s19 s20
    hlen hsalign hsover hsvalid
  have h5 := br3_taken base (srcBytes.getD 0 0) heven
  have h7 := seg4even_spec base dst v30 v31
  have h8 := seg5_spec base ((srcBytes.getD 0 0).zeroExtend 64)
  have hLoop := loop_spec base src dst srcBytes bufOrig
    (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 % 2))
    (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16))
    (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))
    v29 hlen hsalign hsover hsvalid hbuf hdalign hdover hdvalid
  -- Normalize the loop-entry invariant (`i = 1`).
  unfold hdnInv at hLoop
  rw [if_pos (Nat.le_refl 1), if_pos (Nat.le_refl 1), if_pos (Nat.le_refl 1),
    if_pos (Nat.le_refl 1), show (1 : Nat) - 1 = 0 from rfl,
    show hdnC0 srcBytes + 2 * 0 = 0 from by rw [hc0],
    add_ofNat_zero dst,
    show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl,
    hdnWin_zero_even srcBytes bufOrig heven,
    show (BitVec.ofNat 64 1 : Word) = (1 : Word) from rfl] at hLoop
  have h9 := seg6_spec base cnt oldCnt
    (BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1))) src
  -- Frames.
  have Fb3 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ src) ** (.x8 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x9 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)
      ** (.x5 ↦ᵣ ((srcBytes.getD 0 0).zeroExtend 64))
      ** (.x7 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16))
      ** (.x28 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))
      ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)
      ** bytesRegion src srcBytes ** bytesRegion dst bufOrig
      ** (cnt ↦ₘ oldCnt)
      ** (isl ↦ₘ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h5
  have Fb5 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ src) ** (.x8 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x9 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)
      ** (.x5 ↦ᵣ ((srcBytes.getD 0 0).zeroExtend 64))
      ** (.x6 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 % 2))
      ** (.x7 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16))
      ** (.x28 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))
      ** (.x29 ↦ᵣ v29) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** bytesRegion src srcBytes ** bytesRegion dst bufOrig
      ** (cnt ↦ₘ oldCnt)
      ** (isl ↦ₘ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h7
  have Fb6 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ src) ** (.x8 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x9 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)
      ** (.x6 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 % 2))
      ** (.x7 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16))
      ** (.x28 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))
      ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ (0 : Word)) ** (.x31 ↦ᵣ dst)
      ** (Reg.x0 ↦ᵣ (0 : Word))
      ** bytesRegion src srcBytes ** bytesRegion dst bufOrig
      ** (cnt ↦ₘ oldCnt)
      ** (isl ↦ₘ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h8
  have FLoop := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** (cnt ↦ₘ oldCnt)
      ** (isl ↦ₘ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) hLoop
  have Fb7 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x9 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)
      ** (.x5 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x6 ↦ᵣ (if srcBytes.length ≤ 1
          then BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 % 2)
          else src + BitVec.ofNat 64 (srcBytes.length - 1)))
      ** (.x7 ↦ᵣ (if srcBytes.length ≤ 1
          then BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16)
          else (srcBytes.getD (srcBytes.length - 1) 0).zeroExtend 64))
      ** (.x28 ↦ᵣ (if srcBytes.length ≤ 1
          then BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)
          else BitVec.ofNat 64 ((srcBytes.getD (srcBytes.length - 1) 0).toNat / 16)))
      ** (.x29 ↦ᵣ (if srcBytes.length ≤ 1 then v29
          else BitVec.ofNat 64 ((srcBytes.getD (srcBytes.length - 1) 0).toNat % 16)))
      ** (.x31 ↦ᵣ (dst + BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1))))
      ** (Reg.x0 ↦ᵣ (0 : Word))
      ** bytesRegion src srcBytes
      ** bytesRegion dst (hdnWin srcBytes bufOrig (srcBytes.length - 1))
      ** (isl ↦ₘ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h9
  have s5 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by unfold hdnFoot at hp; xperm_hyp hp) hpre Fb3
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 Fb5
  have s8x := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 Fb6
  have s9x := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s8x FLoop
  have s10 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) s9x Fb7
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
    (cpsTripleWithin_mono_nSteps (by omega) s10)
  · exact hp
  · unfold hdnFoot
    xperm_hyp hq


/-- Path D: odd parity — head nibble stored, then the full success run. -/
private theorem pathD_spec (base src dst cnt isl : Word)
    (srcBytes bufOrig : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl : Word)
    (s8 s9 s18 s19 s20 : Word)
    (hlen : 0 < srcBytes.length)
    (hodd : (srcBytes.getD 0 0).toNat / 16 % 2 = 1)
    (hsalign : src.toNat % 8 = 0) (hsover : src.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ j, j < srcBytes.length →
      isValidByteAccess (src + BitVec.ofNat 64 j) = true)
    (hbuf : hdnC0 srcBytes + 2 * (srcBytes.length - 1) ≤ bufOrig.length)
    (hbuf0 : 0 < bufOrig.length)
    (hdalign : dst.toNat % 8 = 0) (hdover : dst.toNat + bufOrig.length < 2 ^ 64)
    (hdvalid : ∀ j, j < bufOrig.length →
      isValidByteAccess (dst + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (15 + 6 + ((srcBytes.length - 1) * 11 + 1) + 3 + 5)
      (bAt base 0) (bAt base 36) (hdnCr base)
      (hdnFoot src dst cnt isl srcBytes src s8 (BitVec.ofNat 64 srcBytes.length)
        s9 dst s18 cnt s19 isl s20 v5 v6 v7 v28 v29 v30 v31 bufOrig oldCnt oldIsl)
      (hdnFoot src dst cnt isl srcBytes (0 : Word) src
        (BitVec.ofNat 64 srcBytes.length) (BitVec.ofNat 64 srcBytes.length)
        dst dst cnt cnt isl isl
        (BitVec.ofNat 64 srcBytes.length)
        (if srcBytes.length ≤ 1 then BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 % 2)
          else src + BitVec.ofNat 64 (srcBytes.length - 1))
        (if srcBytes.length ≤ 1 then BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16)
          else (srcBytes.getD (srcBytes.length - 1) 0).zeroExtend 64)
        (if srcBytes.length ≤ 1 then BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)
          else BitVec.ofNat 64 ((srcBytes.getD (srcBytes.length - 1) 0).toNat / 16))
        (if srcBytes.length ≤ 1 then v29
          else BitVec.ofNat 64 ((srcBytes.getD (srcBytes.length - 1) 0).toNat % 16))
        (BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1)))
        (dst + BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1)))
        (hdnWin srcBytes bufOrig (srcBytes.length - 1))
        (BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1)))
        (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))) := by
  have hc1 : hdnC0 srcBytes = 1 := hdnC0_odd srcBytes hodd
  have hpre := prefix2_spec base src dst cnt isl srcBytes bufOrig
    v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl s8 s9 s18 s19 s20
    hlen hsalign hsover hsvalid
  have h5 := br3_ntaken base (srcBytes.getD 0 0) (by omega)
  have h6 := seg3odd_spec base dst (srcBytes.getD 0 0) bufOrig v30 v31
    hbuf0 hdalign hdover (hdvalid 0 hbuf0)
  rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl] at h6
  have h8 := seg5_spec base ((srcBytes.getD 0 0).zeroExtend 64)
  rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl] at h8
  have hLoop := loop_spec base src dst srcBytes bufOrig
    (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 % 2))
    (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16))
    (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))
    v29 hlen hsalign hsover hsvalid hbuf hdalign hdover hdvalid
  unfold hdnInv at hLoop
  rw [if_pos (Nat.le_refl 1), if_pos (Nat.le_refl 1), if_pos (Nat.le_refl 1),
    if_pos (Nat.le_refl 1), show (1 : Nat) - 1 = 0 from rfl,
    show hdnC0 srcBytes + 2 * 0 = 1 from by rw [hc1],
    hdnWin_zero_odd srcBytes bufOrig hodd,
    show hdnB0 srcBytes = srcBytes.getD 0 0 from rfl] at hLoop
  have h9 := seg6_spec base cnt oldCnt
    (BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1))) src
  have Fb3 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ src) ** (.x8 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x9 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)
      ** (.x5 ↦ᵣ ((srcBytes.getD 0 0).zeroExtend 64))
      ** (.x7 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16))
      ** (.x28 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))
      ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)
      ** bytesRegion src srcBytes ** bytesRegion dst bufOrig
      ** (cnt ↦ₘ oldCnt)
      ** (isl ↦ₘ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h5
  have Fb4 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ src) ** (.x8 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x9 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)
      ** (.x5 ↦ᵣ ((srcBytes.getD 0 0).zeroExtend 64))
      ** (.x6 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 % 2))
      ** (.x28 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))
      ** (.x29 ↦ᵣ v29) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** bytesRegion src srcBytes
      ** (cnt ↦ₘ oldCnt)
      ** (isl ↦ₘ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h6
  have hjal := jal19_spec base
    (P := (.x10 ↦ᵣ src) ** (.x8 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x9 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)
      ** (.x5 ↦ᵣ ((srcBytes.getD 0 0).zeroExtend 64))
      ** (.x6 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 % 2))
      ** (.x7 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16))
      ** (.x28 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))
      ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ BitVec.ofNat 64 1)
      ** (.x31 ↦ᵣ (dst + BitVec.ofNat 64 1)) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** bytesRegion src srcBytes
      ** bytesRegion dst (bufOrig.set 0 (lowNibble (srcBytes.getD 0 0)))
      ** (cnt ↦ₘ oldCnt)
      ** (isl ↦ₘ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj)
  have Fb6 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ src) ** (.x8 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x9 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)
      ** (.x6 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 % 2))
      ** (.x7 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16))
      ** (.x28 ↦ᵣ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))
      ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ BitVec.ofNat 64 1)
      ** (.x31 ↦ᵣ (dst + BitVec.ofNat 64 1)) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** bytesRegion src srcBytes
      ** bytesRegion dst (bufOrig.set 0 (lowNibble (srcBytes.getD 0 0)))
      ** (cnt ↦ₘ oldCnt)
      ** (isl ↦ₘ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h8
  have FLoop := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x19 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** (cnt ↦ₘ oldCnt)
      ** (isl ↦ₘ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) hLoop
  have Fb7 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x9 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x12 ↦ᵣ dst) ** (.x18 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt)
      ** (.x14 ↦ᵣ isl) ** (.x20 ↦ᵣ isl)
      ** (.x5 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
      ** (.x6 ↦ᵣ (if srcBytes.length ≤ 1
          then BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 % 2)
          else src + BitVec.ofNat 64 (srcBytes.length - 1)))
      ** (.x7 ↦ᵣ (if srcBytes.length ≤ 1
          then BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat % 16)
          else (srcBytes.getD (srcBytes.length - 1) 0).zeroExtend 64))
      ** (.x28 ↦ᵣ (if srcBytes.length ≤ 1
          then BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)
          else BitVec.ofNat 64 ((srcBytes.getD (srcBytes.length - 1) 0).toNat / 16)))
      ** (.x29 ↦ᵣ (if srcBytes.length ≤ 1 then v29
          else BitVec.ofNat 64 ((srcBytes.getD (srcBytes.length - 1) 0).toNat % 16)))
      ** (.x31 ↦ᵣ (dst + BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1))))
      ** (Reg.x0 ↦ᵣ (0 : Word))
      ** bytesRegion src srcBytes
      ** bytesRegion dst (hdnWin srcBytes bufOrig (srcBytes.length - 1))
      ** (isl ↦ₘ BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2)))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) h9
  have s5 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by unfold hdnFoot at hp; xperm_hyp hp) hpre Fb3
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 Fb4
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 hjal
  have s8x := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 Fb6
  have s9x := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s8x FLoop
  have s10 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) s9x Fb7
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
    (cpsTripleWithin_mono_nSteps (by omega) s10)
  · exact hp
  · unfold hdnFoot
    xperm_hyp hq


/-! ## Classification ties (guest model ↔ path outcomes) -/

private theorem hdnRes_len0 (bs : List (BitVec 8)) (h : bs.length = 0) :
    hdnRes bs = none := by
  rw [List.length_eq_zero_iff.mp h]
  rfl

private theorem hdnRes_some_odd (bs : List (BitVec 8)) (hlen : 0 < bs.length)
    (hodd : (bs.getD 0 0).toNat / 16 % 2 = 1) :
    hdnRes bs = some (decide (2 ≤ (bs.getD 0 0).toNat / 16 % 4),
      lowNibble (bs.getD 0 0)
        :: EvmAsm.Evm64.hpUnpackPairs (bs.drop 1)) := by
  match bs, hlen with
  | b0 :: rest, _ =>
    have hd : ((b0 :: rest : List (BitVec 8)).getD 0 0) = b0 := rfl
    rw [hd] at hodd ⊢
    show EvmAsm.Evm64.hpDecode (b0 :: rest) = _
    rw [lowNibble_eq,
      show (b0 :: rest : List (BitVec 8)).drop 1 = rest from rfl]
    rcases (by omega : b0.toNat / 16 % 4 = 1 ∨ b0.toNat / 16 % 4 = 3) with h1 | h3
    · rw [EvmAsm.Evm64.hpDecode_cons_div1 b0 rest h1, h1]
      rfl
    · rw [EvmAsm.Evm64.hpDecode_cons_div3 b0 rest h3, h3]
      rfl

private theorem hdnRes_some_even (bs : List (BitVec 8)) (hlen : 0 < bs.length)
    (heven : (bs.getD 0 0).toNat / 16 % 2 = 0) :
    hdnRes bs = some (decide (2 ≤ (bs.getD 0 0).toNat / 16 % 4),
      EvmAsm.Evm64.hpUnpackPairs (bs.drop 1)) := by
  match bs, hlen with
  | b0 :: rest, _ =>
    have hd : ((b0 :: rest : List (BitVec 8)).getD 0 0) = b0 := rfl
    rw [hd] at heven ⊢
    show EvmAsm.Evm64.hpDecode (b0 :: rest) = _
    rw [show (b0 :: rest : List (BitVec 8)).drop 1 = rest from rfl]
    rcases (by omega : b0.toNat / 16 % 4 = 0 ∨ b0.toNat / 16 % 4 = 2) with h0 | h2
    · rw [EvmAsm.Evm64.hpDecode_cons_div0 b0 rest h0, h0]
      rfl
    · rw [EvmAsm.Evm64.hpDecode_cons_div2 b0 rest h2, h2]
      rfl

private theorem hpUnpackPairs_length (l : List (BitVec 8)) :
    (EvmAsm.Evm64.hpUnpackPairs l).length = 2 * l.length := by
  unfold EvmAsm.Evm64.hpUnpackPairs
  rw [List.length_flatMap]
  induction l with
  | nil => rfl
  | cons a t ih => simp_all; omega

/-- On success the loop-exit window IS the spliced decode result. -/
private theorem hdnWin_final (bs orig : List (BitVec 8)) (_hlen : 0 < bs.length)
    (hnibs : hdnNibs bs
      = hdnInitNibs bs ++ EvmAsm.Evm64.hpUnpackPairs (bs.drop 1)) :
    hdnWin bs orig (bs.length - 1) = hdnBufFinal bs orig := by
  unfold hdnWin hdnBufFinal
  rw [hnibs, nibblePrefix_eq_hpUnpackPairs (bs.drop 1) (bs.length - 1)
    (by rw [List.length_drop]),
    show (bs.drop 1).take (bs.length - 1) = bs.drop 1 from by
      rw [List.take_of_length_le (by rw [List.length_drop])]]

/-- Nibble-count tie: on success, `|hdnNibs| = c0 + 2 * (len - 1)`. -/
private theorem hdnNibs_length (bs : List (BitVec 8)) (_hlen : 0 < bs.length)
    (hnibs : hdnNibs bs
      = hdnInitNibs bs ++ EvmAsm.Evm64.hpUnpackPairs (bs.drop 1)) :
    (hdnNibs bs).length = hdnC0 bs + 2 * (bs.length - 1) := by
  rw [hnibs, List.length_append, hdnInitNibs_length, hpUnpackPairs_length,
    List.length_drop]


/-! ## The unified caller contract -/

/-- Caller-visible precondition: arguments in `a0..a4`, scratch registers
    arbitrary, the input path bytes, the caller's nibble buffer, and the
    two output cells. -/
def hdnCallerPre (src dst cnt isl : Word) (srcBytes bufOrig : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl : Word) : Assertion :=
  (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length) ** (.x12 ↦ᵣ dst)
  ** (.x13 ↦ᵣ cnt) ** (.x14 ↦ᵣ isl)
  ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)
  ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)
  ** (Reg.x0 ↦ᵣ (0 : Word))
  ** bytesRegion src srcBytes ** bytesRegion dst bufOrig
  ** (cnt ↦ₘ oldCnt) ** (isl ↦ₘ oldIsl)

/-- Caller-visible postcondition — **the genuine `hp_decode_nibbles`
    semantics**: `a0` holds the status (`hdnStatusW`, 0 iff the guest-exact
    decode `hdnRes` succeeds), the nibble buffer holds the decoded nibbles
    spliced over its old contents (`hdnBufFinal`), and the count/is-leaf
    cells are updated exactly as the routine does (`hdnCntFinal` /
    `hdnIslFinal`).  Scratch registers are clobbered (`regOwn`);
    arguments `a1..a4` are preserved. -/
def hdnCallerPost (src dst cnt isl : Word) (srcBytes bufOrig : List (BitVec 8))
    (oldCnt oldIsl : Word) : Assertion :=
  (.x10 ↦ᵣ hdnStatusW srcBytes) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
  ** (.x12 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x14 ↦ᵣ isl)
  ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28
  ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
  ** (Reg.x0 ↦ᵣ (0 : Word))
  ** bytesRegion src srcBytes ** bytesRegion dst (hdnBufFinal srcBytes bufOrig)
  ** (cnt ↦ₘ hdnCntFinal srcBytes oldCnt) ** (isl ↦ₘ hdnIslFinal srcBytes oldIsl)

/-- Final saved-register values: the argument copies. -/
def hdnVals' (vals : Reg → Word) (src lenW dst cnt isl : Word) : Reg → Word :=
  fun r => match r with
  | .x8 => src
  | .x9 => lenW
  | .x18 => dst
  | .x19 => cnt
  | .x20 => isl
  | r => vals r

/-- Per-case post reconciliation: each path's concrete `hdnFoot` exit
    implies the unified caller post (given the four value ties). -/
private theorem hdnFoot_to_callerPost (src dst cnt isl : Word)
    (srcBytes bufOrig : List (BitVec 8)) (oldCnt oldIsl : Word)
    (st : Word) (w5 w6 w7 w28 w29 w30 w31 : Word)
    (bufW : List (BitVec 8)) (cntW islW : Word)
    (hst : hdnStatusW srcBytes = st)
    (hbe : hdnBufFinal srcBytes bufOrig = bufW)
    (hce : hdnCntFinal srcBytes oldCnt = cntW)
    (hie : hdnIslFinal srcBytes oldIsl = islW) :
    ∀ h, (hdnFoot src dst cnt isl srcBytes st src
        (BitVec.ofNat 64 srcBytes.length) (BitVec.ofNat 64 srcBytes.length)
        dst dst cnt cnt isl isl w5 w6 w7 w28 w29 w30 w31 bufW cntW islW) h →
      ((.x8 ↦ᵣ src) ** (.x9 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
        ** (.x18 ↦ᵣ dst) ** (.x19 ↦ᵣ cnt) ** (.x20 ↦ᵣ isl)
        ** hdnCallerPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl) h := by
  intro h hp
  unfold hdnFoot at hp
  unfold hdnCallerPost
  rw [hst, hbe, hce, hie]
  have hp2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono (regIs_to_regOwn .x5 _)
            (sepConj_mono (regIs_to_regOwn .x6 _)
              (sepConj_mono (regIs_to_regOwn .x7 _)
                (sepConj_mono (regIs_to_regOwn .x28 _)
                  (sepConj_mono (regIs_to_regOwn .x29 _)
                    (sepConj_mono (regIs_to_regOwn .x30 _)
                      (sepConj_mono (regIs_to_regOwn .x31 _)
                        (fun _ hx => hx))))))))))))))))) h hp
  xperm_hyp hp2


private theorem pcFree_frame_bundle (sp0new : Word) (vals : Reg → Word) :
    ((.x2 ↦ᵣ sp0new) ** (((.x1 : Reg) ↦ᵣ vals .x1)
      ** frameSlotsSaved hdnFrame sp0new vals)).pcFree :=
  pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
    (pcFree_frameSlotsSaved _ _ _))

/-- The unified single-exit body triple `abiFrame_spec` consumes: the
    five control paths, dispatched on the guest-exact classification. -/
private theorem hdnBody_unified (base sp0new : Word) (vals : Reg → Word)
    (src dst cnt isl : Word) (srcBytes bufOrig : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl : Word)
    (hsalign : src.toNat % 8 = 0) (hsover : src.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ j, j < srcBytes.length →
      isValidByteAccess (src + BitVec.ofNat 64 j) = true)
    (hbuf : hdnC0 srcBytes + 2 * (srcBytes.length - 1) ≤ bufOrig.length)
    (hdalign : dst.toNat % 8 = 0) (hdover : dst.toNat + bufOrig.length < 2 ^ 64)
    (hdvalid : ∀ j, j < bufOrig.length →
      isValidByteAccess (dst + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (30 + 11 * srcBytes.length)
      (base + BitVec.ofNat 64 (4 * (1 + hdnFrame.length)))
      (base + BitVec.ofNat 64 (4 * (1 + hdnFrame.length + hdnBody.length)))
      (hdnCr base)
      ((.x2 ↦ᵣ sp0new) ** regsAt hdnFrame vals
        ** frameSlotsSaved hdnFrame sp0new vals
        ** hdnCallerPre src dst cnt isl srcBytes bufOrig
            v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl)
      ((.x2 ↦ᵣ sp0new)
        ** regsAt hdnFrame
            (hdnVals' vals src (BitVec.ofNat 64 srcBytes.length) dst cnt isl)
        ** frameSlotsSaved hdnFrame sp0new vals
        ** hdnCallerPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl) := by
  show cpsTripleWithin (30 + 11 * srcBytes.length) (bAt base 0) (bAt base 36)
    (hdnCr base) _ _
  -- The five-way classification.
  by_cases hlen0 : srcBytes.length = 0
  · -- Path A: empty input.
    have hst : hdnStatusW srcBytes = 1 := by
      unfold hdnStatusW
      rw [hdnRes_len0 _ hlen0]
      rfl
    have hbe : hdnBufFinal srcBytes bufOrig = bufOrig := by
      unfold hdnBufFinal hdnNibs
      rw [hdnRes_len0 _ hlen0]
      rfl
    have hce : hdnCntFinal srcBytes oldCnt = oldCnt := by
      unfold hdnCntFinal
      rw [hdnRes_len0 _ hlen0]
      rfl
    have hie : hdnIslFinal srcBytes oldIsl = oldIsl := by
      unfold hdnIslFinal hdnIslWritten
      rw [List.length_eq_zero_iff.mp hlen0]
      rfl
    have hpath := pathA_spec base src dst cnt isl srcBytes bufOrig
      v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl
      (vals .x8) (vals .x9) (vals .x18) (vals .x19) (vals .x20) hlen0
    have hframed := cpsTripleWithin_frameR
      ((.x2 ↦ᵣ sp0new) ** (((.x1 : Reg) ↦ᵣ vals .x1)
        ** frameSlotsSaved hdnFrame sp0new vals))
      (pcFree_frame_bundle sp0new vals) hpath
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
      (cpsTripleWithin_mono_nSteps (by omega) hframed)
    · unfold hdnCallerPre at hp
      simp only [hdnFrame, regsAt_cons, regsAt_nil, frameSlotsSaved_cons,
        frameSlotsSaved_nil, sepConj_emp_right'] at hp ⊢
      unfold hdnFoot
      xperm_hyp hp
    · have hq2 := sepConj_mono_left
        (hdnFoot_to_callerPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl
          (1 : Word) v5 v6 v7 v28 v29 v30 v31 bufOrig oldCnt oldIsl
          hst hbe hce hie) h hq
      unfold hdnCallerPost at hq2 ⊢
      simp only [hdnFrame, regsAt_cons, regsAt_nil, frameSlotsSaved_cons,
        frameSlotsSaved_nil, sepConj_emp_right', hdnVals'] at hq2 ⊢
      xperm_hyp hq2
  · have hlen : 0 < srcBytes.length := by omega
    · by_cases hpar : (srcBytes.getD 0 0).toNat / 16 % 2 = 1
      · -- Path D: odd success.
        have hsome := hdnRes_some_odd srcBytes hlen hpar
        have hnibs : hdnNibs srcBytes
            = hdnInitNibs srcBytes
              ++ EvmAsm.Evm64.hpUnpackPairs (srcBytes.drop 1) := by
          unfold hdnNibs hdnInitNibs
          rw [hsome, hdnOdd_true_of srcBytes hpar]
          rfl
        have hst : hdnStatusW srcBytes = 0 := by
          unfold hdnStatusW
          rw [hsome]
          rfl
        have hbe : hdnBufFinal srcBytes bufOrig
            = hdnWin srcBytes bufOrig (srcBytes.length - 1) :=
          (hdnWin_final srcBytes bufOrig hlen hnibs).symm
        have hce : hdnCntFinal srcBytes oldCnt
            = BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1)) := by
          unfold hdnCntFinal
          rw [hsome]
          show BitVec.ofNat 64 (hdnNibs srcBytes).length = _
          rw [hdnNibs_length srcBytes hlen hnibs]
        have hie : hdnIslFinal srcBytes oldIsl
            = BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2) := by
          have hemp : srcBytes.isEmpty = false := by
            cases srcBytes
            · simp at hlen
            · rfl
          unfold hdnIslFinal hdnIslWritten
          rw [hemp]
          simp only [Bool.not_false, if_true]
          rfl
        have hbuf0 : 0 < bufOrig.length := by
          have := hdnC0_odd srcBytes hpar
          omega
        have hpath := pathD_spec base src dst cnt isl srcBytes bufOrig
          v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl
          (vals .x8) (vals .x9) (vals .x18) (vals .x19) (vals .x20)
          hlen hpar hsalign hsover hsvalid hbuf hbuf0 hdalign hdover hdvalid
        have hframed := cpsTripleWithin_frameR
          ((.x2 ↦ᵣ sp0new) ** (((.x1 : Reg) ↦ᵣ vals .x1)
            ** frameSlotsSaved hdnFrame sp0new vals))
          (pcFree_frame_bundle sp0new vals) hpath
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
          (cpsTripleWithin_mono_nSteps (by omega) hframed)
        · unfold hdnCallerPre at hp
          simp only [hdnFrame, regsAt_cons, regsAt_nil, frameSlotsSaved_cons,
            frameSlotsSaved_nil, sepConj_emp_right'] at hp ⊢
          unfold hdnFoot
          xperm_hyp hp
        · have hq2 := sepConj_mono_left
            (hdnFoot_to_callerPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl
              (0 : Word) _ _ _ _ _ _ _
              (hdnWin srcBytes bufOrig (srcBytes.length - 1))
              (BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1)))
              (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))
              hst hbe hce hie) h hq
          unfold hdnCallerPost at hq2 ⊢
          simp only [hdnFrame, regsAt_cons, regsAt_nil, frameSlotsSaved_cons,
            frameSlotsSaved_nil, sepConj_emp_right', hdnVals'] at hq2 ⊢
          xperm_hyp hq2
      · -- Path E: even success (the padding nibble is IGNORED — lenient,
        -- bead evm-asm-3umhl).
        have heven : (srcBytes.getD 0 0).toNat / 16 % 2 = 0 := by omega
        have hsome := hdnRes_some_even srcBytes hlen heven
        have hnibs : hdnNibs srcBytes
            = hdnInitNibs srcBytes
              ++ EvmAsm.Evm64.hpUnpackPairs (srcBytes.drop 1) := by
          unfold hdnNibs hdnInitNibs
          rw [hsome, hdnOdd_false_of srcBytes heven]
          rfl
        have hst : hdnStatusW srcBytes = 0 := by
          unfold hdnStatusW
          rw [hsome]
          rfl
        have hbe : hdnBufFinal srcBytes bufOrig
            = hdnWin srcBytes bufOrig (srcBytes.length - 1) :=
          (hdnWin_final srcBytes bufOrig hlen hnibs).symm
        have hce : hdnCntFinal srcBytes oldCnt
            = BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1)) := by
          unfold hdnCntFinal
          rw [hsome]
          show BitVec.ofNat 64 (hdnNibs srcBytes).length = _
          rw [hdnNibs_length srcBytes hlen hnibs]
        have hie : hdnIslFinal srcBytes oldIsl
            = BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2) := by
          have hemp : srcBytes.isEmpty = false := by
            cases srcBytes
            · simp at hlen
            · rfl
          unfold hdnIslFinal hdnIslWritten
          rw [hemp]
          simp only [Bool.not_false, if_true]
          rfl
        have hpath := pathE_spec base src dst cnt isl srcBytes bufOrig
          v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl
          (vals .x8) (vals .x9) (vals .x18) (vals .x19) (vals .x20)
          hlen heven hsalign hsover hsvalid hbuf hdalign hdover hdvalid
        have hframed := cpsTripleWithin_frameR
          ((.x2 ↦ᵣ sp0new) ** (((.x1 : Reg) ↦ᵣ vals .x1)
            ** frameSlotsSaved hdnFrame sp0new vals))
          (pcFree_frame_bundle sp0new vals) hpath
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
          (cpsTripleWithin_mono_nSteps (by omega) hframed)
        · unfold hdnCallerPre at hp
          simp only [hdnFrame, regsAt_cons, regsAt_nil, frameSlotsSaved_cons,
            frameSlotsSaved_nil, sepConj_emp_right'] at hp ⊢
          unfold hdnFoot
          xperm_hyp hp
        · have hq2 := sepConj_mono_left
            (hdnFoot_to_callerPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl
              (0 : Word) _ _ _ _ _ _ _
              (hdnWin srcBytes bufOrig (srcBytes.length - 1))
              (BitVec.ofNat 64 (hdnC0 srcBytes + 2 * (srcBytes.length - 1)))
              (BitVec.ofNat 64 ((srcBytes.getD 0 0).toNat / 16 / 2 % 2))
              hst hbe hce hie) h hq
          unfold hdnCallerPost at hq2 ⊢
          simp only [hdnFrame, regsAt_cons, regsAt_nil, frameSlotsSaved_cons,
            frameSlotsSaved_nil, sepConj_emp_right', hdnVals'] at hq2 ⊢
          xperm_hyp hq2


/-! ## The whole-routine contract -/

private theorem pcFree_hdnCallerPre (src dst cnt isl : Word)
    (srcBytes bufOrig : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl : Word) :
    (hdnCallerPre src dst cnt isl srcBytes bufOrig
      v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl).pcFree := by
  unfold hdnCallerPre
  repeat' first
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj

private theorem pcFree_hdnCallerPost (src dst cnt isl : Word)
    (srcBytes bufOrig : List (BitVec 8)) (oldCnt oldIsl : Word) :
    (hdnCallerPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl).pcFree := by
  unfold hdnCallerPost
  repeat' first
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj

/-- **The verified `hp_decode_nibbles` routine contract** (bead
    evm-asm-4ch8f.16.3): over the guest's own bytes (`hdnCr` at a symbolic
    base), from a standard C-ABI entry state, the routine returns to `ret`
    with `sp`/`ra`/all callee-saved registers restored, `a0` holding the
    parse status, the caller's nibble buffer holding the decoded hex-prefix
    path (`hdnBufFinal`), and the count / is-leaf cells written exactly per
    the guest-exact decode `hdnRes` — which agrees with the spec-side
    `EvmAsm.Evm64.hpDecode` on every well-formed encoding
    (`hdnRes_eq_hpDecode` / `hdnRes_hpEncode`). -/
theorem hp_decode_nibbles_spec (base sp0 ret : Word) (vals : Reg → Word)
    (src dst cnt isl : Word) (srcBytes bufOrig : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl : Word)
    (hret : vals .x1 = ret)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (hsalign : src.toNat % 8 = 0) (hsover : src.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ j, j < srcBytes.length →
      isValidByteAccess (src + BitVec.ofNat 64 j) = true)
    (hbuf : hdnC0 srcBytes + 2 * (srcBytes.length - 1) ≤ bufOrig.length)
    (hdalign : dst.toNat % 8 = 0) (hdover : dst.toNat + bufOrig.length < 2 ^ 64)
    (hdvalid : ∀ j, j < bufOrig.length →
      isValidByteAccess (dst + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (1 + hdnFrame.length + (30 + 11 * srcBytes.length)
        + hdnFrame.length + 1 + 1) base ret (hdnCr base)
      ((.x2 ↦ᵣ sp0) ** regsAt hdnFrame vals
        ** frameSlotsOwn hdnFrame (sp0 + signExtend12 (-48 : BitVec 12))
        ** hdnCallerPre src dst cnt isl srcBytes bufOrig
            v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl)
      ((.x2 ↦ᵣ sp0) ** regsAt hdnFrame vals
        ** frameSlotsSaved hdnFrame (sp0 + signExtend12 (-48 : BitVec 12)) vals
        ** hdnCallerPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl) := by
  exact abiFrame_spec base sp0 ret (-48 : BitVec 12) (48 : BitVec 12)
    hdnFrame (0 : BitVec 12)
    [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]
    vals (hdnVals' vals src (BitVec.ofNat 64 srcBytes.length) dst cnt isl)
    hdnBody (30 + 11 * srcBytes.length)
    (hdnCallerPre src dst cnt isl srcBytes bufOrig
      v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl)
    (hdnCallerPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl)
    (hdnCr base)
    rfl
    (by decide)
    (by decide)
    (by
      rw [show abiFrameProg (-48 : BitVec 12) (48 : BitVec 12) hdnFrame hdnBody
        = hpDecodeNibbles_prog from hdnProg_eq]
      decide)
    hret halignRet
    (by
      rw [show signExtend12 (-48 : BitVec 12) = (-48 : Word) from by decide,
        show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]
      bv_omega)
    (pcFree_hdnCallerPre src dst cnt isl srcBytes bufOrig
      v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl)
    (pcFree_hdnCallerPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl)
    (by
      intro a i h
      rw [show abiFrameProg (-48 : BitVec 12) (48 : BitVec 12) hdnFrame hdnBody
        = hpDecodeNibbles_prog from hdnProg_eq] at h
      exact h)
    (hdnBody_unified base (sp0 + signExtend12 (-48 : BitVec 12)) vals
      src dst cnt isl srcBytes bufOrig v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl
      hsalign hsover hsvalid hbuf hdalign hdover hdvalid)


end HpDecodeNibblesSAsm

end EvmAsm.Codegen
